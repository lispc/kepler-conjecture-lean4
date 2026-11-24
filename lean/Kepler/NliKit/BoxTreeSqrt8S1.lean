/-
Kepler.NliKit.BoxTreeSqrt8S1 — leaf witnesses, shard 1 of the
sqrt8 tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeS8Rows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree

theorem vD02_0 : ((rowsS8 (2 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem vF02_0 : ((rowsS8 (2 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6507999999994353856891393661499023437500 := by rw [vD02_0, vB40_2914585422908]; norm_num
theorem vD02_1 : ((rowsS8 (2 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 2949989697323, 2949989697323⟩ : DC) := by decide
theorem vF02_1 : ((rowsS8 (2 : Fin 30)).boxHi (0 : Fin 3)).value = 2.6829999999999927240423858165740966796875 := by rw [vD02_1, vB40_2949989697323]; norm_num
theorem vD02_2 : ((rowsS8 (2 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2230876107408, 2230876107408⟩ : DC) := by decide
theorem vF02_2 : ((rowsS8 (2 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0289699999993899837136268615722656250000 := by rw [vD02_2, vB40_2230876107408]; norm_num
theorem vD02_3 : ((rowsS8 (2 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF02_3 : ((rowsS8 (2 : Fin 30)).boxHi (1 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD02_3, vB40_2262728959265]; norm_num
theorem vD02_4 : ((rowsS8 (2 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF02_4 : ((rowsS8 (2 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD02_4, vB40_2199023255552]; norm_num
theorem vD02_5 : ((rowsS8 (2 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF02_5 : ((rowsS8 (2 : Fin 30)).boxHi (2 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD02_5, vB40_2262728959265]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp02a0h_1 : ((rowsS8 (2 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (2683/1000:ℝ) := by rw [vF02_1]; norm_num
theorem cmp02a2h_2 : ((rowsS8 (2 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF02_5]; norm_num
theorem cmp02a1h_3 : ((rowsS8 (2 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF02_3]; norm_num
theorem leaf_02_s8_cell02 : ∀ x ∈ rowBox (rowsS8 (2 : Fin 30)),
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
  by_cases n0 : x 1 ≤ (202897/100000:ℝ)
  ·
    by_cases n1 : x 2 ≤ (202897/100000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell00 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp02a0h_1]) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell01 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp02a0h_1]) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp02a2h_2]) (hd0 := hdlt)
  ·
    by_cases n1 : x 2 ≤ (202897/100000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell02 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp02a0h_1]) (hc5l := by linarith) (hc5h := by linarith [cmp02a1h_3]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell02 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp02a0h_1]) (hc5l := by linarith) (hc5h := by linarith [cmp02a1h_3]) (hc6l := by linarith) (hc6h := by linarith [cmp02a2h_2]) (hd0 := hdlt)

theorem vD03_0 : ((rowsS8 (3 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2949989697323, 2949989697323⟩ : DC) := by decide
theorem vF03_0 : ((rowsS8 (3 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6829999999999927240423858165740966796875 := by rw [vD03_0, vB40_2949989697323]; norm_num
theorem vD03_1 : ((rowsS8 (3 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF03_1 : ((rowsS8 (3 : Fin 30)).boxHi (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD03_1, vB40_2990671627550]; norm_num
theorem vD03_2 : ((rowsS8 (3 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF03_2 : ((rowsS8 (3 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD03_2, vB40_2199023255552]; norm_num
theorem vD03_3 : ((rowsS8 (3 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2230876107408, 2230876107408⟩ : DC) := by decide
theorem vF03_3 : ((rowsS8 (3 : Fin 30)).boxHi (1 : Fin 3)).value = 2.0289699999993899837136268615722656250000 := by rw [vD03_3, vB40_2230876107408]; norm_num
theorem vD03_4 : ((rowsS8 (3 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF03_4 : ((rowsS8 (3 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD03_4, vB40_2199023255552]; norm_num
theorem vD03_5 : ((rowsS8 (3 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF03_5 : ((rowsS8 (3 : Fin 30)).boxHi (2 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD03_5, vB40_2262728959265]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp03a0l_1 : (2:ℝ) ≤ ((rowsS8 (3 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF03_0]; norm_num
theorem cmp03a1h_2 : ((rowsS8 (3 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (202897/100000:ℝ) := by rw [vF03_3]; norm_num
theorem cmp03a2h_3 : ((rowsS8 (3 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF03_5]; norm_num
theorem cmp03a0h_4 : ((rowsS8 (3 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (68/25:ℝ) := by rw [vF03_1]; norm_num
theorem leaf_03_s8_cell03 : ∀ x ∈ rowBox (rowsS8 (3 : Fin 30)),
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
  by_cases n0 : x 0 ≤ (2683/1000:ℝ)
  ·
    by_cases n1 : x 2 ≤ (202897/100000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell00 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp03a1h_2]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell01 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp03a1h_2]) (hc6l := by linarith) (hc6h := by linarith [cmp03a2h_3]) (hd0 := hdlt)
  ·
    by_cases n1 : x 2 ≤ (202897/100000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell03 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith [cmp03a0h_4]) (hc5l := by linarith) (hc5h := by linarith [cmp03a1h_2]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell03 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith [cmp03a0h_4]) (hc5l := by linarith) (hc5h := by linarith [cmp03a1h_2]) (hc6l := by linarith) (hc6h := by linarith [cmp03a2h_3]) (hd0 := hdlt)

end Kepler.NliKit.BoxTreeSqrt8

