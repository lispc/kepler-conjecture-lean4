/-
Kepler.NliKit.BoxTreeSqrt8S0 — leaf witnesses, shard 0 of the
sqrt8 tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeS8Rows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree

theorem vD00_0 : ((rowsS8 (0 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem vF00_0 : ((rowsS8 (0 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6507999999994353856891393661499023437500 := by rw [vD00_0, vB40_2914585422908]; norm_num
theorem vD00_1 : ((rowsS8 (0 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 2949989697323, 2949989697323⟩ : DC) := by decide
theorem vF00_1 : ((rowsS8 (0 : Fin 30)).boxHi (0 : Fin 3)).value = 2.6829999999999927240423858165740966796875 := by rw [vD00_1, vB40_2949989697323]; norm_num
theorem vD00_2 : ((rowsS8 (0 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF00_2 : ((rowsS8 (0 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD00_2, vB40_2199023255552]; norm_num
theorem vD00_3 : ((rowsS8 (0 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2230876107408, 2230876107408⟩ : DC) := by decide
theorem vF00_3 : ((rowsS8 (0 : Fin 30)).boxHi (1 : Fin 3)).value = 2.0289699999993899837136268615722656250000 := by rw [vD00_3, vB40_2230876107408]; norm_num
theorem vD00_4 : ((rowsS8 (0 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF00_4 : ((rowsS8 (0 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD00_4, vB40_2199023255552]; norm_num
theorem vD00_5 : ((rowsS8 (0 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2230876107408, 2230876107408⟩ : DC) := by decide
theorem vF00_5 : ((rowsS8 (0 : Fin 30)).boxHi (2 : Fin 3)).value = 2.0289699999993899837136268615722656250000 := by rw [vD00_5, vB40_2230876107408]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp00a0h_1 : ((rowsS8 (0 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (2683/1000:ℝ) := by rw [vF00_1]; norm_num
theorem cmp00a1h_2 : ((rowsS8 (0 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (202897/100000:ℝ) := by rw [vF00_3]; norm_num
theorem cmp00a2h_3 : ((rowsS8 (0 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (202897/100000:ℝ) := by rw [vF00_5]; norm_num
theorem leaf_00_s8_cell00 : ∀ x ∈ rowBox (rowsS8 (0 : Fin 30)),
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
  exact Kepler.Text.NliSqrt8.s8_cell00 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp00a0h_1]) (hc5l := by linarith) (hc5h := by linarith [cmp00a1h_2]) (hc6l := by linarith) (hc6h := by linarith [cmp00a2h_3]) (hd0 := hdlt)

theorem vD01_0 : ((rowsS8 (1 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem vF01_0 : ((rowsS8 (1 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6507999999994353856891393661499023437500 := by rw [vD01_0, vB40_2914585422908]; norm_num
theorem vD01_1 : ((rowsS8 (1 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 2949989697323, 2949989697323⟩ : DC) := by decide
theorem vF01_1 : ((rowsS8 (1 : Fin 30)).boxHi (0 : Fin 3)).value = 2.6829999999999927240423858165740966796875 := by rw [vD01_1, vB40_2949989697323]; norm_num
theorem vD01_2 : ((rowsS8 (1 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF01_2 : ((rowsS8 (1 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD01_2, vB40_2199023255552]; norm_num
theorem vD01_3 : ((rowsS8 (1 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2230876107408, 2230876107408⟩ : DC) := by decide
theorem vF01_3 : ((rowsS8 (1 : Fin 30)).boxHi (1 : Fin 3)).value = 2.0289699999993899837136268615722656250000 := by rw [vD01_3, vB40_2230876107408]; norm_num
theorem vD01_4 : ((rowsS8 (1 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2230876107408, 2230876107408⟩ : DC) := by decide
theorem vF01_4 : ((rowsS8 (1 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0289699999993899837136268615722656250000 := by rw [vD01_4, vB40_2230876107408]; norm_num
theorem vD01_5 : ((rowsS8 (1 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF01_5 : ((rowsS8 (1 : Fin 30)).boxHi (2 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD01_5, vB40_2262728959265]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp01a0h_1 : ((rowsS8 (1 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (2683/1000:ℝ) := by rw [vF01_1]; norm_num
theorem cmp01a1h_2 : ((rowsS8 (1 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (202897/100000:ℝ) := by rw [vF01_3]; norm_num
theorem cmp01a2h_3 : ((rowsS8 (1 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF01_5]; norm_num
theorem leaf_01_s8_cell01 : ∀ x ∈ rowBox (rowsS8 (1 : Fin 30)),
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
  by_cases n0 : x 2 ≤ (202897/100000:ℝ)
  ·
    exact Kepler.Text.NliSqrt8.s8_cell00 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp01a0h_1]) (hc5l := by linarith) (hc5h := by linarith [cmp01a1h_2]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
  ·
    exact Kepler.Text.NliSqrt8.s8_cell01 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp01a0h_1]) (hc5l := by linarith) (hc5h := by linarith [cmp01a1h_2]) (hc6l := by linarith) (hc6h := by linarith [cmp01a2h_3]) (hd0 := hdlt)

end Kepler.NliKit.BoxTreeSqrt8

