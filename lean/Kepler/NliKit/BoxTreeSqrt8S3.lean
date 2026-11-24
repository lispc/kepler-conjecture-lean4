/-
Kepler.NliKit.BoxTreeSqrt8S3 — leaf witnesses, shard 3 of the
sqrt8 tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeS8Rows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree

theorem vD06_0 : ((rowsS8 (6 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem vF06_0 : ((rowsS8 (6 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6507999999994353856891393661499023437500 := by rw [vD06_0, vB40_2914585422908]; norm_num
theorem vD06_1 : ((rowsS8 (6 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF06_1 : ((rowsS8 (6 : Fin 30)).boxHi (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD06_1, vB40_2990671627550]; norm_num
theorem vD06_2 : ((rowsS8 (6 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF06_2 : ((rowsS8 (6 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD06_2, vB40_2262728959265]; norm_num
theorem vD06_3 : ((rowsS8 (6 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF06_3 : ((rowsS8 (6 : Fin 30)).boxHi (1 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD06_3, vB40_2326434662978]; norm_num
theorem vD06_4 : ((rowsS8 (6 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF06_4 : ((rowsS8 (6 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD06_4, vB40_2199023255552]; norm_num
theorem vD06_5 : ((rowsS8 (6 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF06_5 : ((rowsS8 (6 : Fin 30)).boxHi (2 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD06_5, vB40_2262728959265]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp06a1l_1 : (202897/100000:ℝ) ≤ ((rowsS8 (6 : Fin 30)).boxLo (1 : Fin 3)).value := by rw [vF06_2]; norm_num
theorem cmp06a2h_2 : ((rowsS8 (6 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF06_5]; norm_num
theorem cmp06a1h_3 : ((rowsS8 (6 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (52897/25000:ℝ) := by rw [vF06_3]; norm_num
theorem cmp06a0h_4 : ((rowsS8 (6 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (68/25:ℝ) := by rw [vF06_1]; norm_num
theorem leaf_06_s8_cell06 : ∀ x ∈ rowBox (rowsS8 (6 : Fin 30)),
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
    by_cases n1 : x 1 ≤ (102897/50000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell02 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith [cmp06a1l_1]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp06a2h_2]) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell06 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp06a1h_3]) (hc6l := by linarith) (hc6h := by linarith [cmp06a2h_2]) (hd0 := hdlt)
  ·
    by_cases n1 : x 1 ≤ (102897/50000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell04 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith [cmp06a0h_4]) (hc5l := by linarith [cmp06a1l_1]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp06a2h_2]) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell06 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp06a0h_4]) (hc5l := by linarith) (hc5h := by linarith [cmp06a1h_3]) (hc6l := by linarith) (hc6h := by linarith [cmp06a2h_2]) (hd0 := hdlt)

theorem vD07_0 : ((rowsS8 (7 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem vF07_0 : ((rowsS8 (7 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6507999999994353856891393661499023437500 := by rw [vD07_0, vB40_2914585422908]; norm_num
theorem vD07_1 : ((rowsS8 (7 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF07_1 : ((rowsS8 (7 : Fin 30)).boxHi (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD07_1, vB40_2990671627550]; norm_num
theorem vD07_2 : ((rowsS8 (7 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF07_2 : ((rowsS8 (7 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD07_2, vB40_2262728959265]; norm_num
theorem vD07_3 : ((rowsS8 (7 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF07_3 : ((rowsS8 (7 : Fin 30)).boxHi (1 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD07_3, vB40_2326434662978]; norm_num
theorem vD07_4 : ((rowsS8 (7 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF07_4 : ((rowsS8 (7 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD07_4, vB40_2262728959265]; norm_num
theorem vD07_5 : ((rowsS8 (7 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF07_5 : ((rowsS8 (7 : Fin 30)).boxHi (2 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD07_5, vB40_2326434662978]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp07a1l_1 : (202897/100000:ℝ) ≤ ((rowsS8 (7 : Fin 30)).boxLo (1 : Fin 3)).value := by rw [vF07_2]; norm_num
theorem cmp07a2h_2 : ((rowsS8 (7 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (52897/25000:ℝ) := by rw [vF07_5]; norm_num
theorem cmp07a1h_3 : ((rowsS8 (7 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (52897/25000:ℝ) := by rw [vF07_3]; norm_num
theorem cmp07a0h_4 : ((rowsS8 (7 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (68/25:ℝ) := by rw [vF07_1]; norm_num
theorem leaf_07_s8_cell07 : ∀ x ∈ rowBox (rowsS8 (7 : Fin 30)),
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
    by_cases n1 : x 1 ≤ (102897/50000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (102897/50000:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell02 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith [cmp07a1l_1]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell05 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp07a2h_2]) (hd0 := hdlt)
    ·
      by_cases n2 : x 2 ≤ (102897/50000:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell06 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp07a1h_3]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell07 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp07a1h_3]) (hc6l := by linarith) (hc6h := by linarith [cmp07a2h_2]) (hd0 := hdlt)
  ·
    by_cases n1 : x 1 ≤ (102897/50000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (102897/50000:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell04 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith [cmp07a0h_4]) (hc5l := by linarith [cmp07a1l_1]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell05 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp07a0h_4]) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp07a2h_2]) (hd0 := hdlt)
    ·
      by_cases n2 : x 2 ≤ (102897/50000:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell06 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp07a0h_4]) (hc5l := by linarith) (hc5h := by linarith [cmp07a1h_3]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell07 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp07a0h_4]) (hc5l := by linarith) (hc5h := by linarith [cmp07a1h_3]) (hc6l := by linarith) (hc6h := by linarith [cmp07a2h_2]) (hd0 := hdlt)

end Kepler.NliKit.BoxTreeSqrt8

