/-
Kepler.NliKit.BoxTreeSqrt8S7 — leaf witnesses, shard 7 of the
sqrt8 tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeS8Rows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree

theorem vD14_0 : ((rowsS8 (14 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem vF14_0 : ((rowsS8 (14 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6507999999994353856891393661499023437500 := by rw [vD14_0, vB40_2914585422908]; norm_num
theorem vD14_1 : ((rowsS8 (14 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF14_1 : ((rowsS8 (14 : Fin 30)).boxHi (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD14_1, vB40_2990671627550]; norm_num
theorem vD14_2 : ((rowsS8 (14 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF14_2 : ((rowsS8 (14 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD14_2, vB40_2199023255552]; norm_num
theorem vD14_3 : ((rowsS8 (14 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF14_3 : ((rowsS8 (14 : Fin 30)).boxHi (1 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD14_3, vB40_2326434662978]; norm_num
theorem vD14_4 : ((rowsS8 (14 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF14_4 : ((rowsS8 (14 : Fin 30)).boxLo (2 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD14_4, vB40_2326434662978]; norm_num
theorem vD14_5 : ((rowsS8 (14 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2390140366692, 2390140366692⟩ : DC) := by decide
theorem vF14_5 : ((rowsS8 (14 : Fin 30)).boxHi (2 : Fin 3)).value = 2.1738199999999778810888528823852539062500 := by rw [vD14_5, vB40_2390140366692]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp14a0h_1 : ((rowsS8 (14 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (68/25:ℝ) := by rw [vF14_1]; norm_num
theorem cmp14a2l_2 : (102897/50000:ℝ) ≤ ((rowsS8 (14 : Fin 30)).boxLo (2 : Fin 3)).value := by rw [vF14_4]; norm_num
theorem cmp14a2h_3 : ((rowsS8 (14 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (108691/50000:ℝ) := by rw [vF14_5]; norm_num
theorem cmp14a1h_4 : ((rowsS8 (14 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (52897/25000:ℝ) := by rw [vF14_3]; norm_num
theorem leaf_14_s8_cell14 : ∀ x ∈ rowBox (rowsS8 (14 : Fin 30)),
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
  by_cases n0 : x 1 ≤ (102897/50000:ℝ)
  ·
    by_cases n1 : x 2 ≤ (52897/25000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell05 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp14a0h_1]) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith [cmp14a2l_2]) (hc6h := by linarith) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell14 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp14a0h_1]) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp14a2h_3]) (hd0 := hdlt)
  ·
    by_cases n1 : x 2 ≤ (52897/25000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell07 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp14a0h_1]) (hc5l := by linarith) (hc5h := by linarith [cmp14a1h_4]) (hc6l := by linarith [cmp14a2l_2]) (hc6h := by linarith) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell14 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp14a0h_1]) (hc5l := by linarith) (hc5h := by linarith [cmp14a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp14a2h_3]) (hd0 := hdlt)

theorem vD15_0 : ((rowsS8 (15 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem vF15_0 : ((rowsS8 (15 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6507999999994353856891393661499023437500 := by rw [vD15_0, vB40_2914585422908]; norm_num
theorem vD15_1 : ((rowsS8 (15 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF15_1 : ((rowsS8 (15 : Fin 30)).boxHi (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD15_1, vB40_2990671627550]; norm_num
theorem vD15_2 : ((rowsS8 (15 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF15_2 : ((rowsS8 (15 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD15_2, vB40_2199023255552]; norm_num
theorem vD15_3 : ((rowsS8 (15 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF15_3 : ((rowsS8 (15 : Fin 30)).boxHi (1 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD15_3, vB40_2326434662978]; norm_num
theorem vD15_4 : ((rowsS8 (15 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2390140366692, 2390140366692⟩ : DC) := by decide
theorem vF15_4 : ((rowsS8 (15 : Fin 30)).boxLo (2 : Fin 3)).value = 2.1738199999999778810888528823852539062500 := by rw [vD15_4, vB40_2390140366692]; norm_num
theorem vD15_5 : ((rowsS8 (15 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem vF15_5 : ((rowsS8 (15 : Fin 30)).boxHi (2 : Fin 3)).value = 2.2317599999996673432178795337677001953125 := by rw [vD15_5, vB40_2453846070405]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp15a0h_1 : ((rowsS8 (15 : Fin 30)).boxHi (0 : Fin 3)).value ≤ (68/25:ℝ) := by rw [vF15_1]; norm_num
theorem cmp15a1h_2 : ((rowsS8 (15 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (52897/25000:ℝ) := by rw [vF15_3]; norm_num
theorem cmp15a2l_3 : (52897/25000:ℝ) ≤ ((rowsS8 (15 : Fin 30)).boxLo (2 : Fin 3)).value := by rw [vF15_4]; norm_num
theorem cmp15a2h_4 : ((rowsS8 (15 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (27897/12500:ℝ) := by rw [vF15_5]; norm_num
theorem leaf_15_s8_cell15 : ∀ x ∈ rowBox (rowsS8 (15 : Fin 30)),
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
  by_cases n0 : x 2 ≤ (108691/50000:ℝ)
  ·
    exact Kepler.Text.NliSqrt8.s8_cell14 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp15a0h_1]) (hc5l := by linarith) (hc5h := by linarith [cmp15a1h_2]) (hc6l := by linarith [cmp15a2l_3]) (hc6h := by linarith) (hd0 := hdlt)
  ·
    exact Kepler.Text.NliSqrt8.s8_cell15 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith [cmp15a0h_1]) (hc5l := by linarith) (hc5h := by linarith [cmp15a1h_2]) (hc6l := by linarith) (hc6h := by linarith [cmp15a2h_4]) (hd0 := hdlt)

end Kepler.NliKit.BoxTreeSqrt8

