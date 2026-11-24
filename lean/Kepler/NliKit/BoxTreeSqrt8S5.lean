/-
Kepler.NliKit.BoxTreeSqrt8S5 — leaf witnesses, shard 5 of the
sqrt8 tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeS8Rows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree

theorem vD10_0 : ((rowsS8 (10 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 3056642325217, 3056642325217⟩ : DC) := by decide
theorem vF10_0 : ((rowsS8 (10 : Fin 30)).boxLo (0 : Fin 3)).value = 2.7799999999997453414835035800933837890625 := by rw [vD10_0, vB40_3056642325217]; norm_num
theorem vD10_1 : ((rowsS8 (10 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF10_1 : ((rowsS8 (10 : Fin 30)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD10_1, vB40_3109888511976]; norm_num
theorem vD10_2 : ((rowsS8 (10 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF10_2 : ((rowsS8 (10 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD10_2, vB40_2199023255552]; norm_num
theorem vD10_3 : ((rowsS8 (10 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF10_3 : ((rowsS8 (10 : Fin 30)).boxHi (1 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD10_3, vB40_2262728959265]; norm_num
theorem vD10_4 : ((rowsS8 (10 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF10_4 : ((rowsS8 (10 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD10_4, vB40_2199023255552]; norm_num
theorem vD10_5 : ((rowsS8 (10 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF10_5 : ((rowsS8 (10 : Fin 30)).boxHi (2 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD10_5, vB40_2262728959265]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp10a0l_1 : (2:ℝ) ≤ ((rowsS8 (10 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF10_0]; norm_num
theorem cmp10a0l_2 : (68/25:ℝ) ≤ ((rowsS8 (10 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF10_0]; norm_num
theorem cmp10a2h_3 : ((rowsS8 (10 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF10_5]; norm_num
theorem cmp10a1h_4 : ((rowsS8 (10 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF10_3]; norm_num
theorem leaf_10_s8_cell10 : ∀ x ∈ rowBox (rowsS8 (10 : Fin 30)),
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
  by_cases n0 : x 0 ≤ (139/50:ℝ)
  ·
    by_cases n1 : x 1 ≤ (202897/100000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell08 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [cmp10a0l_2]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp10a2h_3]) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell09 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [cmp10a0l_2]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp10a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp10a2h_3]) (hd0 := hdlt)
  ·
    by_cases n1 : x 1 ≤ (202897/100000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell10 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp10a2h_3]) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell10 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp10a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp10a2h_3]) (hd0 := hdlt)

theorem vD11_0 : ((rowsS8 (11 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF11_0 : ((rowsS8 (11 : Fin 30)).boxLo (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD11_0, vB40_2990671627550]; norm_num
theorem vD11_1 : ((rowsS8 (11 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF11_1 : ((rowsS8 (11 : Fin 30)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD11_1, vB40_3109888511976]; norm_num
theorem vD11_2 : ((rowsS8 (11 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF11_2 : ((rowsS8 (11 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD11_2, vB40_2199023255552]; norm_num
theorem vD11_3 : ((rowsS8 (11 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF11_3 : ((rowsS8 (11 : Fin 30)).boxHi (1 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD11_3, vB40_2262728959265]; norm_num
theorem vD11_4 : ((rowsS8 (11 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2262728959265, 2262728959265⟩ : DC) := by decide
theorem vF11_4 : ((rowsS8 (11 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0579399999996894621290266513824462890625 := by rw [vD11_4, vB40_2262728959265]; norm_num
theorem vD11_5 : ((rowsS8 (11 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF11_5 : ((rowsS8 (11 : Fin 30)).boxHi (2 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD11_5, vB40_2326434662978]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp11a0l_1 : (2:ℝ) ≤ ((rowsS8 (11 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF11_0]; norm_num
theorem cmp11a0l_2 : (2683/1000:ℝ) ≤ ((rowsS8 (11 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF11_0]; norm_num
theorem cmp11a2h_3 : ((rowsS8 (11 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (52897/25000:ℝ) := by rw [vF11_5]; norm_num
theorem cmp11a1h_4 : ((rowsS8 (11 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (102897/50000:ℝ) := by rw [vF11_3]; norm_num
theorem leaf_11_s8_cell11 : ∀ x ∈ rowBox (rowsS8 (11 : Fin 30)),
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
    by_cases n1 : x 0 ≤ (139/50:ℝ)
    ·
      by_cases n2 : x 1 ≤ (202897/100000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (102897/50000:ℝ)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell03 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [cmp11a0l_2]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell05 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp11a2h_3]) (hd0 := hdlt)
      ·
        by_cases n3 : x 2 ≤ (102897/50000:ℝ)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell04 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [cmp11a0l_2]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp11a1h_4]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell05 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp11a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp11a2h_3]) (hd0 := hdlt)
    ·
      by_cases n2 : x 1 ≤ (202897/100000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (102897/50000:ℝ)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell03 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell05 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp11a2h_3]) (hd0 := hdlt)
      ·
        by_cases n3 : x 2 ≤ (102897/50000:ℝ)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell04 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp11a1h_4]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell05 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp11a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp11a2h_3]) (hd0 := hdlt)
  ·
    by_cases n1 : x 0 ≤ (139/50:ℝ)
    ·
      by_cases n2 : x 1 ≤ (202897/100000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (102897/50000:ℝ)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell08 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell11 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp11a2h_3]) (hd0 := hdlt)
      ·
        by_cases n3 : x 2 ≤ (102897/50000:ℝ)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell09 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp11a1h_4]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell11 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp11a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp11a2h_3]) (hd0 := hdlt)
    ·
      by_cases n2 : x 1 ≤ (202897/100000:ℝ)
      ·
        by_cases n3 : x 2 ≤ (102897/50000:ℝ)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell10 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell11 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp11a2h_3]) (hd0 := hdlt)
      ·
        by_cases n3 : x 2 ≤ (102897/50000:ℝ)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell10 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp11a1h_4]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
        ·
          exact Kepler.Text.NliSqrt8.s8_cell11 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp11a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp11a2h_3]) (hd0 := hdlt)

end Kepler.NliKit.BoxTreeSqrt8

