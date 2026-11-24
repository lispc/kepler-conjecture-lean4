/-
Kepler.NliKit.BoxTreeSqrt8S10 — leaf witnesses, shard 10 of the
sqrt8 tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeS8Rows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree

theorem vD20_0 : ((rowsS8 (20 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF20_0 : ((rowsS8 (20 : Fin 30)).boxLo (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD20_0, vB40_2990671627550]; norm_num
theorem vD20_1 : ((rowsS8 (20 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF20_1 : ((rowsS8 (20 : Fin 30)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD20_1, vB40_3109888511976]; norm_num
theorem vD20_2 : ((rowsS8 (20 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF20_2 : ((rowsS8 (20 : Fin 30)).boxLo (1 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD20_2, vB40_2326434662978]; norm_num
theorem vD20_3 : ((rowsS8 (20 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2390140366692, 2390140366692⟩ : DC) := by decide
theorem vF20_3 : ((rowsS8 (20 : Fin 30)).boxHi (1 : Fin 3)).value = 2.1738199999999778810888528823852539062500 := by rw [vD20_3, vB40_2390140366692]; norm_num
theorem vD20_4 : ((rowsS8 (20 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF20_4 : ((rowsS8 (20 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD20_4, vB40_2199023255552]; norm_num
theorem vD20_5 : ((rowsS8 (20 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF20_5 : ((rowsS8 (20 : Fin 30)).boxHi (2 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD20_5, vB40_2326434662978]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp20a0l_1 : (2:ℝ) ≤ ((rowsS8 (20 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF20_0]; norm_num
theorem cmp20a1l_2 : (102897/50000:ℝ) ≤ ((rowsS8 (20 : Fin 30)).boxLo (1 : Fin 3)).value := by rw [vF20_2]; norm_num
theorem cmp20a2h_3 : ((rowsS8 (20 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (52897/25000:ℝ) := by rw [vF20_5]; norm_num
theorem cmp20a1h_4 : ((rowsS8 (20 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (108691/50000:ℝ) := by rw [vF20_3]; norm_num
theorem leaf_20_s8_cell20 : ∀ x ∈ rowBox (rowsS8 (20 : Fin 30)),
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
    by_cases n1 : x 1 ≤ (52897/25000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (102897/50000:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell06 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith [cmp20a1l_2]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell07 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith [cmp20a1l_2]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp20a2h_3]) (hd0 := hdlt)
    ·
      by_cases n2 : x 2 ≤ (102897/50000:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell18 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp20a1h_4]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell18 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp20a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp20a2h_3]) (hd0 := hdlt)
  ·
    by_cases n1 : x 1 ≤ (52897/25000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (102897/50000:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell12 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith [cmp20a1l_2]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell13 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith [cmp20a1l_2]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp20a2h_3]) (hd0 := hdlt)
    ·
      by_cases n2 : x 2 ≤ (102897/50000:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell20 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp20a1h_4]) (hc6l := by linarith) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell20 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp20a1h_4]) (hc6l := by linarith) (hc6h := by linarith [cmp20a2h_3]) (hd0 := hdlt)

theorem vD21_0 : ((rowsS8 (21 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2990671627550, 2990671627550⟩ : DC) := by decide
theorem vF21_0 : ((rowsS8 (21 : Fin 30)).boxLo (0 : Fin 3)).value = 2.7199999999993451638147234916687011718750 := by rw [vD21_0, vB40_2990671627550]; norm_num
theorem vD21_1 : ((rowsS8 (21 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF21_1 : ((rowsS8 (21 : Fin 30)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD21_1, vB40_3109888511976]; norm_num
theorem vD21_2 : ((rowsS8 (21 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2390140366692, 2390140366692⟩ : DC) := by decide
theorem vF21_2 : ((rowsS8 (21 : Fin 30)).boxLo (1 : Fin 3)).value = 2.1738199999999778810888528823852539062500 := by rw [vD21_2, vB40_2390140366692]; norm_num
theorem vD21_3 : ((rowsS8 (21 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem vF21_3 : ((rowsS8 (21 : Fin 30)).boxHi (1 : Fin 3)).value = 2.2317599999996673432178795337677001953125 := by rw [vD21_3, vB40_2453846070405]; norm_num
theorem vD21_4 : ((rowsS8 (21 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF21_4 : ((rowsS8 (21 : Fin 30)).boxLo (2 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD21_4, vB40_2199023255552]; norm_num
theorem vD21_5 : ((rowsS8 (21 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF21_5 : ((rowsS8 (21 : Fin 30)).boxHi (2 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD21_5, vB40_2326434662978]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp21a0l_1 : (2:ℝ) ≤ ((rowsS8 (21 : Fin 30)).boxLo (0 : Fin 3)).value := by rw [vF21_0]; norm_num
theorem cmp21a1l_2 : (52897/25000:ℝ) ≤ ((rowsS8 (21 : Fin 30)).boxLo (1 : Fin 3)).value := by rw [vF21_2]; norm_num
theorem cmp21a2h_3 : ((rowsS8 (21 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (52897/25000:ℝ) := by rw [vF21_5]; norm_num
theorem leaf_21_absurd : ∀ x ∈ rowBox (rowsS8 (21 : Fin 30)),
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
    by_cases n1 : x 1 ≤ (108691/50000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell18 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith [cmp21a1l_2]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp21a2h_3]) (hd0 := hdlt)
    ·
      exact absurd (le_trans (by linarith : (2.17382:ℝ) ≤ x 1) (le_trans hy56 (by linarith [f2.2, vF21_5] : x 2 ≤ (2.11588:ℝ)))) (by norm_num : ¬ (2.17382:ℝ) ≤ (2.11588:ℝ))
  ·
    by_cases n1 : x 1 ≤ (108691/50000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell20 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith [cmp21a1l_2]) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp21a2h_3]) (hd0 := hdlt)
    ·
      exact absurd (le_trans (by linarith : (2.17382:ℝ) ≤ x 1) (le_trans hy56 (by linarith [f2.2, vF21_5] : x 2 ≤ (2.11588:ℝ)))) (by norm_num : ¬ (2.17382:ℝ) ≤ (2.11588:ℝ))

end Kepler.NliKit.BoxTreeSqrt8

