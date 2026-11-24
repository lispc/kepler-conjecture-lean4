/-
Kepler.NliKit.BoxTreeSqrt8S12 — leaf witnesses, shard 12 of the
sqrt8 tree replay (lane nlikit-boxtree-impl-w1;
machine-generated, PYTHONHASHSEED=0).  Each leaf proof cascades
by_cases over EVERY decimal plane crossing its tile and routes
each branch to the ORIGINAL cell witness.  Zero new axioms.
-/
import Kepler.NliKit.BoxTreeS8Rows

set_option maxHeartbeats 400000000

namespace Kepler.NliKit.BoxTreeSqrt8

open Kepler.NliKit.BoxTree

theorem vD24_0 : ((rowsS8 (24 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem vF24_0 : ((rowsS8 (24 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6507999999994353856891393661499023437500 := by rw [vD24_0, vB40_2914585422908]; norm_num
theorem vD24_1 : ((rowsS8 (24 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF24_1 : ((rowsS8 (24 : Fin 30)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD24_1, vB40_3109888511976]; norm_num
theorem vD24_2 : ((rowsS8 (24 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2326434662978, 2326434662978⟩ : DC) := by decide
theorem vF24_2 : ((rowsS8 (24 : Fin 30)).boxLo (1 : Fin 3)).value = 2.1158799999993789242580533027648925781250 := by rw [vD24_2, vB40_2326434662978]; norm_num
theorem vD24_3 : ((rowsS8 (24 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem vF24_3 : ((rowsS8 (24 : Fin 30)).boxHi (1 : Fin 3)).value = 2.2317599999996673432178795337677001953125 := by rw [vD24_3, vB40_2453846070405]; norm_num
theorem vD24_4 : ((rowsS8 (24 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem vF24_4 : ((rowsS8 (24 : Fin 30)).boxLo (2 : Fin 3)).value = 2.2317599999996673432178795337677001953125 := by rw [vD24_4, vB40_2453846070405]; norm_num
theorem vD24_5 : ((rowsS8 (24 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2581257477832, 2581257477832⟩ : DC) := by decide
theorem vF24_5 : ((rowsS8 (24 : Fin 30)).boxHi (2 : Fin 3)).value = 2.3476399999999557621777057647705078125000 := by rw [vD24_5, vB40_2581257477832]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp24a2l_1 : (108691/50000:ℝ) ≤ ((rowsS8 (24 : Fin 30)).boxLo (2 : Fin 3)).value := by rw [vF24_4]; norm_num
theorem cmp24a2h_2 : ((rowsS8 (24 : Fin 30)).boxHi (2 : Fin 3)).value ≤ (58691/25000:ℝ) := by rw [vF24_5]; norm_num
theorem cmp24a1h_3 : ((rowsS8 (24 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (27897/12500:ℝ) := by rw [vF24_3]; norm_num
theorem cmp24a2l_4 : (52897/25000:ℝ) ≤ ((rowsS8 (24 : Fin 30)).boxLo (2 : Fin 3)).value := by rw [vF24_4]; norm_num
theorem leaf_24_s8_cell24 : ∀ x ∈ rowBox (rowsS8 (24 : Fin 30)),
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
      by_cases n2 : x 2 ≤ (27897/12500:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell15 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith [cmp24a2l_1]) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell23 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp24a2h_2]) (hd0 := hdlt)
    ·
      by_cases n2 : x 2 ≤ (27897/12500:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell22 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp24a1h_3]) (hc6l := by linarith [cmp24a2l_4]) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell24 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp24a1h_3]) (hc6l := by linarith) (hc6h := by linarith [cmp24a2h_2]) (hd0 := hdlt)
  ·
    by_cases n1 : x 1 ≤ (52897/25000:ℝ)
    ·
      by_cases n2 : x 2 ≤ (27897/12500:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell17 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith [cmp24a2l_1]) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell23 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [cmp24a2h_2]) (hd0 := hdlt)
    ·
      by_cases n2 : x 2 ≤ (27897/12500:ℝ)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell22 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp24a1h_3]) (hc6l := by linarith [cmp24a2l_4]) (hc6h := by linarith) (hd0 := hdlt)
      ·
        exact Kepler.Text.NliSqrt8.s8_cell24 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp24a1h_3]) (hc6l := by linarith) (hc6h := by linarith [cmp24a2h_2]) (hd0 := hdlt)

theorem vD25_0 : ((rowsS8 (25 : Fin 30)).boxLo (0 : Fin 3)) = (⟨40, 2914585422908, 2914585422908⟩ : DC) := by decide
theorem vF25_0 : ((rowsS8 (25 : Fin 30)).boxLo (0 : Fin 3)).value = 2.6507999999994353856891393661499023437500 := by rw [vD25_0, vB40_2914585422908]; norm_num
theorem vD25_1 : ((rowsS8 (25 : Fin 30)).boxHi (0 : Fin 3)) = (⟨40, 3109888511976, 3109888511976⟩ : DC) := by decide
theorem vF25_1 : ((rowsS8 (25 : Fin 30)).boxHi (0 : Fin 3)).value = 2.8284271247466676868498325347900390625000 := by rw [vD25_1, vB40_3109888511976]; norm_num
theorem vD25_2 : ((rowsS8 (25 : Fin 30)).boxLo (1 : Fin 3)) = (⟨40, 2199023255552, 2199023255552⟩ : DC) := by decide
theorem vF25_2 : ((rowsS8 (25 : Fin 30)).boxLo (1 : Fin 3)).value = 2.0000000000000000000000000000000000000000 := by rw [vD25_2, vB40_2199023255552]; norm_num
theorem vD25_3 : ((rowsS8 (25 : Fin 30)).boxHi (1 : Fin 3)) = (⟨40, 2453846070405, 2453846070405⟩ : DC) := by decide
theorem vF25_3 : ((rowsS8 (25 : Fin 30)).boxHi (1 : Fin 3)).value = 2.2317599999996673432178795337677001953125 := by rw [vD25_3, vB40_2453846070405]; norm_num
theorem vD25_4 : ((rowsS8 (25 : Fin 30)).boxLo (2 : Fin 3)) = (⟨40, 2581257477832, 2581257477832⟩ : DC) := by decide
theorem vF25_4 : ((rowsS8 (25 : Fin 30)).boxLo (2 : Fin 3)).value = 2.3476399999999557621777057647705078125000 := by rw [vD25_4, vB40_2581257477832]; norm_num
theorem vD25_5 : ((rowsS8 (25 : Fin 30)).boxHi (2 : Fin 3)) = (⟨40, 2708668885259, 2708668885259⟩ : DC) := by decide
theorem vF25_5 : ((rowsS8 (25 : Fin 30)).boxHi (2 : Fin 3)).value = 2.4635200000002441811375319957733154296875 := by rw [vD25_5, vB40_2708668885259]; norm_num
/-- tile-vs-plane/shell comparison facts (rw [vF]; norm_num). -/
theorem cmp25a2l_1 : (27897/12500:ℝ) ≤ ((rowsS8 (25 : Fin 30)).boxLo (2 : Fin 3)).value := by rw [vF25_4]; norm_num
theorem cmp25a1h_2 : ((rowsS8 (25 : Fin 30)).boxHi (1 : Fin 3)).value ≤ (27897/12500:ℝ) := by rw [vF25_3]; norm_num
theorem leaf_25_s8_cell25 : ∀ x ∈ rowBox (rowsS8 (25 : Fin 30)),
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
  by_cases n0 : x 1 ≤ (52897/25000:ℝ)
  ·
    by_cases n1 : x 2 ≤ (58691/25000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell23 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith [cmp25a2l_1]) (hc6h := by linarith) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell25 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith) (hc6l := by linarith) (hc6h := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hd0 := hdlt)
  ·
    by_cases n1 : x 2 ≤ (58691/25000:ℝ)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell24 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp25a1h_2]) (hc6l := by linarith [cmp25a2l_1]) (hc6h := by linarith) (hd0 := hdlt)
    ·
      exact Kepler.Text.NliSqrt8.s8_cell25 (hy4 := by linarith [s8hp]) (hy4' := by linarith) (hy5 := by linarith) (hy5' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hy6 := by linarith) (hy6' := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hc4l := by linarith [s8hp]) (hc4h := by linarith) (hc5l := by linarith) (hc5h := by linarith [cmp25a1h_2]) (hc6l := by linarith) (hc6h := by linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.2]) (hd0 := hdlt)

end Kepler.NliKit.BoxTreeSqrt8

