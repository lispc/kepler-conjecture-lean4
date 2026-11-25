/-
Kepler.Text.TaylorSecond.DltCornerWide — the wt1 `Dlt` corner rule at a
**wider `y4` base** than the landed `Kepler.NliBanks21.nb21_delta_mono_y4`.

Why this file exists (2026-11-25, lane `wt1-emission-pilot-w1` / round M8):

The 221 certificate boxes of the wt1 cover start at the *18-digit* lower
bound `2.46350884418000923` of `2 * hminus`, which is **below** the true
`2 * hminus = 2.46350884418060878...`.  The landed monotonicity lemma
`nb21_delta_mono_y4` requires `2 * hminus ≤ y4` at *both* endpoints, so the
corner-rule proof `fDlt x ≤ fDlt xlo` cannot be emitted on those 45 bottom
boxes (their `l4` is below `2 * hminus`).

The factorisation used by that lemma is

  `Delta(x4) - Delta(x4') = (x4 - x4') * (-2*(x4+x4') + 4*x5 + 4*x6 - x5*x6)`

and its second factor is `≤ 16 - 2*(6.06 + 6.06) < 0` as soon as
`x4, x4' ≥ 6.06` and `x5, x6 ≥ 4` — no `hminus` is needed.  Since
`2.4618^2 = 6.06045924 ≥ 6.06`, the lemma below only assumes
`2.4618 ≤ y4, y4'`, which holds with room to spare on every certificate box
(minimum `l4 = 2.46350884418000923`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.NliBanks21
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Kepler.Text.TaylorSecond
namespace DltCornerWide

open Kepler.Text (deltaX)

/-- **`Delta` is nonincreasing in `y4` on the wider base `y4 ≥ 2.4618`**
(`y4² ≥ 6.06045924 ≥ 6.06`), not only on `y4 ≥ 2 * hminus`. -/
theorem delta_mono_y4_wide {y4 y4' y5 y6 : ℝ}
    (hy4 : 2.4618 ≤ y4) (hy4' : 2.4618 ≤ y4') (hy4le : y4 ≤ y4')
    (hy5 : 2 ≤ y5) (hy6 : 2 ≤ y6) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≥
      deltaX (y4' * y4') 2 (y5 * y5) 2 (y6 * y6) 2 := by
  have hx5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith [hy5]
  have hx6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  have hfac : deltaX (y4' * y4') 2 (y5 * y5) 2 (y6 * y6) 2
      - deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2
      = ((y4' * y4') - (y4 * y4)) *
          (4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)
            - 2 * ((y4' * y4') + (y4 * y4))) := by
    rw [Kepler.NliBanks21.nb21_dlt_eq, Kepler.NliBanks21.nb21_dlt_eq]
    ring
  have hd : (0 : ℝ) ≤ (y4' * y4') - (y4 * y4) := by
    nlinarith [hy4le, hy4, hy4']
  have hs : 4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)
      - 2 * ((y4' * y4') + (y4 * y4)) ≤ 0 := by
    have h1 : (0 : ℝ) ≤ ((y5 * y5) - 4) * ((y6 * y6) - 4) :=
      mul_nonneg (by linarith) (by linarith)
    have hx4 : (6.06 : ℝ) ≤ y4 * y4 := by nlinarith [hy4]
    have hx4' : (6.06 : ℝ) ≤ y4' * y4' := by nlinarith [hy4']
    have hid : 4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)
        = 16 - ((y5 * y5) - 4) * ((y6 * y6) - 4) := by ring
    rw [hid]
    linarith [h1, hx4, hx4']
  nlinarith [hfac, hd, hs]

#print axioms delta_mono_y4_wide

end DltCornerWide
end Kepler.Text.TaylorSecond
