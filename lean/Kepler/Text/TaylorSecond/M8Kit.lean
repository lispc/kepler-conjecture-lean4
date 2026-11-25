/-
Kepler.Text.TaylorSecond.M8Kit — three box-independent kit pieces found by lane
`wt1-m8-preflight-w1` (2026-11-25) while generalising the M7 single-box template
to the D1 = 221 certificate boxes.

1. `delta_mono_y5_wide` / `delta_mono_y6_wide`: the `y5`/`y6` counterparts of
   `DltCornerWide.delta_mono_y4_wide`.  The landed `nb21_delta_mono_y5/y6` use
   `2*hminus ≤ y4` only to conclude `4 ≤ y4*y4` (via `2.4635 ≤ y4`); the same
   factorisations give both directions on the wider base `2.4618 ≤ y4`
   (`2.4618^2 = 6.06045924 ≥ 4`).  Needed because 45 of the 221 boxes start at
   the 18-digit lower bound `2.46350884418000923 < 2*hminus`.

2. `dMatanTightW` / `dMatanTightW_mem`: the landed `dMatanTight` picks
   `dMatanWp` from `dHiLt (dInv A) 4` alone, but `dMatanWp_mem` also needs
   `1/r > 1`.  On the D1 cover the `MgC` argument is frequently in `(1, 2.2)`,
   so the inner `1/r` is below `1` and the landed choice is out of domain
   (measured: 178 boxes hit the false gate).  The local version requires
   **both** provable tests (`1 < 1/r < 4`) and falls back to `dMatanU9`
   (sound for every positive argument).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.NliBanks21
import Kepler.Text.TaylorSecond.DCJet
import Kepler.Text.TaylorSecond.DCMatan
import Kepler.Text.TaylorSecond.DCSqrtLit
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Kepler.Text.TaylorSecond
namespace M8Kit

open Kepler.Text (deltaX)
open DCKit
open DCMatan
open DCJetKit

/-! ## 1. Wide-base monotonicity in `y5` / `y6` -/

/-- `Delta` is nonincreasing in `y5` on the wider base `y4 ≥ 2.4618`. -/
theorem delta_mono_y5_wide {y4 y5 y5' y6 : ℝ}
    (hy4 : 2.4618 ≤ y4) (hy5 : 2 ≤ y5) (hy5' : 2 ≤ y5') (hy5le : y5' ≤ y5)
    (hy6 : 2 ≤ y6) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤
      deltaX (y4 * y4) 2 (y5' * y5') 2 (y6 * y6) 2 := by
  have hx4 : (4 : ℝ) ≤ y4 * y4 := by nlinarith [hy4]
  have hx5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith [hy5]
  have hx5' : (4 : ℝ) ≤ y5' * y5' := by nlinarith [hy5']
  have hx6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  have hfac : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2
      - deltaX (y4 * y4) 2 (y5' * y5') 2 (y6 * y6) 2
      = ((y5 * y5) - (y5' * y5')) *
          (16 - ((y4 * y4) - 4) * ((y6 * y6) - 4)
            - 2 * ((y5 * y5) + (y5' * y5'))) := by
    rw [Kepler.NliBanks21.nb21_dlt_eq, Kepler.NliBanks21.nb21_dlt_eq]
    ring
  have hd : (0 : ℝ) ≤ (y5 * y5) - (y5' * y5') := by
    nlinarith [hy5le, hy5, hy5']
  have hs : 16 - ((y4 * y4) - 4) * ((y6 * y6) - 4)
      - 2 * ((y5 * y5) + (y5' * y5')) ≤ 0 := by
    have h1 : (0 : ℝ) ≤ ((y4 * y4) - 4) * ((y6 * y6) - 4) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith [hfac, hd, hs]

/-- `Delta` is nonincreasing in `y6` on the wider base `y4 ≥ 2.4618`. -/
theorem delta_mono_y6_wide {y4 y5 y6 y6' : ℝ}
    (hy4 : 2.4618 ≤ y4) (hy6 : 2 ≤ y6) (hy6' : 2 ≤ y6') (hy6le : y6' ≤ y6)
    (hy5 : 2 ≤ y5) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤
      deltaX (y4 * y4) 2 (y5 * y5) 2 (y6' * y6') 2 := by
  have hx4 : (4 : ℝ) ≤ y4 * y4 := by nlinarith [hy4]
  have hx5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith [hy5]
  have hx6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  have hx6' : (4 : ℝ) ≤ y6' * y6' := by nlinarith [hy6']
  have hfac : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2
      - deltaX (y4 * y4) 2 (y5 * y5) 2 (y6' * y6') 2
      = ((y6 * y6) - (y6' * y6')) *
          (16 - ((y4 * y4) - 4) * ((y5 * y5) - 4)
            - 2 * ((y6 * y6) + (y6' * y6'))) := by
    rw [Kepler.NliBanks21.nb21_dlt_eq, Kepler.NliBanks21.nb21_dlt_eq]
    ring
  have hd : (0 : ℝ) ≤ (y6 * y6) - (y6' * y6') := by
    nlinarith [hy6le, hy6, hy6']
  have hs : 16 - ((y4 * y4) - 4) * ((y5 * y5) - 4)
      - 2 * ((y6 * y6) + (y6' * y6')) ≤ 0 := by
    have h1 : (0 : ℝ) ≤ ((y4 * y4) - 4) * ((y5 * y5) - 4) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith [hfac, hd, hs]

/-! ## 2. The universal tight-mirror inner -/

/-- **Universal tight-mirror inner**: `dMatanWp` only when **both** `1 < 1/r < 4`
are provable, else `dMatanU9` (valid for every positive argument). -/
def dMatanTightW (A : DC) : DC :=
  if dLoGt (dInv A) ONE then
    (if dHiLt (dInv A) (dInt 4) then dMatanWp (dInv A) else dMatanU9 (dInv A))
  else dMatanU9 (dInv A)

theorem dMatanTightW_mem {A : DC} {r : ℝ} (hA : A.mem r) (hbig : dLoBig A = true)
    (hRden : dLoBig (dAdd (dSqrt (dInv A)) ONE) = true)
    (hRbig : dLoBig (dInv A) = true) :
    (dMatanTightW A).mem (matan (1 / r)) := by
  have hA0 : (0 : ℤ) < A.lo := by exact_mod_cast dLoBig_sound hbig
  have hR : (dInv A).mem (1 / r) := by
    have h := dInv_mem hA0 hA
    simpa [one_div] using h
  unfold dMatanTightW
  split
  · next h1 =>
      split
      · next h2 => exact dMatanWp_mem hR hRbig h1 hRden
      · next h2 => exact dMatanU9_mem hR hRbig
  · next h1 => exact dMatanU9_mem hR hRbig

#print axioms delta_mono_y5_wide
#print axioms delta_mono_y6_wide
#print axioms dMatanTightW
#print axioms dMatanTightW_mem

end M8Kit
end Kepler.Text.TaylorSecond
