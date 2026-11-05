/-
Kepler.Text.Gamma4Deriv8 — lane `gamma4-w3`, part 5: the `gamma4fgcy`
y-partials.

`gamma4fgcy y f = volY y − vol4f y f`, so the slot partial is
`∂volY/∂yᵢ − ∂vol4f/∂yᵢ`, both supplied by the previous files.  This is the
explicit derivative expression of the bank monotonicity slots; the sign
analysis on the two sharp boxes is a separate (numeric) question, see
`DELIVERY.md`.
-/
import Kepler.Text.Gamma4Deriv7

set_option maxHeartbeats 4000000

open Filter
open scoped Topology

namespace Kepler.Text

/-! ## The six `volY` derivative values

`∂volY/∂yᵢ = yᵢ·Δᵢ / (12·√Δ)` (definitionally the values of
`volY_hasDerivAt_y1..y6`). -/


noncomputable def g4dDVolY1 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  y1 * g4dDX1 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
    / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))

noncomputable def g4dDVolY2 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  y2 * g4dDX2 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
    / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))

noncomputable def g4dDVolY3 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  y3 * g4dDX3 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
    / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))

noncomputable def g4dDVolY4 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  y4 * deltaX4 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
    / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))

noncomputable def g4dDVolY5 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  y5 * deltaX5 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
    / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))

noncomputable def g4dDVolY6 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  y6 * g4dDX6 (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)
    / (12 * Real.sqrt (deltaY y1 y2 y3 y4 y5 y6))

/-! ## The six `gamma4fgcy` y-partials -/

theorem gamma4fgcy_hasDerivAt_y1 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y1 / 2)) :
    HasDerivAt (fun t => gamma4fgcy t y2 y3 y4 y5 y6 lmfun)
      (g4dDVolY1 y1 y2 y3 y4 y5 y6 - g4dDVol4f1 y1 y2 y3 y4 y5 y6 L) y1 := by
  have hv := volY_hasDerivAt_y1 y1 y2 y3 y4 y5 y6 hd
  have hw := vol4f_hasDerivAt_y1 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have h := hv.sub hw
  convert h using 1 <;> rfl

theorem gamma4fgcy_hasDerivAt_y2 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y2 / 2)) :
    HasDerivAt (fun t => gamma4fgcy y1 t y3 y4 y5 y6 lmfun)
      (g4dDVolY2 y1 y2 y3 y4 y5 y6 - g4dDVol4f2 y1 y2 y3 y4 y5 y6 L) y2 := by
  have hv := volY_hasDerivAt_y2 y1 y2 y3 y4 y5 y6 hd
  have hw := vol4f_hasDerivAt_y2 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have h := hv.sub hw
  convert h using 1 <;> rfl

theorem gamma4fgcy_hasDerivAt_y3 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y3 / 2)) :
    HasDerivAt (fun t => gamma4fgcy y1 y2 t y4 y5 y6 lmfun)
      (g4dDVolY3 y1 y2 y3 y4 y5 y6 - g4dDVol4f3 y1 y2 y3 y4 y5 y6 L) y3 := by
  have hv := volY_hasDerivAt_y3 y1 y2 y3 y4 y5 y6 hd
  have hw := vol4f_hasDerivAt_y3 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have h := hv.sub hw
  convert h using 1 <;> rfl

theorem gamma4fgcy_hasDerivAt_y4 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y4 / 2)) :
    HasDerivAt (fun t => gamma4fgcy y1 y2 y3 t y5 y6 lmfun)
      (g4dDVolY4 y1 y2 y3 y4 y5 y6 - g4dDVol4f4 y1 y2 y3 y4 y5 y6 L) y4 := by
  have hv := volY_hasDerivAt_y4 y1 y2 y3 y4 y5 y6 hd
  have hw := vol4f_hasDerivAt_y4 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have h := hv.sub hw
  convert h using 1 <;> rfl

theorem gamma4fgcy_hasDerivAt_y5 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y5 / 2)) :
    HasDerivAt (fun t => gamma4fgcy y1 y2 y3 y4 t y6 lmfun)
      (g4dDVolY5 y1 y2 y3 y4 y5 y6 - g4dDVol4f5 y1 y2 y3 y4 y5 y6 L) y5 := by
  have hv := volY_hasDerivAt_y5 y1 y2 y3 y4 y5 y6 hd
  have hw := vol4f_hasDerivAt_y5 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have h := hv.sub hw
  convert h using 1 <;> rfl

theorem gamma4fgcy_hasDerivAt_y6 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y6 / 2)) :
    HasDerivAt (fun t => gamma4fgcy y1 y2 y3 y4 y5 t lmfun)
      (g4dDVolY6 y1 y2 y3 y4 y5 y6 - g4dDVol4f6 y1 y2 y3 y4 y5 y6 L) y6 := by
  have hv := volY_hasDerivAt_y6 y1 y2 y3 y4 y5 y6 hd
  have hw := vol4f_hasDerivAt_y6 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf
  have h := hv.sub hw
  convert h using 1 <;> rfl

/-! ## Axiom audit -/

#print axioms gamma4fgcy_hasDerivAt_y1
#print axioms gamma4fgcy_hasDerivAt_y2
#print axioms gamma4fgcy_hasDerivAt_y3
#print axioms gamma4fgcy_hasDerivAt_y4
#print axioms gamma4fgcy_hasDerivAt_y5
#print axioms gamma4fgcy_hasDerivAt_y6

end Kepler.Text
