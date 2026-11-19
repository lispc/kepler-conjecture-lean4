/-
Kepler.Text.FhbG3posCurve — lane `fhb-g3pos-w1`, 2026-11-18.

FHBa 3-D guard positivity `g3pos`: binding 1-D seam-curve certificate kit.

The seam lane (`fhb-seam-curve-w1`) reduced `bank_FHBVYXZa` to the
`g3pos` obligation and identified its binding leaf: the 1-D curve
certificate
    `γ4(y1, fhbY2Star y1, 2,2,2,2,2) ≥ 7e-3`  on  `y1 ∈ [2hmin, 2hplus]`,
whose global minimum `+7.3623e-3` is attained at the endpoint `y1 = 2hplus`
(the *double-radical* corner: `y2* = √((4 − (511/4489)·y1²) + (1250/4489)·√D)`).

This file is the reusable algebraic core for that certificate:

1. `g3c_curve_x2` — on the seam curve, `y2*²` is *affine* in `(y1², s)`,
   `s = √fhbD4(y1²)` the factorised-discriminant root.  Hence every
   polynomial quantity of `γ4` (the `deltaX` / `deltaX4` slot data) is a
   rational-coefficient polynomial in `(y1², s)` — no nested radicals beyond
   the single `s`.
2. `g3c_dihXf_eq` — the generic slot reduction
   `dihXf x⃗ = π/2 + arctan (−deltaX4 x⃗ / √(4 x1 deltaX x⃗))`, valid on the
   `|deltaX4| < √(4 x1 deltaX)` branch (the branch active on the whole seam
   curve, seam-lane recon).  Together with (1) each of the 14 distinct
   `arctan` slot arguments is `v(y1², s) / √u2(y1², s)` with explicit
   rational polynomials `v, u2`.
3. The consumable curve certificate `γ4 ≥ 7e-3` itself is NOT in this file —
   it is a remaining obligation.  What is delivered: the algebraic core
   (1)+(2) plus `g3c_arctan_of_bounds`; the assembled bound needs the
   `g4v_corner_value_bounds` kit (V/S/D bounds) with the coefficient
   intervals `g4v_AB_bounds`, and the per-box `V/S/D` slot bounds are
   open obligations (see lane Evidence.md).  The right-endpoint instance
   `g3c_endpoint_gamma4` is proven in `Kepler.Text.FhbG3posEndpoint`.

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited at
the tail.
-/
import Kepler.Text.FhbEtaCurve
import Kepler.Text.Gamma4ValCornerKit
import Kepler.Text.Gamma4WideKink

set_option maxHeartbeats 4000000

namespace Kepler.Text

/-- `arctan` two-sided bounds from a two-sided argument bracket: if
`g ∈ [glo, ghi]`, `alo ≤ arctan glo` and `arctan ghi ≤ ahi`, then
`arctan g ∈ [alo, ahi]` (monotonicity). -/
theorem g3c_arctan_of_bounds {g glo ghi alo ahi : ℝ}
    (hglo : glo ≤ g) (hghi : g ≤ ghi)
    (halo : alo ≤ Real.arctan glo) (hahi : Real.arctan ghi ≤ ahi) :
    alo ≤ Real.arctan g ∧ Real.arctan g ≤ ahi :=
  ⟨le_trans halo (Real.arctan_mono hglo), le_trans (Real.arctan_mono hghi) hahi⟩

/-! ## 1. The seam curve is affine in `(y1², s)`

`fhbX2Root x1 = (1250/4489)·(−B + √D)`; expanding `−B` at `b = 4` gives the
affine form.  With `s = √fhbD4(y1²)` this makes every slot polynomial
rational in `(y1², s)`. -/

/-- On the seam curve, `y2*²` is affine in `(y1², s)`, `s = √fhbD4(y1²)`:
`(fhbY2Star y1)² = (4 − (511/4489)·y1²) + (1250/4489)·s`. -/
theorem g3c_curve_x2 {y1 : ℝ} (h1 : 2 * hminus ≤ y1) (h1' : y1 ≤ 2 * hplus) :
    fhbY2Star y1 * fhbY2Star y1
      = (4 - (511 / 4489) * (y1 * y1))
        + (1250 / 4489) * Real.sqrt (fhbD4 (y1 * y1)) := by
  have hb := fhbX2Root_bounds h1 h1'
  have hroot_nn : (0:ℝ) ≤ fhbX2Root (y1 * y1) := by linarith [hb.1]
  have hsq : fhbY2Star y1 * fhbY2Star y1 = fhbX2Root (y1 * y1) := by
    unfold fhbY2Star
    exact Real.mul_self_sqrt hroot_nn
  rw [hsq]
  unfold fhbX2Root fhbD4
  ring

/-! ## 2. The generic slot reduction

`dihXf x⃗ = π/2 + atn2 (√(4 x1 Δ), −Δ4)`; on the `|Δ4| < √(4 x1 Δ)` branch
`atn2` is `arctan (−Δ4 / √(4 x1 Δ))`.  This is the only branch on the seam
curve (seam-lane recon: `|−Δ4|/√(4 x1 Δ) ≤ ~0.34` with margin). -/

/-- Generic `dihXf` reduction to a single `arctan` on the `|Δ4| < √(4 x1 Δ)`
branch. -/
theorem g3c_dihXf_eq {x1 x2 x3 x4 x5 x6 : ℝ}
    (hbr : |deltaX4 x1 x2 x3 x4 x5 x6|
      < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) :
    dihXf x1 x2 x3 x4 x5 x6
      = Real.pi / 2 + Real.arctan (-(deltaX4 x1 x2 x3 x4 x5 x6)
          / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) := by
  unfold dihXf
  rw [atn2]
  rw [abs_neg]
  rw [if_pos hbr]

/-- The `dihY` form of the reduction (squared lengths). -/
theorem g3c_dihY_eq {y1 y2 y3 y4 y5 y6 : ℝ}
    (hbr : |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)|
      < Real.sqrt (4 * (y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))) :
    dihY y1 y2 y3 y4 y5 y6
      = Real.pi / 2 + Real.arctan (-(deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))
          / Real.sqrt (4 * (y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))) := by
  unfold dihY
  exact g3c_dihXf_eq hbr

#print axioms g3c_curve_x2
#print axioms g3c_dihXf_eq
#print axioms g3c_dihY_eq

end Kepler.Text
