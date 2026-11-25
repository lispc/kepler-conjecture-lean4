/-
Kepler.Text.TaylorSecond.MatanC1 — `matan` is `C¹` on the whole domain
`(-1, ∞)` (lane `wt1-m9-emission-w1`, 2026-11-25).

The landed `contDiffAt_matan_of_pos` (Wt1C2/DCJet) covers `t > 0` only, while
the M9 endpoint-monotone value bracket evaluates `matan` at endpoints that may
be negative (the 8 Dlt-crossing boxes have `matan` arguments in `(-0.69, 0)`
at one end) and the `JetMem` chain rule needs `ContDiffAt ℝ 1 matan` there.
`matan_hasDerivAt` is already global on `(-1, ∞)`; what was missing is the
continuity of the derivative function `matanD` on `(-1, ∞)`, proved here from
the slope at `0` (`matanD 0 = -1/3` is the removable-singularity value) plus
the closed form on the punctured domain.  The landed `contDiffOn_matanD_pos`
covers `(0, ∞)` only.

These five lemmas were first proved inside each M9 emitted box file (~110
lines × 221); this module lands them once.  They are extracted verbatim from
the green sample `W1DC_15869_LLLLLLL_zero_0` (M9 v4, 221/221 pre-flight).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.MatanNegKit
import Kepler.Text.TaylorSecond.DCJet
import Kepler.Text.Wt1TowerKit

set_option maxHeartbeats 32000000
set_option maxRecDepth 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Kepler.Text.TaylorSecond
namespace MatanC1

open Kepler.Text
open Filter
open scoped Topology ContDiff

/-! ## 2b. The M9 matan plumbing

The landed `contDiffAt_matan_of_pos` covers `t > 0` only, while the M9 value
bracket is taken at endpoints that may be negative (the 8 Dlt-crossing boxes)
and the `JetMem` chain rule needs `ContDiffAt ℝ 1 matan` there.
`matan_hasDerivAt` is global on `(-1, ∞)`; what is missing is the continuity of
the derivative function `matanD` on `(-1, ∞)`, proved below from the slope at
`0` (`matanD 0 = -1/3` is its removable-singularity value) plus the closed
form on `(-1, 0)`.  The landed `contDiffOn_matanD_pos` covers `(0, ∞)`. -/

theorem continuousAt_matanD_zero : ContinuousAt matanD (0:ℝ) := by
  have hslope : Tendsto (fun t : ℝ => (matan t - matan 0) / t) (𝓝[≠] 0) (𝓝 (-(1/3))) := by
    have h := (matan_hasDerivAt (show (-1:ℝ) < 0 by norm_num)).tendsto_slope_zero
    rw [matanD_zero] at h
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  have hIoo : Set.Ioo (-(1/2):ℝ) (1/2) ∈ 𝓝[≠] (0:ℝ) :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (show (-(1/2):ℝ) < 0 by norm_num)
      (show (0:ℝ) < 1/2 by norm_num))
  have hA : Tendsto (fun t : ℝ => (1/(1+t) - 1)/(2*t)) (𝓝[≠] 0) (𝓝 (-(1/2))) := by
    have heq : (fun t : ℝ => (1/(1+t) - 1)/(2*t)) =ᶠ[𝓝[≠] 0] (fun t => -(1/(2*(1+t)))) := by
      filter_upwards [self_mem_nhdsWithin, hIoo] with t ht hI
      have ht0 : t ≠ 0 := by simpa using ht
      have h1t : (1:ℝ) + t ≠ 0 := by
        intro hc; linarith [hI.1]
      field_simp
      ring
    rw [tendsto_congr' heq]
    have hlin : ContinuousAt (fun t : ℝ => 2*(1+t)) 0 := by fun_prop
    have hne : (fun t : ℝ => 2*(1+t)) 0 ≠ 0 := by norm_num
    have h2 : ContinuousAt (fun t : ℝ => ((2*(1+t)))⁻¹) 0 := hlin.inv₀ hne
    have h3 : ContinuousAt (fun t : ℝ => -((2*(1+t)))⁻¹) 0 := h2.neg
    have hc : ContinuousAt (fun t : ℝ => -(1/(2*(1+t)))) 0 := by simpa [one_div] using h3
    have h4 := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    have h6 : (-(1/(2*(1+(0:ℝ))))) = (-(1/2):ℝ) := by norm_num
    rwa [h6] at h4
  have hB : Tendsto (fun t : ℝ => (matan 0 - matan t)/(2*t)) (𝓝[≠] 0) (𝓝 ((1:ℝ)/6)) := by
    have heq : (fun t : ℝ => (matan 0 - matan t)/(2*t))
        = fun t => (-(1/2)) * ((matan t - matan 0)/t) := by
      funext t; ring
    rw [heq]
    have h := hslope.const_mul (-(1/2))
    convert h using 2
    norm_num
  have heqD : matanD =ᶠ[𝓝[≠] 0]
      (fun t => (1/(1+t) - 1)/(2*t) + (matan 0 - matan t)/(2*t)) := by
    filter_upwards [self_mem_nhdsWithin, hIoo] with t ht hI
    have ht0 : t ≠ 0 := by simpa using ht
    have h1t : (1:ℝ) + t ≠ 0 := by
      intro hc; linarith [hI.1]
    rw [matanD_of_ne ht0, lkB_matan_zero]
    field_simp
    ring
  have hsum : Tendsto (fun t : ℝ => (1/(1+t) - 1)/(2*t) + (matan 0 - matan t)/(2*t))
      (𝓝[≠] 0) (𝓝 (-(1/3))) := by
    have h := hA.add hB
    convert h using 2
    norm_num
  have h2 : Tendsto matanD (𝓝[≠] 0) (𝓝 (-(1/3))) := hsum.congr' heqD.symm
  have hpure : Tendsto matanD (pure (0:ℝ)) (𝓝 (-(1/3))) := by
    have h := tendsto_pure_nhds matanD (0:ℝ)
    rwa [matanD_zero] at h
  have hall : Tendsto matanD (𝓝 (0:ℝ)) (𝓝 (-(1/3))) := by
    rw [← nhdsNE_sup_pure, tendsto_sup]
    exact ⟨h2, hpure⟩
  rwa [ContinuousAt, matanD_zero]

/-- `matanD` is continuous at every `t ≠ 0` inside the domain. -/
theorem continuousAt_matanD_of_ne {t : ℝ} (ht1 : -1 < t) (ht0 : t ≠ 0) :
    ContinuousAt matanD t := by
  have ht1' : (1:ℝ) + t ≠ 0 := by
    intro hc; linarith
  have hmat : ContinuousAt matan t := (matan_hasDerivAt ht1).continuousAt
  have heq : matanD =ᶠ[𝓝 t] (fun y => (1/(2*y)) * (1/(1+y) - matan y)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using ht0)] with y hy
    exact matanD_of_ne hy
  have hnum : ContinuousAt (fun y : ℝ => 1/(1+y) - matan y) t := by
    have h1 : ContinuousAt (fun y : ℝ => (1+y)⁻¹) t :=
      (by fun_prop : ContinuousAt (fun y : ℝ => 1+y) t).inv₀ (by simpa using ht1')
    have h2 : ContinuousAt (fun y : ℝ => 1/(1+y)) t := by simpa [one_div] using h1
    exact h2.sub hmat
  have hden : ContinuousAt (fun y : ℝ => (2*y)⁻¹) t :=
    (by fun_prop : ContinuousAt (fun y : ℝ => 2*y) t).inv₀ (by simp [ht0])
  have hprod := hden.mul hnum
  have hfin : ContinuousAt (fun y : ℝ => (1/(2*y)) * (1/(1+y) - matan y)) t := by
    have hfeq : ((fun y : ℝ => (2*y)⁻¹) * fun y => 1 / (1 + y) - matan y)
        = fun y => (1/(2*y)) * (1/(1+y) - matan y) := by
      funext y; rw [one_div]; rfl
    rw [← hfeq]
    exact hprod
  exact hfin.congr heq.symm

/-- `matanD` is continuous on `(-1, ∞)`. -/
theorem continuousOn_matanD : ContinuousOn matanD (Set.Ioi (-1)) := by
  intro t ht
  by_cases h : t = 0
  · subst h
    exact continuousAt_matanD_zero.continuousWithinAt
  · exact (continuousAt_matanD_of_ne ht h).continuousWithinAt

/-- **`matan` is `C¹` on `(-1, ∞)`** (the landed `contDiffAt_matan_of_pos` is
`t > 0` only). -/
theorem contDiffOn_matan_gt : ContDiffOn ℝ 1 matan (Set.Ioi (-1)) := by
  have hderiv : ContDiffOn ℝ 0 (deriv matan) (Set.Ioi (-1)) := by
    rw [contDiffOn_zero]
    exact continuousOn_matanD.congr (fun t ht => (matan_hasDerivAt ht).deriv)
  rw [show (1 : ℕ∞ω) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, by norm_num, hderiv⟩
  intro t ht
  exact (matan_hasDerivAt ht).differentiableAt.differentiableWithinAt

theorem contDiffAt_matan_gt {t : ℝ} (ht : -1 < t) : ContDiffAt ℝ 1 matan t :=
  (contDiffOn_matan_gt t (Set.mem_Ioi.mpr ht)).contDiffAt (isOpen_Ioi.mem_nhds ht)

#print axioms continuousAt_matanD_zero
#print axioms continuousAt_matanD_of_ne
#print axioms continuousOn_matanD
#print axioms contDiffOn_matan_gt
#print axioms contDiffAt_matan_gt

end MatanC1
end Kepler.Text.TaylorSecond
