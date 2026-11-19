/-
Kepler.Text.FhbFloorMono — lane `fhb-floor-mono-w1`, 2026-11-18.

FHBVYXZa floor-monotonicity `m3 m4 m5` (the hypotheses of
`fhb_hba_of_floor3` in lane `fhb-seam-curve-w1`'s `FhbEtaCurve.lean`):
  m3 : ∀ y ∈ B0, γ4(y1,y2, 2 ,y4,y5,y6) ≤ γ4(y1,y2,y3,y4,y5,y6)
  m4 : ∀ y ∈ B0, γ4(y1,y2,y3, 2 ,y5,y6) ≤ γ4(y1,y2,y3,y4,y5,y6)
  m5 : ∀ y ∈ B0, γ4(y1,y2,y3,y4, 2 ,y6) ≤ γ4(y1,y2,y3,y4,y5,y6)
with `γ4 = fun y => gamma4fgcy y lmfun` on the B0 box `g4wB5`.

**Recon correction (this lane, three independent checks).** The first
partial derivatives `∂γ4/∂y3, ∂γ4/∂y4, ∂γ4/∂y5` are **NOT positive on the
whole B0 box**: each dips negative in the box-top region. Measured
(`dihXf`-calibrated mpmath evaluator of the seam lane, closed-form
`Gamma4Deriv` port agreeing with finite differences to 4+ digits, and
mpmath's own adaptive `diff`):
  ∂/∂y4 = −0.0401 at (2.5447, 2, 2, 2.3832, 2, 2)
  ∂/∂y4 = −0.0931 at (2.6508, 2, 2, 2.4635, 2, 2)
  ∂/∂y3 = −0.0579 at (2.6508, 2, 2.4635, 2, 2.4635, 2)
Hence the "first-derivative ≥ 0 on the fibre + `monotoneOn_of_deriv_nonneg`"
route is **structurally unavailable**: γ4 is not monotone in any of y3,y4,y5
on B0 (it rises off the floor, then sags, but stays above the floor value).

**What IS true (verified).** The floor-comparison statements m3/m4/m5
themselves hold on B0: 1500 random box points per axis give zero violations,
with interior minimum `γ4(full) − γ4(floor) ≈ +1e-4` (→ 0 as the slot → 2).
γ4 is concave in each of y3,y4,y5 on a 243-point box grid (second partial
< 0 everywhere, ≈ −0.5).

**Reduction delivered here.** For a function concave on `[a,b]`, the minimum
over `[a,b]` is attained at an endpoint (segment lower bound by the endpoint
minimum, `ConcaveOn.ge_on_segment`). Therefore each `m_i` follows from TWO
explicit obligations on B0:
  (H1) concavity of the slot fibre: `ConcaveOn ℝ (Icc 2 (2*hminus))` of
       `t ↦ γ4(..., t at slot i, ...)`;
  (H2) the endpoint comparison `γ4(..., 2, ...) ≤ γ4(..., 2*hminus, ...)`.
Both are exact analytic certificates still to be produced (see the lane
`DELIVERY.md`); this file is the machine-checked reduction that consumes them
and yields the exact `fhb_hba_of_floor3` hypothesis shapes. No `sorry` /
`axiom` / `native_decide`; every declaration is axiom-audited below.
-/
import Kepler.Text.Gamma4WideBanks
import Kepler.NliBanks17

set_option maxHeartbeats 4000000

open Set
open scoped Convex

namespace Kepler.Text

/-- Interval membership is segment membership on the real line. -/
theorem fhb_mem_segment_Icc {a b t : ℝ} (h : a ≤ b) (ht : t ∈ Icc a b) :
    t ∈ [a -[ℝ] b] := by
  rw [segment_eq_Icc h]
  exact ht

/-- The floor-edge fact `2 ≤ 2*hminus` packed from the bank bounds. -/
theorem fhb_two_le_two_hminus : (2:ℝ) ≤ 2 * hminus := by
  linarith [Kepler.NliBanks17.nb17_two_hminus_bounds.1]

/-! ## m3  (slot y3) ← fibre concavity + endpoint comparison -/

/-- **m3 ← concavity + endpoint.** Consumes
`(H1)` concavity of `t ↦ γ4(y1,y2,t,y4,y5,y6)` on `[2, 2*hminus]` and
`(H2)` `γ4(y1,y2,2,y4,y5,y6) ≤ γ4(y1,y2,2*hminus,y4,y5,y6)`; produces the
exact `fhb_hba_of_floor3` `m3` shape. -/
theorem fhb_m3_of_concaveOn_and_endpoint
    (hconc : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      ConcaveOn ℝ (Icc 2 (2 * hminus))
        (fun t => gamma4fgcy y1 y2 t y4 y5 y6 lmfun))
    (hend : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      gamma4fgcy y1 y2 2 y4 y5 y6 lmfun ≤ gamma4fgcy y1 y2 (2 * hminus) y4 y5 y6 lmfun) :
    ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      gamma4fgcy y1 y2 2 y4 y5 y6 lmfun ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  intro y1 y2 y3 y4 y5 y6 hb
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hb
  have hconc' := hconc y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have h2mem : (2:ℝ) ∈ Icc (2:ℝ) (2 * hminus) := ⟨le_refl _, fhb_two_le_two_hminus⟩
  have htm_mem : (2 * hminus) ∈ Icc (2:ℝ) (2 * hminus) :=
    ⟨fhb_two_le_two_hminus, le_refl _⟩
  have hy3mem : y3 ∈ Icc (2:ℝ) (2 * hminus) := ⟨h3l, h3h⟩
  have hseg := hconc'.ge_on_segment h2mem htm_mem
    (fhb_mem_segment_Icc fhb_two_le_two_hminus hy3mem)
  have hmin : min (gamma4fgcy y1 y2 2 y4 y5 y6 lmfun)
        (gamma4fgcy y1 y2 (2 * hminus) y4 y5 y6 lmfun)
      = gamma4fgcy y1 y2 2 y4 y5 y6 lmfun := min_eq_left (hend y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩)
  have hseg2 : min (gamma4fgcy y1 y2 2 y4 y5 y6 lmfun)
        (gamma4fgcy y1 y2 (2 * hminus) y4 y5 y6 lmfun)
      ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := hseg
  rw [hmin] at hseg2
  exact hseg2

/-! ## m4  (slot y4) ← fibre concavity + endpoint comparison -/

/-- **m4 ← concavity + endpoint.** Consumes
`(H1)` concavity of `t ↦ γ4(y1,y2,y3,t,y5,y6)` on `[2, 2*hminus]` and
`(H2)` `γ4(y1,y2,y3,2,y5,y6) ≤ γ4(y1,y2,y3,2*hminus,y5,y6)`; produces the
exact `fhb_hba_of_floor3` `m4` shape. -/
theorem fhb_m4_of_concaveOn_and_endpoint
    (hconc : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      ConcaveOn ℝ (Icc 2 (2 * hminus))
        (fun t => gamma4fgcy y1 y2 y3 t y5 y6 lmfun))
    (hend : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      gamma4fgcy y1 y2 y3 2 y5 y6 lmfun ≤ gamma4fgcy y1 y2 y3 (2 * hminus) y5 y6 lmfun) :
    ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      gamma4fgcy y1 y2 y3 2 y5 y6 lmfun ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  intro y1 y2 y3 y4 y5 y6 hb
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hb
  have hconc' := hconc y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have h2mem : (2:ℝ) ∈ Icc (2:ℝ) (2 * hminus) := ⟨le_refl _, fhb_two_le_two_hminus⟩
  have htm_mem : (2 * hminus) ∈ Icc (2:ℝ) (2 * hminus) :=
    ⟨fhb_two_le_two_hminus, le_refl _⟩
  have hy4mem : y4 ∈ Icc (2:ℝ) (2 * hminus) := ⟨h4l, h4h⟩
  have hseg := hconc'.ge_on_segment h2mem htm_mem
    (fhb_mem_segment_Icc fhb_two_le_two_hminus hy4mem)
  have hmin : min (gamma4fgcy y1 y2 y3 2 y5 y6 lmfun)
        (gamma4fgcy y1 y2 y3 (2 * hminus) y5 y6 lmfun)
      = gamma4fgcy y1 y2 y3 2 y5 y6 lmfun := min_eq_left (hend y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩)
  have hseg2 : min (gamma4fgcy y1 y2 y3 2 y5 y6 lmfun)
        (gamma4fgcy y1 y2 y3 (2 * hminus) y5 y6 lmfun)
      ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := hseg
  rw [hmin] at hseg2
  exact hseg2

/-! ## m5  (slot y5) ← fibre concavity + endpoint comparison -/

/-- **m5 ← concavity + endpoint.** Consumes
`(H1)` concavity of `t ↦ γ4(y1,y2,y3,y4,t,y6)` on `[2, 2*hminus]` and
`(H2)` `γ4(y1,y2,y3,y4,2,y6) ≤ γ4(y1,y2,y3,y4,2*hminus,y6)`; produces the
exact `fhb_hba_of_floor3` `m5` shape. -/
theorem fhb_m5_of_concaveOn_and_endpoint
    (hconc : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      ConcaveOn ℝ (Icc 2 (2 * hminus))
        (fun t => gamma4fgcy y1 y2 y3 y4 t y6 lmfun))
    (hend : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      gamma4fgcy y1 y2 y3 y4 2 y6 lmfun ≤ gamma4fgcy y1 y2 y3 y4 (2 * hminus) y6 lmfun) :
    ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      gamma4fgcy y1 y2 y3 y4 2 y6 lmfun ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  intro y1 y2 y3 y4 y5 y6 hb
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hb
  have hconc' := hconc y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have h2mem : (2:ℝ) ∈ Icc (2:ℝ) (2 * hminus) := ⟨le_refl _, fhb_two_le_two_hminus⟩
  have htm_mem : (2 * hminus) ∈ Icc (2:ℝ) (2 * hminus) :=
    ⟨fhb_two_le_two_hminus, le_refl _⟩
  have hy5mem : y5 ∈ Icc (2:ℝ) (2 * hminus) := ⟨h5l, h5h⟩
  have hseg := hconc'.ge_on_segment h2mem htm_mem
    (fhb_mem_segment_Icc fhb_two_le_two_hminus hy5mem)
  have hmin : min (gamma4fgcy y1 y2 y3 y4 2 y6 lmfun)
        (gamma4fgcy y1 y2 y3 y4 (2 * hminus) y6 lmfun)
      = gamma4fgcy y1 y2 y3 y4 2 y6 lmfun := min_eq_left (hend y1 y2 y3 y4 y5 y6 ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩)
  have hseg2 : min (gamma4fgcy y1 y2 y3 y4 2 y6 lmfun)
        (gamma4fgcy y1 y2 y3 y4 (2 * hminus) y6 lmfun)
      ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := hseg
  rw [hmin] at hseg2
  exact hseg2

/-! ## Axiom audit (house style) -/

#print axioms fhb_mem_segment_Icc
#print axioms fhb_two_le_two_hminus
#print axioms fhb_m3_of_concaveOn_and_endpoint
#print axioms fhb_m4_of_concaveOn_and_endpoint
#print axioms fhb_m5_of_concaveOn_and_endpoint

end Kepler.Text
