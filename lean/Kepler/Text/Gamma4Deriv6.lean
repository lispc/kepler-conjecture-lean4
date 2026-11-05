/-
Kepler.Text.Gamma4Deriv6 — lane `gamma4-w3`, part 4a: `vol4f` y-partials.

`vol4f y f = (2·mm1/π)·Σ_{4 terms} solY − (8·mm2/π)·Σ_{6 terms} f(y_j/2)·dihY`.
Differentiating in `yᵢ` gives `g4dDVol4f1..6`; the only occurrence of the
`f`-derivative is the one weighted term whose first argument is `yᵢ`, so the
statement carries `hf : HasDerivAt lmfun L (yᵢ/2)` generically (the two branch
values `L = −1/(h0−1)` and `L = 0` are supplied by
`g4d_lmfun_hasDerivAt_of_lt` / `_of_gt`).  This file has the helper lemmas,
the six derivative functions and the first three slot theorems; the other
three are in `Gamma4Deriv7`.
-/
import Kepler.Text.Gamma4Deriv5

set_option maxHeartbeats 4000000

open Filter
open scoped Topology

namespace Kepler.Text

/-! ## `lmfun` derivatives on the two branches -/

/-- `lmfun` on the affine branch `h < h0` (eventually equals `(h0−h)/(h0−1)`). -/
theorem g4d_lmfun_hasDerivAt_of_lt {x : ℝ} (hx : x < h0) :
    HasDerivAt lmfun (-1 / (h0 - 1)) x := by
  have he : lmfun =ᶠ[𝓝 x] fun q : ℝ => (h0 - q) / (h0 - 1) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with q hq
    simp only [Set.mem_Iio] at hq
    simp only [lmfun, if_pos (le_of_lt hq)]
  have h : HasDerivAt (fun q : ℝ => (h0 - q) / (h0 - 1)) ((0 - 1) / (h0 - 1)) x :=
    ((hasDerivAt_const (x := x) (c := h0)).sub (hasDerivAt_id x)).div_const (h0 - 1)
  have h' : HasDerivAt (fun q : ℝ => (h0 - q) / (h0 - 1)) (-1 / (h0 - 1)) x :=
    h.congr_deriv (by ring)
  exact h'.congr_of_eventuallyEq he

/-- `lmfun` on the zero branch `h0 < h`. -/
theorem g4d_lmfun_hasDerivAt_of_gt {x : ℝ} (hx : h0 < x) :
    HasDerivAt lmfun 0 x := by
  have he : lmfun =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with q hq
    simp only [Set.mem_Ioi] at hq
    simp only [lmfun, if_neg (not_le.mpr hq)]
  exact (hasDerivAt_const (x := x) (c := 0)).congr_of_eventuallyEq he

/-- `t ↦ lmfun (t/2)`, chain rule: the point is `x`, the inner value `x/2`. -/
theorem g4d_hasDerivAt_lmfun_div2 {L x : ℝ} (hf : HasDerivAt lmfun L (x / 2)) :
    HasDerivAt (fun t : ℝ => lmfun (t / 2)) (L * (1 / 2)) x := by
  have hdiv : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have h := HasDerivAt.comp (𝕜 := ℝ) (x := x) (h := fun t : ℝ => t / 2) (h₂ := lmfun)
    hf hdiv
  convert h using 1 <;> rfl


noncomputable def g4dDVol4f1 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (g4dDSolY1 y1 y2 y3 y4 y5 y6
     + g4dDSolY1 y1 y5 y6 y4 y2 y3
     + g4dDSolY4 y4 y5 y3 y1 y2 y6
     + g4dDSolY4 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * g4dDDihY1 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * g4dDDihY3 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * g4dDDihY2 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * g4dDDihY4 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * g4dDDihY2 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * g4dDDihY2 y6 y1 y5 y3 y4 y2
     + (L / 2) * dihY y1 y2 y3 y4 y5 y6)

noncomputable def g4dDVol4f2 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (g4dDSolY2 y1 y2 y3 y4 y5 y6
     + g4dDSolY5 y1 y5 y6 y4 y2 y3
     + g4dDSolY5 y4 y5 y3 y1 y2 y6
     + g4dDSolY2 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * g4dDDihY2 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * g4dDDihY1 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * g4dDDihY3 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * g4dDDihY6 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * g4dDDihY4 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * g4dDDihY6 y6 y1 y5 y3 y4 y2
     + (L / 2) * dihY y2 y3 y1 y5 y6 y4)

noncomputable def g4dDVol4f3 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (g4dDSolY3 y1 y2 y3 y4 y5 y6
     + g4dDSolY6 y1 y5 y6 y4 y2 y3
     + g4dDSolY3 y4 y5 y3 y1 y2 y6
     + g4dDSolY6 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * g4dDDihY3 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * g4dDDihY2 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * g4dDDihY1 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * g4dDDihY2 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * g4dDDihY6 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * g4dDDihY4 y6 y1 y5 y3 y4 y2
     + (L / 2) * dihY y3 y1 y2 y6 y4 y5)

theorem vol4f_hasDerivAt_y1 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y1 / 2)) :
    HasDerivAt (fun t => vol4f t y2 y3 y4 y5 y6 lmfun) (g4dDVol4f1 y1 y2 y3 y4 y5 y6 L) y1 := by
  have s1 := solY_hasDerivAt_y1 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd
  have s2 := solY_hasDerivAt_y1 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd)
  have s3 := solY_hasDerivAt_y4 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd)
  have s4 := solY_hasDerivAt_y4 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := dihY_hasDerivAt_y1 y1 y2 y3 y4 y5 y6 hy1 hd
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y1) hf
  have d1 := hf2.mul dt1
  have dt2 := dihY_hasDerivAt_y3 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := dihY_hasDerivAt_y2 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := dihY_hasDerivAt_y4 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := dihY_hasDerivAt_y2 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := dihY_hasDerivAt_y2 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6)
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [g4dDVol4f1]
  convert h using 1
  all_goals first | rfl | ring

theorem vol4f_hasDerivAt_y2 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y2 / 2)) :
    HasDerivAt (fun t => vol4f y1 t y3 y4 y5 y6 lmfun) (g4dDVol4f2 y1 y2 y3 y4 y5 y6 L) y2 := by
  have s1 := solY_hasDerivAt_y2 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd
  have s2 := solY_hasDerivAt_y5 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd)
  have s3 := solY_hasDerivAt_y5 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd)
  have s4 := solY_hasDerivAt_y2 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := dihY_hasDerivAt_y2 y1 y2 y3 y4 y5 y6 hy1 hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := dihY_hasDerivAt_y1 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y2) hf
  have d2 := hf2.mul dt2
  have dt3 := dihY_hasDerivAt_y3 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := dihY_hasDerivAt_y6 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := dihY_hasDerivAt_y4 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := dihY_hasDerivAt_y6 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6)
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [g4dDVol4f2]
  convert h using 1
  all_goals first | rfl | ring

theorem vol4f_hasDerivAt_y3 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y3 / 2)) :
    HasDerivAt (fun t => vol4f y1 y2 t y4 y5 y6 lmfun) (g4dDVol4f3 y1 y2 y3 y4 y5 y6 L) y3 := by
  have s1 := solY_hasDerivAt_y3 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd
  have s2 := solY_hasDerivAt_y6 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd)
  have s3 := solY_hasDerivAt_y3 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd)
  have s4 := solY_hasDerivAt_y6 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := dihY_hasDerivAt_y3 y1 y2 y3 y4 y5 y6 hy1 hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := dihY_hasDerivAt_y2 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := dihY_hasDerivAt_y1 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y3) hf
  have d3 := hf2.mul dt3
  have dt4 := dihY_hasDerivAt_y2 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := dihY_hasDerivAt_y6 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := dihY_hasDerivAt_y4 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6)
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [g4dDVol4f3]
  convert h using 1
  all_goals first | rfl | ring

/-! ## Axiom audit -/

#print axioms vol4f_hasDerivAt_y1
#print axioms vol4f_hasDerivAt_y2
#print axioms vol4f_hasDerivAt_y3

end Kepler.Text
