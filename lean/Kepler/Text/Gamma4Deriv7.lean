/-
Kepler.Text.Gamma4Deriv7 — lane `gamma4-w3`, part 4b: the remaining three
`vol4f` y-partials (`y4`, `y5`, `y6`); see `Gamma4Deriv6` for the setup.
-/
import Kepler.Text.Gamma4Deriv6

set_option maxHeartbeats 4000000

open Filter
open scoped Topology

namespace Kepler.Text

/-! ## The three remaining derivative values -/

noncomputable def g4dDVol4f4 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (g4dDSolY4 y1 y2 y3 y4 y5 y6
     + g4dDSolY4 y1 y5 y6 y4 y2 y3
     + g4dDSolY1 y4 y5 y3 y1 y2 y6
     + g4dDSolY1 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * g4dDDihY4 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * g4dDDihY6 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * g4dDDihY5 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * g4dDDihY1 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * g4dDDihY5 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * g4dDDihY5 y6 y1 y5 y3 y4 y2
     + (L / 2) * dihY y4 y3 y5 y1 y6 y2)

noncomputable def g4dDVol4f5 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (g4dDSolY5 y1 y2 y3 y4 y5 y6
     + g4dDSolY2 y1 y5 y6 y4 y2 y3
     + g4dDSolY2 y4 y5 y3 y1 y2 y6
     + g4dDSolY5 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * g4dDDihY5 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * g4dDDihY4 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * g4dDDihY6 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * g4dDDihY3 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * g4dDDihY1 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * g4dDDihY3 y6 y1 y5 y3 y4 y2
     + (L / 2) * dihY y5 y1 y6 y2 y4 y3)

noncomputable def g4dDVol4f6 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (g4dDSolY6 y1 y2 y3 y4 y5 y6
     + g4dDSolY3 y1 y5 y6 y4 y2 y3
     + g4dDSolY6 y4 y5 y3 y1 y2 y6
     + g4dDSolY3 y4 y2 y6 y1 y5 y3)
  - (8 * mm2 / Real.pi) *
    (lmfun (y1 / 2) * g4dDDihY6 y1 y2 y3 y4 y5 y6
     + lmfun (y2 / 2) * g4dDDihY5 y2 y3 y1 y5 y6 y4
     + lmfun (y3 / 2) * g4dDDihY4 y3 y1 y2 y6 y4 y5
     + lmfun (y4 / 2) * g4dDDihY5 y4 y3 y5 y1 y6 y2
     + lmfun (y5 / 2) * g4dDDihY3 y5 y1 y6 y2 y4 y3
     + lmfun (y6 / 2) * g4dDDihY1 y6 y1 y5 y3 y4 y2
     + (L / 2) * dihY y6 y1 y5 y3 y4 y2)


theorem vol4f_hasDerivAt_y4 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y4 / 2)) :
    HasDerivAt (fun t => vol4f y1 y2 y3 t y5 y6 lmfun) (g4dDVol4f4 y1 y2 y3 y4 y5 y6 L) y4 := by
  have s1 := solY_hasDerivAt_y4 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd
  have s2 := solY_hasDerivAt_y4 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd)
  have s3 := solY_hasDerivAt_y1 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd)
  have s4 := solY_hasDerivAt_y1 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := dihY_hasDerivAt_y4 y1 y2 y3 y4 y5 y6 hy1 hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := dihY_hasDerivAt_y6 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := dihY_hasDerivAt_y5 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := dihY_hasDerivAt_y1 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y4) hf
  have d4 := hf2.mul dt4
  have dt5 := dihY_hasDerivAt_y5 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := dihY_hasDerivAt_y5 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6)
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [g4dDVol4f4]
  convert h using 1
  all_goals first | rfl | ring

theorem vol4f_hasDerivAt_y5 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y5 / 2)) :
    HasDerivAt (fun t => vol4f y1 y2 y3 y4 t y6 lmfun) (g4dDVol4f5 y1 y2 y3 y4 y5 y6 L) y5 := by
  have s1 := solY_hasDerivAt_y5 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd
  have s2 := solY_hasDerivAt_y2 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd)
  have s3 := solY_hasDerivAt_y2 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd)
  have s4 := solY_hasDerivAt_y5 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := dihY_hasDerivAt_y5 y1 y2 y3 y4 y5 y6 hy1 hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := dihY_hasDerivAt_y4 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := dihY_hasDerivAt_y6 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := dihY_hasDerivAt_y3 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := dihY_hasDerivAt_y1 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y5) hf
  have d5 := hf2.mul dt5
  have dt6 := dihY_hasDerivAt_y3 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have d6 := dt6.const_mul (lmfun (y6 / 2))
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6)
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [g4dDVol4f5]
  convert h using 1
  all_goals first | rfl | ring

theorem vol4f_hasDerivAt_y6 (y1 y2 y3 y4 y5 y6 : ℝ) (L : ℝ)
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y6 / 2)) :
    HasDerivAt (fun t => vol4f y1 y2 y3 y4 y5 t lmfun) (g4dDVol4f6 y1 y2 y3 y4 y5 y6 L) y6 := by
  have s1 := solY_hasDerivAt_y6 y1 y2 y3 y4 y5 y6 hy1 hy2 hy3 hd
  have s2 := solY_hasDerivAt_y3 y1 y5 y6 y4 y2 y3 hy1 hy5 hy6 (by rw [g4d_deltaY_p156423]; exact hd)
  have s3 := solY_hasDerivAt_y6 y4 y5 y3 y1 y2 y6 hy4 hy5 hy3 (by rw [g4d_deltaY_p453126]; exact hd)
  have s4 := solY_hasDerivAt_y3 y4 y2 y6 y1 y5 y3 hy4 hy2 hy6 (by rw [g4d_deltaY_p426153]; exact hd)
  have hS := ((s1.add s2).add s3).add s4
  have dt1 := dihY_hasDerivAt_y6 y1 y2 y3 y4 y5 y6 hy1 hd
  have d1 := dt1.const_mul (lmfun (y1 / 2))
  have dt2 := dihY_hasDerivAt_y5 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have d2 := dt2.const_mul (lmfun (y2 / 2))
  have dt3 := dihY_hasDerivAt_y4 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have d3 := dt3.const_mul (lmfun (y3 / 2))
  have dt4 := dihY_hasDerivAt_y5 y4 y3 y5 y1 y6 y2 hy4 (by rw [g4d_deltaY_p435162]; exact hd)
  have d4 := dt4.const_mul (lmfun (y4 / 2))
  have dt5 := dihY_hasDerivAt_y3 y5 y1 y6 y2 y4 y3 hy5 (by rw [g4d_deltaY_p516243]; exact hd)
  have d5 := dt5.const_mul (lmfun (y5 / 2))
  have dt6 := dihY_hasDerivAt_y1 y6 y1 y5 y3 y4 y2 hy6 (by rw [g4d_deltaY_p615342]; exact hd)
  have hf2 := g4d_hasDerivAt_lmfun_div2 (x := y6) hf
  have d6 := hf2.mul dt6
  have hD := (((((d1.add d2).add d3).add d4).add d5).add d6)
  have h := (hS.const_mul (2 * mm1 / Real.pi)).sub (hD.const_mul (8 * mm2 / Real.pi))
  rw [g4dDVol4f6]
  convert h using 1
  all_goals first | rfl | ring

/-! ## Axiom audit -/

#print axioms vol4f_hasDerivAt_y4
#print axioms vol4f_hasDerivAt_y5
#print axioms vol4f_hasDerivAt_y6

end Kepler.Text
