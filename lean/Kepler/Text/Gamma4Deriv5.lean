/-
Kepler.Text.Gamma4Deriv5 — lane `gamma4-w3`, part 3: `solY` y-partials.

`solY a = dihY a + dihY (a₂,a₃,a₁,a₅,a₆,a₄) + dihY (a₃,a₁,a₂,a₆,a₄,a₅) − π`,
so each slot partial is the sum of three `dihY` slot partials
(`g4dDSolY1..6` below).  The hypotheses are positivity of `y₁,y₂,y₃` (the first
arguments of the three permuted `dihY` calls) and `0 < deltaY`; the permuted
`deltaY` facts are transported with `g4d_deltaY_p231564` / `_p312645`.
-/
import Kepler.Text.Gamma4Deriv4

set_option maxHeartbeats 4000000

open Filter
open scoped Topology

namespace Kepler.Text

/-! ## The six `solY` slot derivative values -/

noncomputable def g4dDSolY1 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  g4dDDihY1 y1 y2 y3 y4 y5 y6
    + g4dDDihY3 y2 y3 y1 y5 y6 y4
    + g4dDDihY2 y3 y1 y2 y6 y4 y5

noncomputable def g4dDSolY2 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  g4dDDihY2 y1 y2 y3 y4 y5 y6
    + g4dDDihY1 y2 y3 y1 y5 y6 y4
    + g4dDDihY3 y3 y1 y2 y6 y4 y5

noncomputable def g4dDSolY3 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  g4dDDihY3 y1 y2 y3 y4 y5 y6
    + g4dDDihY2 y2 y3 y1 y5 y6 y4
    + g4dDDihY1 y3 y1 y2 y6 y4 y5

noncomputable def g4dDSolY4 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  g4dDDihY4 y1 y2 y3 y4 y5 y6
    + g4dDDihY6 y2 y3 y1 y5 y6 y4
    + g4dDDihY5 y3 y1 y2 y6 y4 y5

noncomputable def g4dDSolY5 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  g4dDDihY5 y1 y2 y3 y4 y5 y6
    + g4dDDihY4 y2 y3 y1 y5 y6 y4
    + g4dDDihY6 y3 y1 y2 y6 y4 y5

noncomputable def g4dDSolY6 (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  g4dDDihY6 y1 y2 y3 y4 y5 y6
    + g4dDDihY5 y2 y3 y1 y5 y6 y4
    + g4dDDihY4 y3 y1 y2 y6 y4 y5

theorem solY_hasDerivAt_y1 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => solY t y2 y3 y4 y5 y6) (g4dDSolY1 y1 y2 y3 y4 y5 y6) y1 := by
  have h1 : HasDerivAt (fun t => dihY t y2 y3 y4 y5 y6)
      (g4dDDihY1 y1 y2 y3 y4 y5 y6) y1 :=
    dihY_hasDerivAt_y1 y1 y2 y3 y4 y5 y6 hy1 hd
  have h2 : HasDerivAt (fun t => dihY y2 y3 t y5 y6 y4)
      (g4dDDihY3 y2 y3 y1 y5 y6 y4) y1 :=
    dihY_hasDerivAt_y3 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => dihY y3 t y2 y6 y4 y5)
      (g4dDDihY2 y3 y1 y2 y6 y4 y5) y1 :=
    dihY_hasDerivAt_y2 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have h := ((h1.add h2).add h3).sub_const Real.pi
  rw [g4dDSolY1]
  convert h using 1 <;> rfl

theorem solY_hasDerivAt_y2 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => solY y1 t y3 y4 y5 y6) (g4dDSolY2 y1 y2 y3 y4 y5 y6) y2 := by
  have h1 : HasDerivAt (fun t => dihY y1 t y3 y4 y5 y6)
      (g4dDDihY2 y1 y2 y3 y4 y5 y6) y2 :=
    dihY_hasDerivAt_y2 y1 y2 y3 y4 y5 y6 hy1 hd
  have h2 : HasDerivAt (fun t => dihY t y3 y1 y5 y6 y4)
      (g4dDDihY1 y2 y3 y1 y5 y6 y4) y2 :=
    dihY_hasDerivAt_y1 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => dihY y3 y1 t y6 y4 y5)
      (g4dDDihY3 y3 y1 y2 y6 y4 y5) y2 :=
    dihY_hasDerivAt_y3 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have h := ((h1.add h2).add h3).sub_const Real.pi
  rw [g4dDSolY2]
  convert h using 1 <;> rfl

theorem solY_hasDerivAt_y3 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => solY y1 y2 t y4 y5 y6) (g4dDSolY3 y1 y2 y3 y4 y5 y6) y3 := by
  have h1 : HasDerivAt (fun t => dihY y1 y2 t y4 y5 y6)
      (g4dDDihY3 y1 y2 y3 y4 y5 y6) y3 :=
    dihY_hasDerivAt_y3 y1 y2 y3 y4 y5 y6 hy1 hd
  have h2 : HasDerivAt (fun t => dihY y2 t y1 y5 y6 y4)
      (g4dDDihY2 y2 y3 y1 y5 y6 y4) y3 :=
    dihY_hasDerivAt_y2 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => dihY t y1 y2 y6 y4 y5)
      (g4dDDihY1 y3 y1 y2 y6 y4 y5) y3 :=
    dihY_hasDerivAt_y1 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have h := ((h1.add h2).add h3).sub_const Real.pi
  rw [g4dDSolY3]
  convert h using 1 <;> rfl

theorem solY_hasDerivAt_y4 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => solY y1 y2 y3 t y5 y6) (g4dDSolY4 y1 y2 y3 y4 y5 y6) y4 := by
  have h1 : HasDerivAt (fun t => dihY y1 y2 y3 t y5 y6)
      (g4dDDihY4 y1 y2 y3 y4 y5 y6) y4 :=
    dihY_hasDerivAt_y4 y1 y2 y3 y4 y5 y6 hy1 hd
  have h2 : HasDerivAt (fun t => dihY y2 y3 y1 y5 y6 t)
      (g4dDDihY6 y2 y3 y1 y5 y6 y4) y4 :=
    dihY_hasDerivAt_y6 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => dihY y3 y1 y2 y6 t y5)
      (g4dDDihY5 y3 y1 y2 y6 y4 y5) y4 :=
    dihY_hasDerivAt_y5 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have h := ((h1.add h2).add h3).sub_const Real.pi
  rw [g4dDSolY4]
  convert h using 1 <;> rfl

theorem solY_hasDerivAt_y5 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => solY y1 y2 y3 y4 t y6) (g4dDSolY5 y1 y2 y3 y4 y5 y6) y5 := by
  have h1 : HasDerivAt (fun t => dihY y1 y2 y3 y4 t y6)
      (g4dDDihY5 y1 y2 y3 y4 y5 y6) y5 :=
    dihY_hasDerivAt_y5 y1 y2 y3 y4 y5 y6 hy1 hd
  have h2 : HasDerivAt (fun t => dihY y2 y3 y1 t y6 y4)
      (g4dDDihY4 y2 y3 y1 y5 y6 y4) y5 :=
    dihY_hasDerivAt_y4 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => dihY y3 y1 y2 y6 y4 t)
      (g4dDDihY6 y3 y1 y2 y6 y4 y5) y5 :=
    dihY_hasDerivAt_y6 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have h := ((h1.add h2).add h3).sub_const Real.pi
  rw [g4dDSolY5]
  convert h using 1 <;> rfl

theorem solY_hasDerivAt_y6 (y1 y2 y3 y4 y5 y6 : ℝ) (hy1 : 0 < y1) (hy2 : 0 < y2)
    (hy3 : 0 < y3) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6) :
    HasDerivAt (fun t => solY y1 y2 y3 y4 y5 t) (g4dDSolY6 y1 y2 y3 y4 y5 y6) y6 := by
  have h1 : HasDerivAt (fun t => dihY y1 y2 y3 y4 y5 t)
      (g4dDDihY6 y1 y2 y3 y4 y5 y6) y6 :=
    dihY_hasDerivAt_y6 y1 y2 y3 y4 y5 y6 hy1 hd
  have h2 : HasDerivAt (fun t => dihY y2 y3 y1 y5 t y4)
      (g4dDDihY5 y2 y3 y1 y5 y6 y4) y6 :=
    dihY_hasDerivAt_y5 y2 y3 y1 y5 y6 y4 hy2 (by rw [g4d_deltaY_p231564]; exact hd)
  have h3 : HasDerivAt (fun t => dihY y3 y1 y2 t y4 y5)
      (g4dDDihY4 y3 y1 y2 y6 y4 y5) y6 :=
    dihY_hasDerivAt_y4 y3 y1 y2 y6 y4 y5 hy3 (by rw [g4d_deltaY_p312645]; exact hd)
  have h := ((h1.add h2).add h3).sub_const Real.pi
  rw [g4dDSolY6]
  convert h using 1 <;> rfl

/-! ## Axiom audit -/

#print axioms solY_hasDerivAt_y1
#print axioms solY_hasDerivAt_y2
#print axioms solY_hasDerivAt_y3
#print axioms solY_hasDerivAt_y4
#print axioms solY_hasDerivAt_y5
#print axioms solY_hasDerivAt_y6

end Kepler.Text
