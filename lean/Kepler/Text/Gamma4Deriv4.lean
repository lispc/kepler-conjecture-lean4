/-
Kepler.Text.Gamma4Deriv4 — lane `gamma4-w3`, part 2: `dihY` y-partials.

`dihY y = dihXf (y₁²,…,y₆²)`, so the slot-`k` partial is
`2·yₖ · (∂dihXf/∂xₖ at the squared arguments)`.  The six `HasDerivAt`
theorems below state exactly this (`g4dDDihY1..6` are the derivative values).
The only hypotheses are `0 < a₁` (first argument of the `dihXf` call, needed
for the square root) and `0 < deltaY` (needed for `4·x₁·Δ ≠ 0`).
-/
import Kepler.Text.Gamma4Deriv3

set_option maxHeartbeats 4000000

open Filter
open scoped Topology

namespace Kepler.Text

/-! ## The six `dihY` slot derivative values

For an argument tuple `a₁…a₆`, `g4dDDihYₖ a` is `2·aₖ·g4dDihXₖ` at the
squared arguments. -/

noncomputable def g4dDDihY1 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * a1 * g4dDihX1 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)

noncomputable def g4dDDihY2 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * a2 * g4dDihX2 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)

noncomputable def g4dDDihY3 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * a3 * g4dDihX3 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)

noncomputable def g4dDDihY4 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * a4 * g4dDihX4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)

noncomputable def g4dDDihY5 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * a5 * g4dDihX5 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)

noncomputable def g4dDDihY6 (a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  2 * a6 * g4dDihX6 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)

theorem dihY_hasDerivAt_y1 (a1 a2 a3 a4 a5 a6 : ℝ) (ha1 : 0 < a1)
    (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => dihY t a2 a3 a4 a5 a6) (g4dDDihY1 a1 a2 a3 a4 a5 a6) a1 := by
  have hF : HasDerivAt (fun s => dihXf s (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))
      (g4dDihX1 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))
      (a1 * a1) :=
    dihXf_hasDerivAt_x1 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)
      (by positivity) (by simpa only [deltaY] using hd)
  have h := g4d_hasDerivAt_sq_comp hF
  rw [g4dDDihY1]
  convert h using 1
  · funext t; simp only [dihY]
  · ring

theorem dihY_hasDerivAt_y2 (a1 a2 a3 a4 a5 a6 : ℝ) (ha1 : 0 < a1)
    (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => dihY a1 t a3 a4 a5 a6) (g4dDDihY2 a1 a2 a3 a4 a5 a6) a2 := by
  have hF : HasDerivAt (fun s => dihXf (a1 * a1) s (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))
      (g4dDihX2 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))
      (a2 * a2) :=
    dihXf_hasDerivAt_x2 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)
      (by positivity) (by simpa only [deltaY] using hd)
  have h := g4d_hasDerivAt_sq_comp hF
  rw [g4dDDihY2]
  convert h using 1
  · funext t; simp only [dihY]
  · ring

theorem dihY_hasDerivAt_y3 (a1 a2 a3 a4 a5 a6 : ℝ) (ha1 : 0 < a1)
    (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => dihY a1 a2 t a4 a5 a6) (g4dDDihY3 a1 a2 a3 a4 a5 a6) a3 := by
  have hF : HasDerivAt (fun s => dihXf (a1 * a1) (a2 * a2) s (a4 * a4) (a5 * a5) (a6 * a6))
      (g4dDihX3 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))
      (a3 * a3) :=
    dihXf_hasDerivAt_x3 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)
      (by positivity) (by simpa only [deltaY] using hd)
  have h := g4d_hasDerivAt_sq_comp hF
  rw [g4dDDihY3]
  convert h using 1
  · funext t; simp only [dihY]
  · ring

theorem dihY_hasDerivAt_y4 (a1 a2 a3 a4 a5 a6 : ℝ) (ha1 : 0 < a1)
    (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => dihY a1 a2 a3 t a5 a6) (g4dDDihY4 a1 a2 a3 a4 a5 a6) a4 := by
  have hF : HasDerivAt (fun s => dihXf (a1 * a1) (a2 * a2) (a3 * a3) s (a5 * a5) (a6 * a6))
      (g4dDihX4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))
      (a4 * a4) :=
    dihXf_hasDerivAt_x4 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)
      (by positivity) (by simpa only [deltaY] using hd)
  have h := g4d_hasDerivAt_sq_comp hF
  rw [g4dDDihY4]
  convert h using 1
  · funext t; simp only [dihY]
  · ring

theorem dihY_hasDerivAt_y5 (a1 a2 a3 a4 a5 a6 : ℝ) (ha1 : 0 < a1)
    (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => dihY a1 a2 a3 a4 t a6) (g4dDDihY5 a1 a2 a3 a4 a5 a6) a5 := by
  have hF : HasDerivAt (fun s => dihXf (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) s (a6 * a6))
      (g4dDihX5 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))
      (a5 * a5) :=
    dihXf_hasDerivAt_x5 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)
      (by positivity) (by simpa only [deltaY] using hd)
  have h := g4d_hasDerivAt_sq_comp hF
  rw [g4dDDihY5]
  convert h using 1
  · funext t; simp only [dihY]
  · ring

theorem dihY_hasDerivAt_y6 (a1 a2 a3 a4 a5 a6 : ℝ) (ha1 : 0 < a1)
    (hd : 0 < deltaY a1 a2 a3 a4 a5 a6) :
    HasDerivAt (fun t => dihY a1 a2 a3 a4 a5 t) (g4dDDihY6 a1 a2 a3 a4 a5 a6) a6 := by
  have hF : HasDerivAt (fun s => dihXf (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) s)
      (g4dDihX6 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6))
      (a6 * a6) :=
    dihXf_hasDerivAt_x6 (a1 * a1) (a2 * a2) (a3 * a3) (a4 * a4) (a5 * a5) (a6 * a6)
      (by positivity) (by simpa only [deltaY] using hd)
  have h := g4d_hasDerivAt_sq_comp hF
  rw [g4dDDihY6]
  convert h using 1
  · funext t; simp only [dihY]
  · ring

/-! ## Axiom audit -/

#print axioms dihY_hasDerivAt_y1
#print axioms dihY_hasDerivAt_y2
#print axioms dihY_hasDerivAt_y3
#print axioms dihY_hasDerivAt_y4
#print axioms dihY_hasDerivAt_y5
#print axioms dihY_hasDerivAt_y6

end Kepler.Text
