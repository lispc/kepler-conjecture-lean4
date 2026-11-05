/-
Kepler.Text.Gamma4SharpRoute — machine-checked reductions of the two sharp
TSKAJXY bank statements to explicit analytic premises.

Lane `gamma4-sharp`.  NEITHER bank is proved here, and nothing enters the
environment: the unproved analytic content sits in explicit hypothesis slots
(the repo's `p21i_derived4` / `h4 : cell4_from_ineq` explicit-premise
pattern).

* `bank_TSKAJXYRIBCYXUsharp_of_mono` (box `[2,2.001]⁶`, HOL ineq.hl:165):
  the bank follows from the corner identity `gamma4_at_regular` plus
  coordinatewise monotonicity of `gamma4fgcy · lmfun` on the box.
  Numerically the slot holds with min partial derivative `0.08217 > 0`
  over the box (grid 5⁶ + 20k random samples), so this is the right debt
  shape for that bank.
* `bank_TSKAJXYIYOUOBFsharpv2_of_reduce` (HOL ineq.hl:242): the bank follows
  from monotonicity in `y2,y3,y5,y6` plus the two-variable inequality at
  `(y2,y3,y5,y6) = (2,2,2,2)`.  This is the *corrected* route: on that box
  `gamma4fgcy` is NOT monotone in `y1` (∂ ∈ [+0.023, −0.021] over
  `[2hplus,√8]`) nor in `y4` (∂ ∈ [+0.083, −0.089] over `[2,2hmin]`), so
  the all-six-variable route cannot apply to this bank.  The four remaining
  slots are numerically clean (min ∂ = 0.1314), and the 2-variable premise
  has its minimum `0` exactly at the `(√8, 2)` corner proved in
  `Gamma4Sharp.gamma4_at_sqrt8`.
-/
import Kepler.Text.Gamma4Sharp

set_option maxHeartbeats 5000000

namespace Kepler.Text

/-- Box predicate for the RIBCYXU sharp bank `[2,2.001]⁶`. -/
private def g4sInBox (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  2 ≤ y1 ∧ y1 ≤ 2.001 ∧ 2 ≤ y2 ∧ y2 ≤ 2.001 ∧ 2 ≤ y3 ∧ y3 ≤ 2.001 ∧
    2 ≤ y4 ∧ y4 ≤ 2.001 ∧ 2 ≤ y5 ∧ y5 ≤ 2.001 ∧ 2 ≤ y6 ∧ y6 ≤ 2.001

private theorem g4sInBox_corner : g4sInBox 2 2 2 2 2 2 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Route closure for `bank_TSKAJXYRIBCYXUsharp`.**  The single unproved
slot `hmono` is coordinatewise monotonicity of `gamma4fgcy · lmfun` on the
box (numerically verified: min partial derivative `0.08217`). -/
theorem bank_TSKAJXYRIBCYXUsharp_of_mono
    (hmono : ∀ y1 y2 y3 y4 y5 y6 y1' y2' y3' y4' y5' y6' : ℝ,
      g4sInBox y1 y2 y3 y4 y5 y6 → g4sInBox y1' y2' y3' y4' y5' y6' →
      y1 ≤ y1' → y2 ≤ y2' → y3 ≤ y3' → y4 ≤ y4' → y5 ≤ y5' → y6 ≤ y6' →
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun ≤
        gamma4fgcy y1' y2' y3' y4' y5' y6' lmfun)
    : bank_TSKAJXYRIBCYXUsharp := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have key := hmono 2 2 2 2 2 2 y1 y2 y3 y4 y5 y6 g4sInBox_corner
    ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ h1 h2 h3 h4 h5 h6
  rw [gamma4_at_regular] at key
  exact key

/-! ## The `YOUOBF sharp v2` bank

The v2 box has `y1 ∈ [2hplus, √8]` and `y4 ∈ [2, 2hmin]`; on those wider
ranges `gamma4fgcy` is not monotone, so the reduction keeps `(y1, y4)`
fixed and carries the remaining two-variable inequality as `h2d`. -/

/-- Box predicate for the four monotone slots of the v2 bank. -/
private def g4sInBox24 (y2 y3 y5 y6 : ℝ) : Prop :=
  2 ≤ y2 ∧ y2 ≤ 2.001 ∧ 2 ≤ y3 ∧ y3 ≤ 2.001 ∧
    2 ≤ y5 ∧ y5 ≤ 2.001 ∧ 2 ≤ y6 ∧ y6 ≤ 2.001

private theorem g4sInBox24_corner : g4sInBox24 2 2 2 2 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Route closure for `bank_TSKAJXYIYOUOBFsharpv2`.**  Two unproved slots:
`hmono` (coordinatewise monotonicity in `y2,y3,y5,y6`, numerically
`min ∂ = 0.1314`) and `h2d` (the `(y1,y4)` inequality at the remaining
coordinates `2`; numerically `min = 0`, attained exactly at `(√8, 2)`). -/
theorem bank_TSKAJXYIYOUOBFsharpv2_of_reduce
    (hmono : ∀ y1 y2 y3 y4 y5 y6 y2' y3' y5' y6' : ℝ,
      2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 →
      2 ≤ y4 → y4 ≤ 2 * hminus →
      g4sInBox24 y2 y3 y5 y6 → g4sInBox24 y2' y3' y5' y6' →
      y2 ≤ y2' → y3 ≤ y3' → y5 ≤ y5' → y6 ≤ y6' →
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun ≤
        gamma4fgcy y1 y2' y3' y4 y5' y6' lmfun)
    (h2d : ∀ y1 y4 : ℝ, 2 * hplus ≤ y1 → y1 ≤ Real.sqrt 8 →
      2 ≤ y4 → y4 ≤ 2 * hminus → 0 ≤ gamma4fgcy y1 2 2 y4 2 2 lmfun)
    : bank_TSKAJXYIYOUOBFsharpv2 := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have s0 : 0 ≤ gamma4fgcy y1 2 2 y4 2 2 lmfun := h2d y1 y4 h1 h1' h4 h4'
  have s1 : gamma4fgcy y1 2 2 y4 2 2 lmfun ≤
      gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun :=
    hmono y1 2 2 y4 2 2 y2 y3 y5 y6 h1 h1' h4 h4' g4sInBox24_corner
      ⟨h2, h2', h3, h3', h5, h5', h6, h6'⟩ h2 h3 h5 h6
  exact le_trans s0 s1

/-! ## Axiom audit (house style) -/

#print axioms Kepler.Text.bank_TSKAJXYRIBCYXUsharp_of_mono
#print axioms Kepler.Text.bank_TSKAJXYIYOUOBFsharpv2_of_reduce

end Kepler.Text
