/-
Kepler.NliBanksZTGIJCF4Bounds — lane `ztgijcf4-w1`, part 2.

Two-scalar decomposition of the `ZTGIJCF4` main-branch residual
(`Kepler.NliBanksZTGIJCF4Route`): separate lower bounds on `gamma4fgcy` and
`dihY` plus a rational side condition close the bank.  This is the cheapest
shape for a future bounding kit, because the two transcendental pieces are then
minimised independently.  `TABLE.md` records, per instance, whether this
reduction can serve and with which candidate `(G, D)` (exploratory, not
verified).

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited.
-/
import Kepler.NliBanksZTGIJCF4Route

set_option maxHeartbeats 1000000

namespace Kepler.NliBanksZTGIJCF4Route
open Kepler.Text

/-! ## 3b. Two-scalar decomposition of the residual

The joint main-branch inequality is implied by *separate* bounds on the two
transcendental pieces, because `w > 0` and `bSpine5 < 0`:

`γ4 ≥ G`, `dihY ≥ D`, and `a5 + b5·D < G/w + m·β_lb`  ⟹  `ztgMain > 0`.

This splits the 6-variable problem into two independent scalar minimisations
(the shape every `Mathlib`-style bounding kit can attack separately).  It is
*not* strong enough for all ten boxes — see `TABLE.md` for which instances it
can serve and with which `(G, D)`. -/

theorem bankGenMid_eq (i : ℕ) : bankGenMid i = 0 ∨ bankGenMid i = 1 := by
  unfold bankGenMid
  split <;> simp

theorem ztgW_pos (i3 i4 i5 i6 : ℕ) : 0 < ztgW i3 i4 i5 i6 := by
  have e3 := bankGenMid_eq i3
  have e4 := bankGenMid_eq i4
  have e5 := bankGenMid_eq i5
  have e6 := bankGenMid_eq i6
  unfold ztgW
  rcases e3 with h3 | h3 <;> rcases e4 with h4 | h4 <;>
    rcases e5 with h5 | h5 <;> rcases e6 with h6 | h6 <;>
    rw [h3, h4, h5, h6] <;> norm_num

/-- **Two-scalar reduction**: separate `γ4` and `dihY` bounds plus a numeric
side condition close the bank. -/
theorem ztg_of_global_bounds (i3 i4 i5 i6 : ℕ) (G D : ℝ)
    (hG : ∀ y1 y2 y3 y4 y5 y6, ztgBox i3 i4 i5 i6 y1 y2 y3 y4 y5 y6 →
      G ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun)
    (hD : ∀ y1 y2 y3 y4 y5 y6, ztgBox i3 i4 i5 i6 y1 y2 y3 y4 y5 y6 →
      D ≤ dihY y1 y2 y3 y4 y5 y6)
    (hnum : aSpine5 + bSpine5 * D < G / ztgW i3 i4 i5 i6 + ztgM i3 i4 i5 i6 * betaBumpLb) :
    bank_ZTGIJCF4tmpl i3 i4 i5 i6 := by
  refine ztg_of_main i3 i4 i5 i6 ?_
  intro y1 y2 y3 y4 y5 y6 hy
  have hw : (0:ℝ) < ztgW i3 i4 i5 i6 := ztgW_pos i3 i4 i5 i6
  have hgl : G ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := hG y1 y2 y3 y4 y5 y6 hy
  have hdl : D ≤ dihY y1 y2 y3 y4 y5 y6 := hD y1 y2 y3 y4 y5 y6 hy
  have hdiv : G / ztgW i3 i4 i5 i6 ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / ztgW i3 i4 i5 i6 :=
    div_le_div_of_nonneg_right hgl hw.le
  have hb5 : bSpine5 < 0 := by rw [bSpine5]; norm_num
  have hbnd : aSpine5 + bSpine5 * dihY y1 y2 y3 y4 y5 y6 ≤ aSpine5 + bSpine5 * D := by
    nlinarith [hdl, hb5]
  unfold ztgMain
  linarith [hdiv, hbnd, hnum]

/-! ## Conditional closures with candidate constants

For the four boxes where the decoupled bound clears (see `TABLE.md`), the
reduction is instantiated with **exploratory** numeric constants: the numeric
sweep gives `min γ4` and `min dihY` a few `1e-3` above the constants used here,
but neither scalar bound is proved.  Treat these as the exact open obligations,
not as closures. -/

/-- Conditional closure of `ZTGIJCF4 1_1_0_0`; open obligations:
`γ4 ≥ 0.06` and `dihY ≥ 1.1` on the box. -/
theorem ztg_1_1_0_0_of_bounds
    (hG : ∀ y1 y2 y3 y4 y5 y6, ztgBox 1 1 0 0 y1 y2 y3 y4 y5 y6 →
      (0.06:ℝ) ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun)
    (hD : ∀ y1 y2 y3 y4 y5 y6, ztgBox 1 1 0 0 y1 y2 y3 y4 y5 y6 →
      (1.1:ℝ) ≤ dihY y1 y2 y3 y4 y5 y6) :
    bank_ZTGIJCF4_1_1_0_0 := by
  refine ztg_of_global_bounds 1 1 0 0 0.06 1.1 hG hD ?_
  norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-- Conditional closure of `ZTGIJCF4 0_1_1_0`; open obligations:
`γ4 ≥ 0.06` and `dihY ≥ 1.1` on the box. -/
theorem ztg_0_1_1_0_of_bounds
    (hG : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 1 1 0 y1 y2 y3 y4 y5 y6 →
      (0.06:ℝ) ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun)
    (hD : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 1 1 0 y1 y2 y3 y4 y5 y6 →
      (1.1:ℝ) ≤ dihY y1 y2 y3 y4 y5 y6) :
    bank_ZTGIJCF4_0_1_1_0 := by
  refine ztg_of_global_bounds 0 1 1 0 0.06 1.1 hG hD ?_
  norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-- Conditional closure of `ZTGIJCF4 0_1_0_1`; open obligations:
`γ4 ≥ 0.06` and `dihY ≥ 1.1` on the box. -/
theorem ztg_0_1_0_1_of_bounds
    (hG : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 1 0 1 y1 y2 y3 y4 y5 y6 →
      (0.06:ℝ) ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun)
    (hD : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 1 0 1 y1 y2 y3 y4 y5 y6 →
      (1.1:ℝ) ≤ dihY y1 y2 y3 y4 y5 y6) :
    bank_ZTGIJCF4_0_1_0_1 := by
  refine ztg_of_global_bounds 0 1 0 1 0.06 1.1 hG hD ?_
  norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-- Conditional closure of `ZTGIJCF4 0_0_1_1`; open obligations:
`γ4 ≥ 0.08` and `dihY ≥ 0.88` on the box. -/
theorem ztg_0_0_1_1_of_bounds
    (hG : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 1 1 y1 y2 y3 y4 y5 y6 →
      (0.08:ℝ) ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun)
    (hD : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 1 1 y1 y2 y3 y4 y5 y6 →
      (0.88:ℝ) ≤ dihY y1 y2 y3 y4 y5 y6) :
    bank_ZTGIJCF4_0_0_1_1 := by
  refine ztg_of_global_bounds 0 0 1 1 0.08 0.88 hG hD ?_
  norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-! ## Axiom audit (house style) -/

#print axioms bankGenMid_eq
#print axioms ztgW_pos
#print axioms ztg_of_global_bounds
#print axioms ztg_1_1_0_0_of_bounds
#print axioms ztg_0_1_1_0_of_bounds
#print axioms ztg_0_1_0_1_of_bounds
#print axioms ztg_0_0_1_1_of_bounds

end Kepler.NliBanksZTGIJCF4Route
