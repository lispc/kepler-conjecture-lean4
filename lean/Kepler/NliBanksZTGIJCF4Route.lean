/-
Kepler.NliBanksZTGIJCF4Route — lane `ztgijcf4-w1`.

## Verdict on the ten remaining `ZTGIJCF4` banks

The work order proposed to close

`nliRestZTGIJCF4_1_1_0_0`, `_1_0_0_1`, `_1_0_0_0`, `_0_1_1_0`, `_0_1_0_1`,
`_0_1_0_0`, `_0_0_1_1`, `_0_0_1_0`, `_0_0_0_1`, `_0_0_0_0`

with the `Kepler.NliBanks4/5` template: `bank_ZTGIJCF4lo/hi` expansion, the
`x = y²` box bounds, the `H_mono_*` / `HW_*` telescoping chain for
`H = rhoX − 8·deltaX`, and then a **positive rational corner value**
`H(corner) > 0`, which is equivalent to `rad2X > 2` on the box.

**That template cannot work for these ten**, and this module machine-checks it.
The second disjunct of `bank_ZTGIJCF4tmpl` is

`yOfX rad2X y1 … y6 > 2`  ⟺  `rhoX x − 8 · deltaX x > 0`  (as `deltaX > 0`),

and at the box point `y = (2.47, 2, 2.47 or 2, …)` (i.e. `x = (2.47², 4, …)`
with `xᵢ = 2.47² = 6.1009` on the critical slots and `xᵢ = 4` on the
subcritical ones) one has `rad2X < 2` on **all ten** boxes: the explicit
`norm_num` values are `1.6780` (`0_0_0_0`), `1.7626`, `1.8384`, `1.9212`,
`1.9518`.  These are exactly the ten boxes where `H(lower corner) < 0`
(`−51 … −188`), i.e. the six already-proved instances are the *only* six
whose corner value is positive.  The independent numeric sweep recorded in
`nli-triage-w1/NLI_MAP.md` §1 found the same phenomenon (`min rad2 =
1.67–1.94 < 2` on these boxes).

Consequently the only live branch on these ten boxes is the **main branch**

`gamma4fgcy y lmfun / w + m · betaBumpLb > aSpine5 + bSpine5 · dihY y`,
`w = 1 + Σ bankGenMid`, `m = [w = 2 ∧ i4 = 1]`,

whose positivity is `ztgMain > 0` below.  This module provides

* `ztgBox` — the bank box in y-space, shared by all sixteen instances;
* `ztgMain` + `ztg_of_main` — the exact main-branch reduction: positivity of
  `ztgMain` on `ztgBox` closes `bank_ZTGIJCF4tmpl i3 i4 i5 i6` with no further
  case analysis (same shape as `Kepler.Text.Gamma4WideBanks`' `_of_main`
  interfaces for the other eleven banks);
* `ztg_<bits>_rad2_refuted` (10) — machine-checked refutation of the `rad2`
  disjunct at an explicit rational box point;
* `ztg_<bits>_main_forced` (10) — therefore the bank, *at that point*, is
  equivalent to `ztgMain > 0`: the main branch is not optional.

What is **not** in this module, and why (see `TABLE.md` / `DELIVERY.md`): a
proof of `ztgMain > 0` on any of the ten boxes.  `ztgMain` contains
`sqrt`, `arctan` and `lmfun`, so the x-space ring-algebraic corner walk of
`NliBanks15/16` does not apply, and the only in-tree x↔y bridge
(`PackingAuto21.p21k_gamma4fgcy_div_sqrtdelta`) is `private` and consumes the
`p21k_euler_anchor` (recorded in `Kepler/NliBanks17.lean`; unproved at lane
time, since proved in-tree: `p21k_euler_anchor_true`, PA21:11558, landed
`ac1efea1a`).  The
numeric margins of the main branch on these boxes are `+0.0008 … +0.037`
(exploratory sweep, not verified), so a genuine proof needs a 6-variable
transcendental minimisation kit that does not exist in the tree.

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited at the
end of the file.
-/
import Kepler.NliBanks17

set_option maxHeartbeats 1000000

namespace Kepler.NliBanksZTGIJCF4Route
open Kepler.Text
open Kepler.NliHminus

/-! ## 1. The bank boxes and the main-branch functional -/

/-- The `ZTGIJCF4 i3 i4 i5 i6` bank box in y-space (`bank_ZTGIJCF4lo/hi`
spelled out on the four free slots). -/
def ztgBox (i3 i4 i5 i6 : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) : Prop :=
  2 * hminus ≤ y1 ∧ y1 ≤ 2 * hplus ∧ 2 ≤ y2 ∧ y2 ≤ 2 * hminus ∧
  bank_ZTGIJCF4lo i3 ≤ y3 ∧ y3 ≤ bank_ZTGIJCF4hi i3 ∧
  bank_ZTGIJCF4lo i4 ≤ y4 ∧ y4 ≤ bank_ZTGIJCF4hi i4 ∧
  bank_ZTGIJCF4lo i5 ≤ y5 ∧ y5 ≤ bank_ZTGIJCF4hi i5 ∧
  bank_ZTGIJCF4lo i6 ≤ y6 ∧ y6 ≤ bank_ZTGIJCF4hi i6

/-- `w = 1 + Σ bankGenMid` — the `gamma4fgcy` denominator of the bank. -/
noncomputable def ztgW (i3 i4 i5 i6 : ℕ) : ℝ :=
  1 + bankGenMid i3 + bankGenMid i4 + bankGenMid i5 + bankGenMid i6

/-- `m` — the `betaBumpLb` flag of the bank template (`w = 2 ∧ i4 = 1`). -/
noncomputable def ztgM (i3 i4 i5 i6 : ℕ) : ℝ :=
  if 1 + bankGenMid i3 + bankGenMid i4 + bankGenMid i5 + bankGenMid i6 = 2 ∧ i4 = 1
    then 1 else 0

/-- The **main branch**, shifted to a `> 0` form:
`γ4/w + m·β_lb − (a5 + b5·dihY)`. -/
noncomputable def ztgMain (i3 i4 i5 i6 : ℕ) (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun / ztgW i3 i4 i5 i6 +
    ztgM i3 i4 i5 i6 * betaBumpLb - (aSpine5 + bSpine5 * dihY y1 y2 y3 y4 y5 y6)

/-- **Main-branch reduction**: `ztgMain > 0` on the whole box closes the bank.

This is the exact residual obligation of the ten remaining instances; it is the
y-space analogue of `Kepler.Text.Gamma4WideBanks`' `nliRest*_of_main`. -/
theorem ztg_of_main (i3 i4 i5 i6 : ℕ)
    (h : ∀ y1 y2 y3 y4 y5 y6, ztgBox i3 i4 i5 i6 y1 y2 y3 y4 y5 y6 →
      0 < ztgMain i3 i4 i5 i6 y1 y2 y3 y4 y5 y6) :
    bank_ZTGIJCF4tmpl i3 i4 i5 i6 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  refine Or.inl ?_
  have hm := h y1 y2 y3 y4 y5 y6
    ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  unfold ztgMain ztgW ztgM at hm
  linarith [hm]

/-! ## 2. The witness point `(2.47, 2, 2.47/2, …)`

`2.47 = 247/100` sits strictly inside every slot interval: it is above
`2·hminus ≥ 2.4635` (from `nb17_two_hminus_bounds`), below `2·hplus = 2.6508`,
and below `√8` (`2.47² = 6.1009 < 8`). -/

theorem two_hminus_le_wit : 2 * hminus ≤ (247/100 : ℝ) := by
  have h := Kepler.NliBanks17.nb17_two_hminus_bounds
  linarith [h.2]

theorem two_le_two_hminus : (2:ℝ) ≤ 2 * hminus := by
  have h := Kepler.NliBanks17.nb17_two_hminus_bounds
  linarith [h.1]

theorem wit_le_two_hplus : (247/100 : ℝ) ≤ 2 * hplus := by
  rw [hplus]; norm_num

theorem wit_le_sqrt8 : (247/100 : ℝ) ≤ Real.sqrt 8 := by
  have h : (247/100 : ℝ) < Real.sqrt 8 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  linarith

theorem boxLo_zero : bank_ZTGIJCF4lo 0 ≤ (2:ℝ) := by simp [bank_ZTGIJCF4lo]

theorem boxHi_zero : (2:ℝ) ≤ bank_ZTGIJCF4hi 0 := by
  simp only [bank_ZTGIJCF4hi]
  norm_num
  have h := Kepler.NliBanks17.nb17_two_hminus_bounds
  linarith [h.1]

theorem boxLo_one : bank_ZTGIJCF4lo 1 ≤ (247/100 : ℝ) := by
  simp only [bank_ZTGIJCF4lo]
  norm_num
  exact two_hminus_le_wit

theorem boxHi_one : (247/100 : ℝ) ≤ bank_ZTGIJCF4hi 1 := by
  simp only [bank_ZTGIJCF4hi]
  norm_num
  exact wit_le_sqrt8

/-! ## 3. The ten refutations and the forced main branch -/

/-- **`ZTGIJCF4 1_1_0_0`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2.47, 2.47, 2, 2)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_1_1_0_0_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 1 1 0 0 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 1 1 0 0 (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_one, boxHi_one, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 1_1_0_0`**: at `(2.47, 2, 2.47, 2.47, 2, 2)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_1_1_0_0_main_forced (hb : bank_ZTGIJCF4_1_1_0_0) :
    0 < ztgMain 1 1 0 0 (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) := by
  have hbox : ztgBox 1 1 0 0 (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_one, boxHi_one, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-- **`ZTGIJCF4 1_0_0_1`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2.47, 2, 2, 2.47)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_1_0_0_1_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 1 0 0 1 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 1 0 0 1 (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 1_0_0_1`**: at `(2.47, 2, 2.47, 2, 2, 2.47)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_1_0_0_1_main_forced (hb : bank_ZTGIJCF4_1_0_0_1) :
    0 < ztgMain 1 0 0 1 (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) := by
  have hbox : ztgBox 1 0 0 1 (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-- **`ZTGIJCF4 1_0_0_0`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2.47, 2, 2, 2)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_1_0_0_0_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 1 0 0 0 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 1 0 0 0 (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 1_0_0_0`**: at `(2.47, 2, 2.47, 2, 2, 2)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_1_0_0_0_main_forced (hb : bank_ZTGIJCF4_1_0_0_0) :
    0 < ztgMain 1 0 0 0 (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) := by
  have hbox : ztgBox 1 0 0 0 (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-- **`ZTGIJCF4 0_1_1_0`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2, 2.47, 2.47, 2)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_0_1_1_0_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 0 1 1 0 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 0 1 1 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 0_1_1_0`**: at `(2.47, 2, 2, 2.47, 2.47, 2)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_0_1_1_0_main_forced (hb : bank_ZTGIJCF4_0_1_1_0) :
    0 < ztgMain 0 1 1 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) := by
  have hbox : ztgBox 0 1 1 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) (2:ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-- **`ZTGIJCF4 0_1_0_1`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2, 2.47, 2, 2.47)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_0_1_0_1_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 0 1 0 1 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 0 1 0 1 (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 0_1_0_1`**: at `(2.47, 2, 2, 2.47, 2, 2.47)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_0_1_0_1_main_forced (hb : bank_ZTGIJCF4_0_1_0_1) :
    0 < ztgMain 0 1 0 1 (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) := by
  have hbox : ztgBox 0 1 0 1 (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (247/100 : ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-- **`ZTGIJCF4 0_1_0_0`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2, 2.47, 2, 2)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_0_1_0_0_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 0 1 0 0 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 0 1 0 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 0_1_0_0`**: at `(2.47, 2, 2, 2.47, 2, 2)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_0_1_0_0_main_forced (hb : bank_ZTGIJCF4_0_1_0_0) :
    0 < ztgMain 0 1 0 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) := by
  have hbox : ztgBox 0 1 0 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) (2:ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-- **`ZTGIJCF4 0_0_1_1`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2, 2, 2.47, 2.47)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_0_0_1_1_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 0 0 1 1 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 0 0 1 1 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_one, boxHi_one⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 0_0_1_1`**: at `(2.47, 2, 2, 2, 2.47, 2.47)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_0_0_1_1_main_forced (hb : bank_ZTGIJCF4_0_0_1_1) :
    0 < ztgMain 0 0 1 1 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) := by
  have hbox : ztgBox 0 0 1 1 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_one, boxHi_one⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (247/100 : ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-- **`ZTGIJCF4 0_0_1_0`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2, 2, 2.47, 2)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_0_0_1_0_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 0 0 1 0 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 0 0 1 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 0_0_1_0`**: at `(2.47, 2, 2, 2, 2.47, 2)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_0_0_1_0_main_forced (hb : bank_ZTGIJCF4_0_0_1_0) :
    0 < ztgMain 0 0 1 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) := by
  have hbox : ztgBox 0 0 1 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one, boxLo_zero, boxHi_zero⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) (2:ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-- **`ZTGIJCF4 0_0_0_1`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2, 2, 2, 2.47)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_0_0_0_1_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 0 0 0 1 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 0 0 0 1 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 0_0_0_1`**: at `(2.47, 2, 2, 2, 2, 2.47)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_0_0_0_1_main_forced (hb : bank_ZTGIJCF4_0_0_0_1) :
    0 < ztgMain 0 0 0 1 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) := by
  have hbox : ztgBox 0 0 0 1 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_one, boxHi_one⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (247/100 : ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-- **`ZTGIJCF4 0_0_0_0`**: the `rad2` disjunct fails at the box point `(2.47, 2, 2, 2, 2, 2)`,
so this bank cannot be closed through the `NliBanks4/5` `H = rhoX − 8·deltaX`
corner template (the corner value is negative, not positive). -/
theorem ztg_0_0_0_0_rad2_refuted :
    ¬ (∀ y1 y2 y3 y4 y5 y6 : ℝ, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      2 < yOfX rad2X y1 y2 y3 y4 y5 y6) := by
  intro h
  have hbox : ztgBox 0 0 0 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero⟩
  have hnum := h (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) hbox
  simp only [yOfX, rad2X, rhoX, deltaX] at hnum
  norm_num at hnum

/-- **`ZTGIJCF4 0_0_0_0`**: at `(2.47, 2, 2, 2, 2, 2)` the bank can only hold through the
`gamma4fgcy` main branch. -/
theorem ztg_0_0_0_0_main_forced (hb : bank_ZTGIJCF4_0_0_0_0) :
    0 < ztgMain 0 0 0 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) := by
  have hbox : ztgBox 0 0 0 0 (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) := ⟨
     two_hminus_le_wit, wit_le_two_hplus, le_rfl, two_le_two_hminus, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero, boxLo_zero, boxHi_zero⟩
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hbox
  rcases hb (247/100 : ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) (2:ℝ) h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h with hA | hB
  · unfold ztgMain ztgW ztgM
    linarith [hA]
  · simp only [yOfX, rad2X, rhoX, deltaX] at hB
    norm_num at hB

/-! ## 4. Axiom audit (house style) -/

#print axioms ztg_of_main
#print axioms ztg_1_1_0_0_rad2_refuted
#print axioms ztg_1_1_0_0_main_forced
#print axioms ztg_1_0_0_1_rad2_refuted
#print axioms ztg_1_0_0_1_main_forced
#print axioms ztg_1_0_0_0_rad2_refuted
#print axioms ztg_1_0_0_0_main_forced
#print axioms ztg_0_1_1_0_rad2_refuted
#print axioms ztg_0_1_1_0_main_forced
#print axioms ztg_0_1_0_1_rad2_refuted
#print axioms ztg_0_1_0_1_main_forced
#print axioms ztg_0_1_0_0_rad2_refuted
#print axioms ztg_0_1_0_0_main_forced
#print axioms ztg_0_0_1_1_rad2_refuted
#print axioms ztg_0_0_1_1_main_forced
#print axioms ztg_0_0_1_0_rad2_refuted
#print axioms ztg_0_0_1_0_main_forced
#print axioms ztg_0_0_0_1_rad2_refuted
#print axioms ztg_0_0_0_1_main_forced
#print axioms ztg_0_0_0_0_rad2_refuted
#print axioms ztg_0_0_0_0_main_forced

end Kepler.NliBanksZTGIJCF4Route
