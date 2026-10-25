/-
Kepler.Text.EulerAtn2Kit — Euler 泛型立体角工程 W1 波 (lane AY): the full
`atn2` kit + the generic `sol_euler_x = sqrt(delta_x) * sol_euler_x_div_sqrtdelta`
rescaling + the two anchor statements (6-premise HOL-merge form and the
8-premise backup form).

Provenance (HOL originals under `reference/flyspeck/text_formalization/`):
  * `atn2` kit      : trig1.hl:341 ATN2_BREAKDOWN (four branches),
                      trig1.hl:420 ATN2_RNEG, merge_ineq.hl:600 ATN2_POS,
                      merge_ineq.hl:614 ATN2_LE_PI2, merge_ineq.hl:592
                      pi2_sub_atn2, merge_ineq.hl:584 matan_pos.
  * rescaling       : merge_ineq.hl:1060 `sol_x_sol_x_sqrtdelta`, with
                      `sol_euler_x` inlined as
                      `2 * atn2 (2 * eulerA_x) (sqrt delta_x)` (sphere.hl:735).
  * `ea1_eulerAX`   : sphere.hl:830 `eulerA_x` — bridge copy of
                      PackingAuto21.eulerAX (this lane must NOT import PA21;
                      the bodies are verbatim identical, W5 wires via rfl).
  * anchors         : mirrors of `p21k_euler_anchor` (PA21:10973, 6-premise)
                      with `0 < x2 → 0 < x3 →` added for the backup form.

RECORDED STATEMENT GAP (not fixed here, scout §5.2): HOL
`sol_x_sol_x_sqrtdelta` carries `0 < x2 /\ 0 < x3`; the 6-premise anchor
drops them (upsX > 0 does not imply x2 > 0), so it is a strengthened merge.
Both statements are recorded; only the W1 rescaling theorem is proved —
the anchors wait for W2-W4 (W1 is statement + kit only).

Acceptance valve: the regular-tetrahedron reverse unit test
`ea1_regular_tetrahedron_check` reduces both sides of the rescaling at
(4,4,4,4,4,4) — `eulerA = 20`, `deltaX = 128` — to `2 * arctan (√2/5)`,
cross-checking `2*atn2(40, √128)` against `√128 · matan(2/25)/20`
(the ICD spot-check coordinates).
-/

import Kepler.Text.SphereKit
import Kepler.Text.IneqClosureDefs
import Mathlib

namespace Kepler.Text

/-! ## `ea1_eulerAX`: the `eulerA_x` body (bridge copy, no PA21 import) -/

/-- HOL `eulerA_x` (sphere.hl:830-833), verbatim = `PackingAuto21.eulerAX`
(bridge copy: importing PA21 here would create the PA21-ring the scout
forbids; the two defs have identical bodies, so `rfl` re-links them). -/
noncomputable def ea1_eulerAX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt x1 * Real.sqrt x2 * Real.sqrt x3 +
    Real.sqrt x1 * (x2 + x3 - x4) / 2 +
    Real.sqrt x2 * (x1 + x3 - x5) / 2 +
    Real.sqrt x3 * (x1 + x2 - x6) / 2

private theorem ea1_sqrtprod (x1 x2 x3 : ℝ) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) :
    Real.sqrt (x1 * x2 * x3) = Real.sqrt x1 * Real.sqrt x2 * Real.sqrt x3 := by
  rw [Real.sqrt_mul (mul_nonneg hx1 hx2) x3, Real.sqrt_mul hx1 x2]

/-- `solEulerXDivSqrtdelta` with its let-bound `a` presented as
`ea1_eulerAX` (the ICD def keeps `sqrt (x1*x2*x3)` unsplit). -/
private theorem ea1_solEulerXDivSqrtdelta_eq (x1 x2 x3 x4 x5 x6 : ℝ)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) :
    solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 =
      matan (deltaX x1 x2 x3 x4 x5 x6 / (4 * ea1_eulerAX x1 x2 x3 x4 x5 x6 ^ 2)) /
        ea1_eulerAX x1 x2 x3 x4 x5 x6 := by
  show matan (deltaX x1 x2 x3 x4 x5 x6 /
      (4 * (Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
        Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2) ^ 2)) /
    (Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
      Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2) =
    matan (deltaX x1 x2 x3 x4 x5 x6 / (4 * ea1_eulerAX x1 x2 x3 x4 x5 x6 ^ 2)) /
      ea1_eulerAX x1 x2 x3 x4 x5 x6
  rw [ea1_sqrtprod x1 x2 x3 hx1 hx2]
  rfl

/-! ## The `atn2` kit (trig1.hl + merge_ineq.hl:584-640) -/

/-- Branch 1 of `ATN2_BREAKDOWN` (copied from W2a `mi_p21e_atn2`,
PA21:2089): on `0 < a` the two-argument arctangent is the plain arctangent
of the ratio. -/
private theorem ea1_atn2_xpos (a b : ℝ) (ha : 0 < a) : atn2 a b = Real.arctan (b / a) := by
  rw [atn2]
  split_ifs with h1 h2 h3
  · rfl
  · have hba : 0 < b / a := div_pos h2 ha
    rw [show a / b = (b / a)⁻¹ from by field_simp, Real.arctan_inv_of_pos hba]
    ring
  · have hz : 0 < -(b / a) := by
      rw [neg_pos]
      exact div_neg_of_neg_of_pos h3 ha
    have h1' : a / b = -(-(b / a))⁻¹ := by field_simp
    have h2' : b / a = -(-(b / a)) := by ring
    rw [h1', Real.arctan_neg, Real.arctan_inv_of_pos hz, h2', Real.arctan_neg]
    ring
  · have hb0 : b = 0 := by linarith
    rw [hb0] at h1
    simp at h1
    linarith

/-- Branch 2: on `0 < b` the value is the first-quadrant complement. -/
private theorem ea1_atn2_ypos (a b : ℝ) (hb : 0 < b) :
    atn2 a b = Real.pi / 2 - Real.arctan (a / b) := by
  rw [atn2]
  split_ifs with h1 _ _
  · have hap : 0 < a := lt_of_le_of_lt (abs_nonneg b) h1
    have hba : 0 < b / a := div_pos hb hap
    rw [show a / b = (b / a)⁻¹ from by field_simp, Real.arctan_inv_of_pos hba]
    ring
  · rfl

/-- Branch 3: on `b < 0` the value is the negative mirror of branch 2. -/
private theorem ea1_atn2_yneg (a b : ℝ) (hb : b < 0) :
    atn2 a b = -(Real.pi / 2) - Real.arctan (a / b) := by
  rw [atn2]
  split_ifs with h1 h2 _
  · have hap : 0 < a := lt_of_le_of_lt (abs_nonneg b) h1
    have hz : 0 < -(b / a) := by
      rw [neg_pos]
      exact div_neg_of_neg_of_pos hb hap
    have h1' : a / b = -(-(b / a))⁻¹ := by field_simp
    have h2' : b / a = -(-(b / a)) := by ring
    rw [h1', Real.arctan_neg, Real.arctan_inv_of_pos hz, h2', Real.arctan_neg]
    ring
  · exact absurd (h2.trans hb) (by norm_num : ¬(0:ℝ) < 0)
  · rfl

/-- Branch 4: the degenerate corner (`y = 0`, `x ≤ 0`) is pinned to `π`. -/
private theorem ea1_atn2_corner (a b : ℝ) (hb0 : b = 0) (ha : a ≤ 0) :
    atn2 a b = Real.pi := by
  rw [atn2, hb0, abs_zero, if_neg (not_lt.mpr ha),
    if_neg (by norm_num : ¬(0:ℝ) < 0), if_neg (by norm_num : ¬(0:ℝ) < 0)]

/-- HOL `ATN2_BREAKDOWN` (trig1.hl:341-346): the four-branch specification
of `atn2`; together with the definition these suffice. -/
theorem ea1_atn2_breakdown (a b : ℝ) :
    (0 < a → atn2 a b = Real.arctan (b / a)) ∧
      (0 < b → atn2 a b = Real.pi / 2 - Real.arctan (a / b)) ∧
      (b < 0 → atn2 a b = -(Real.pi / 2) - Real.arctan (a / b)) ∧
      (b = 0 ∧ a ≤ 0 → atn2 a b = Real.pi) :=
  ⟨ea1_atn2_xpos a b, ea1_atn2_ypos a b, ea1_atn2_yneg a b, fun h =>
    ea1_atn2_corner a b h.1 h.2⟩

/-- HOL `atn2_0` (merge_ineq.hl:581, from `ATN2_BREAKDOWN` at `(0,0)`):
the junk corner value. -/
theorem ea1_atn2_0 : atn2 0 0 = Real.pi := by
  simp only [atn2, abs_zero, if_neg (by norm_num : ¬(0:ℝ) < 0)]

/-- HOL `ATN2_RNEG` (trig1.hl:420-434): oddness in the second argument,
off the corner. -/
theorem ea1_atn2_rneg (a b : ℝ) (h : b ≠ 0 ∨ 0 < a) : atn2 a (-b) = -atn2 a b := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · rw [ea1_atn2_yneg a b hb, ea1_atn2_ypos a (-b) (neg_pos.mpr hb),
      show a / -b = -(a / b) from by ring, Real.arctan_neg]
    ring
  · subst hb
    rcases h with hne | hpos
    · exact absurd rfl hne
    · rw [show (-0:ℝ) = 0 from by norm_num, ea1_atn2_xpos a 0 hpos,
        show (0:ℝ) / a = 0 by norm_num, Real.arctan_zero, neg_zero]
  · rw [ea1_atn2_ypos a b hb, ea1_atn2_yneg a (-b) (neg_lt_zero.mpr hb),
      show a / -b = -(a / b) from by ring, Real.arctan_neg]
    ring

/-- HOL `ATN2_POS` (merge_ineq.hl:600-613): with positive first argument,
the sign of `atn2 a b` is the sign of `b`. -/
theorem ea1_atn2_pos (a b : ℝ) (ha : 0 < a) : 0 < atn2 a b ↔ 0 < b := by
  constructor
  · intro hpos
    rcases lt_trichotomy b 0 with hb | hb | hb
    · exfalso
      have h3 : Real.arctan (a / b) = -Real.arctan (-(a / b)) := by
        rw [Real.arctan_neg, neg_neg]
      have h4 : Real.arctan (-(a / b)) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
      rw [ea1_atn2_yneg a b hb, h3] at hpos
      linarith
    · subst hb
      rw [ea1_atn2_xpos a 0 ha, show (0:ℝ) / a = 0 by norm_num,
        Real.arctan_zero] at hpos
      exact hpos
    · exact hb
  · intro hb
    rw [ea1_atn2_ypos a b hb]
    have h6 : 0 < Real.arctan (a / b) := Real.arctan_pos.mpr (div_pos ha hb)
    have h7 : Real.arctan (a / b) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    linarith

/-- HOL `ATN2_LE_PI2` (merge_ineq.hl:614-640): with positive first argument
the value never reaches `π/2`. -/
theorem ea1_atn2_le_pi2 (a b : ℝ) (ha : 0 < a) : atn2 a b < Real.pi / 2 := by
  rw [atn2]
  split_ifs with h1 h2 h3
  · exact Real.arctan_lt_pi_div_two _
  · have h6 : 0 < Real.arctan (a / b) := Real.arctan_pos.mpr (div_pos ha h2)
    linarith
  · have h6 := Real.neg_pi_div_two_lt_arctan (a / b)
    linarith [Real.pi_pos]
  · have h2' := not_lt.mp h2
    have h3' := not_lt.mp h3
    have h1' := not_lt.mp h1
    rw [show b = 0 from by linarith] at h1'
    simp only [abs_zero] at h1'
    linarith

/-- HOL `pi2_sub_atn2` (merge_ineq.hl:592-598): on the positive quadrant
the two argument orders are complementary. -/
theorem ea1_pi2_sub_atn2 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.pi / 2 - atn2 a b = atn2 b a := by
  rw [ea1_atn2_ypos a b hb, ea1_atn2_xpos b a hb]
  ring

/-- HOL `matan_pos` (merge_ineq.hl:584-591); copied from W2a
`mi_p21e_matan` (PA21:2108). -/
theorem ea1_matan_pos (z : ℝ) (hz : 0 < z) :
    matan z = Real.arctan (Real.sqrt z) / Real.sqrt z := by
  rw [matan, if_neg (ne_of_gt hz), if_pos hz]

/-! ## The W1 core: `sol_euler_x = sqrt(delta_x) * sol_euler_x_div_sqrtdelta` -/

/-- HOL `sol_x_sol_x_sqrtdelta` (merge_ineq.hl:1060-1065): the
`atn2`-to-`matan` rescaling half of the Euler solid-angle anchor, with
`sol_euler_x` inlined as `2 * atn2 (2 * eulerA_x) (sqrt delta_x)`
(sphere.hl:735-739).  The HOL-faithful premises `0 < x2`, `0 < x3` are kept
here; the strengthened 6-premise merge is recorded as `ea1_euler_anchor6`
(statement only, scout §5.2). -/
theorem ea1_sol_euler_x_sqrtdelta (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3)
    (ha : 0 < ea1_eulerAX x1 x2 x3 x4 x5 x6)
    (hd : 0 ≤ deltaX x1 x2 x3 x4 x5 x6) :
    2 * atn2 (2 * ea1_eulerAX x1 x2 x3 x4 x5 x6)
        (Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)) =
      Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) * solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 := by
  set a := ea1_eulerAX x1 x2 x3 x4 x5 x6 with hdefa
  rw [ea1_solEulerXDivSqrtdelta_eq _ _ _ _ _ _ (le_of_lt h1) (le_of_lt h2)]
  rcases le_iff_eq_or_lt.mp hd with hd0 | hd0
  · -- `delta_x = 0` branch: both sides vanish
    rw [← hd0, Real.sqrt_zero,
      ea1_atn2_xpos (2 * a) 0 (by linarith : (0:ℝ) < 2 * a),
      show (0:ℝ) / (2 * a) = 0 by norm_num, Real.arctan_zero]
    simp
  · -- `0 < delta_x` branch: `2 * atn2 (2a, √Δ) = √Δ · matan(Δ/(4a²))/a`
    have h2a : (0:ℝ) < 2 * a := by linarith
    have hsd : 0 < Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) := Real.sqrt_pos.mpr hd0
    have ha4 : (0:ℝ) < 4 * a ^ 2 := by positivity
    have h4a2 : Real.sqrt (4 * a ^ 2) = 2 * a := by
      rw [show (4:ℝ) * a ^ 2 = (2 * a) ^ 2 from by ring,
        Real.sqrt_sq (by linarith : (0:ℝ) ≤ 2 * a)]
    rw [ea1_atn2_xpos (2 * a) (Real.sqrt (deltaX x1 x2 x3 x4 x5 x6)) h2a,
      ea1_matan_pos _ (div_pos hd0 ha4), Real.sqrt_div (le_of_lt hd0), h4a2]
    have hane : a ≠ 0 := ne_of_gt ha
    have ht0 : Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) / (2 * a) ≠ 0 :=
      div_ne_zero hsd.ne' (ne_of_gt h2a)
    rw [← hdefa]
    field_simp [hane, hsd.ne', ht0]

/-! ## The two anchor statements (W5 consumers; proved in W2-W4) -/

/-- The 6-premise HOL-merge anchor: verbatim mirror of PA21
`p21k_euler_anchor` (:10973) with `ea1_eulerAX` for PA21's `eulerAX`.
This is the strengthened merge of merge_ineq.hl:841 `sol_x_sol_euler_x`
plus :1060 `sol_x_sol_x_sqrtdelta` — the latter's `0 < x2 /\ 0 < x3` is
dropped (recorded gap, scout §5.2).  Statement only in W1. -/
def ea1_euler_anchor6 : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ,
    0 < x1 → 0 < upsX x1 x2 x6 → 0 < upsX x2 x3 x4 → 0 < upsX x1 x3 x5 →
    0 < ea1_eulerAX x1 x2 x3 x4 x5 x6 → 0 < deltaX x1 x2 x3 x4 x5 x6 →
    solX x1 x2 x3 x4 x5 x6 =
      Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) * solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6

/-- The 8-premise BACKUP anchor (scout §5.2 mitigation): adds the
`sol_x_sol_x_sqrtdelta` premises `0 < x2`, `0 < x3` so the W1 rescaling
theorem `ea1_sol_euler_x_sqrtdelta` applies directly; the W5 consumer
`p21k_gamma4fgcy_div_sqrtdelta` carries `h1..h6` all-positive anyway.
Statement only in W1. -/
def ea1_euler_anchor8 : Prop :=
  ∀ x1 x2 x3 x4 x5 x6 : ℝ,
    0 < x1 → 0 < x2 → 0 < x3 →
    0 < upsX x1 x2 x6 → 0 < upsX x2 x3 x4 → 0 < upsX x1 x3 x5 →
    0 < ea1_eulerAX x1 x2 x3 x4 x5 x6 → 0 < deltaX x1 x2 x3 x4 x5 x6 →
    solX x1 x2 x3 x4 x5 x6 =
      Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) * solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6

/-- The backup anchor is implied by the 6-premise anchor (the latter has
strictly weaker hypotheses), so W5 wiring through the 8-premise form is
safe. -/
theorem ea1_euler_anchor8_of_anchor6 (h : ea1_euler_anchor6) : ea1_euler_anchor8 := by
  intro x1 x2 x3 x4 x5 x6 h1 h2 h3 u1 u2 u3 he hd
  exact h x1 x2 x3 x4 x5 x6 h1 u1 u2 u3 he hd

/-! ## Regular-tetrahedron reverse unit test (WAVES W1 acceptance) -/

/-- WAVES W1 acceptance valve: at the regular-tetrahedron point
(4,4,4,4,4,4) (`eulerA = 20`, `deltaX = 128`) both sides of the rescaling
reduce independently — the `atn2` side via `ea1_atn2_xpos`, the `matan`
side via `ea1_matan_pos` — to the same closed form
`2 * arctan (√2/5)`, cross-checking `2*atn2(40, √128)` against
`√128 · matan(2/25)/20` (the ICD spot-check coordinates). -/
theorem ea1_regular_tetrahedron_check :
    2 * atn2 (2 * ea1_eulerAX 4 4 4 4 4 4) (Real.sqrt (deltaX 4 4 4 4 4 4))
      = Real.sqrt (deltaX 4 4 4 4 4 4) * solEulerXDivSqrtdelta 4 4 4 4 4 4 := by
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h20 : ea1_eulerAX 4 4 4 4 4 4 = 20 := by
    simp only [ea1_eulerAX, hs4]
    norm_num
  have h128 : deltaX 4 4 4 4 4 4 = 128 := by norm_num [deltaX]
  have hsq : Real.sqrt 128 = 8 * Real.sqrt 2 := by
    rw [show (128:ℝ) = 64 * 2 by norm_num,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 64) 2,
      show (64:ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h40 : 2 * ea1_eulerAX 4 4 4 4 4 4 = 40 := by rw [h20]; norm_num
  have hsol : solEulerXDivSqrtdelta 4 4 4 4 4 4 = matan (2 / 25) / 20 := by
    have hs64 : Real.sqrt ((4:ℝ) * 4 * 4) = 8 := by
      rw [show (4:ℝ) * 4 * 4 = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    unfold solEulerXDivSqrtdelta
    norm_num [h128, hs64, hs4]
  rw [h40, h128, hsq, hsol, ea1_atn2_xpos (40 : ℝ) (8 * Real.sqrt 2) (by norm_num),
    ea1_matan_pos _ (by norm_num : (0:ℝ) < 2 / 25),
    show Real.sqrt (2 / 25) = Real.sqrt 2 / 5 from by
      rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2),
        show (25:ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
    show (8 * Real.sqrt 2) / 40 = Real.sqrt 2 / 5 from by ring]
  field_simp [show Real.sqrt 2 ≠ 0 from Real.sqrt_ne_zero'.mpr (by norm_num)]
  all_goals norm_num

end Kepler.Text
