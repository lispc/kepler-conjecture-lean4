/-
LocalAuto15: port of `scripts/local/VPWSHTO.hl` (Flyspeck "Local Fan"
chapter, module `Vpwshto`, H. L. Truong, 2012; 2925 lines, 0 defs +
28 theorems).  The file carries the pentagon-diagonal "short diagonal"
argument: a 5-cycle of unit edges (all five `norm(vv i - vv (i+1)) = 2`)
always has a vertex whose two pentagon diagonals are at most
`1 + sqrt 5`, first for straight-line configurations (`VPWSHTO1` via the
`MAX_IF_COPLANAR` fold / `TWO_DIAGONAL_AT_MOST` yardstick), then for
5-point packings in the ball annulus (`POINTS_IN_BALL_ANNULUS_*`,
`VPWSHTO_PRIME`), the annulus-side input to `VPWSHTO_concl`
(LocalAuto1, appendix.hl:62).

FILE MAP (source order)
  Section A: point-wise geometry: `NORM_COS_ANGLE_LT`, `MAX_COPLANAR_4POINT`,
    `SUM_4ANGLE_4POINT_EQ_2PI`, `EQ_DIAGONAL_MIN`, the explicit yardsticks
    `TWO_DIAGONAL_AT_MOST` / `TWO_DIAGONAL_AT_MOST1`, the fold existence
    lemmas `MAX_IF_COPLANAR` / `MAX_IF_COPLANAR1`, the straight-chain
    conclusions `VPWSHTO1` / `VPWSHTO200` / `VPWSHTO2`.
  Section B: the 12 mechanical index lemmas `MOD_ADD_*` (PROVED here).
  Section C: `VPWSHTO` (5-cycle, no minimality hypotheses) and the
    annulus chain `POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR{,2}`,
    `SUBSET_PACKING`, `VPWSHTO_PRIME`.

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `vec 0` <-> `0`; `norm` <-> `norm`;
    `dist` <-> `dist`; `min` <-> `min` (Real); `sqrt(&5)` <-> `Real.sqrt 5`;
    `&1 + sqrt(&5)` <-> `1 + Real.sqrt 5`; `pi` <-> `Real.pi`;
    `MOD` <-> `%`; HOL `i IN 0..4` <-> `i ∈ Set.Icc (0:ℕ) 4`.
    NO `native_decide` anywhere.
  - HOL `angle(u,v,w)` (Multivariate/geom.ml:506, flyspeck `angle_def`) <->
    `angle_p4` (importable LocalAuto4 copy of the same HOL def).
  - Segments: HOL `segment [u,w]` (bracket form, CLOSED segment) <->
    `segment ℝ u w`; HOL `segment(v,w)` (paren form = `open_segment`,
    `closed_segment DIFF {a,b}`, polytope1.ml:25 convention) <->
    `openSegment ℝ v w`.  (Polytope.lean:14 renders the paren form by the
    closed `segment ℝ a b`; here the two HOL forms are kept apart because
    BOTH occur, including in existential conclusions where the difference
    is not harmless.)  Both sides are documented for the merge wave.
  - HOL `packing s` <-> `Kepler.Packing (s : Set V3)` (Kepler.Statement);
    HOL `ball_annulus` <-> `ballAnnulus` (PackingAuto2, `h0 = 1.26`).
  - HOL `collinear {a,b,c}` <-> `Collinear ℝ ({a,b,c} : Set V3)`.
  - PROVED here: the 12 `MOD_ADD_*` index lemmas (`omega`), `SUBSET_PACKING`
    (one line from `Kepler.Packing`'s definition), and — relative to the
    sorried giants `POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR` and `VPWSHTO` —
    the permutation discharges `POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR2`
    (`Collinear.wbtw_or_wbtw_or_wbtw`) and `VPWSHTO_PRIME` (pure
    hypothesis juggling; the duplicated `~(vv 0 = vv 1)` conjunct is kept
    verbatim).  All other theorems keep `sorry` bodies: they are the
    chapter's contract registry (DISCHARGES convention — a later wave
    proves them and the `sorry` disappears).
  - Same-wave note: nothing here imports LocalAuto12-14/16-18 (owned by
    other lanes); every declaration carries the `_p15` suffix.

FILL LEDGER (proof-fill worker, this wave): `NORM_COS_ANGLE_LT_p15`
  was DISCHARGED (13 -> 12 sorries) by a self-contained law-of-cosines +
  `Real.strictAntiOn_arccos` proof (no external blocker existed; the other
  12 remain the chapter's contract registry — no proved blockers found in
  LocalAuto1-38 / PackingAuto1-25 / Fan / Geom for them).
  M1a root-w4 (2026-11-05): `POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15` was
  DISCHARGED (12 -> 11 sorries) by the segment variance (Stewart) identity:
  on `v = p•u + q•w` (`p,q ≥ 0`, `p+q = 1`) one has
  `‖v‖² = p‖u‖² + q‖w‖² - p q ‖u-w‖²`; the annulus caps `‖u‖²,‖w‖² ≤ (2h0)²`
  and packing forces `p‖u-w‖ ≥ 2`, `q‖u-w‖ ≥ 2`, so
  `‖v‖² ≤ (2h0)² - 4 = 2.3504 < 4 ≤ ‖v‖²`.

DISCHARGES (remaining `sorry`): `MAX_COPLANAR_4POINT_p15`,
  `SUM_4ANGLE_4POINT_EQ_2PI_p15`, `EQ_DIAGONAL_MIN_p15`,
  `TWO_DIAGONAL_AT_MOST_p15`, `MAX_IF_COPLANAR_p15`,
  `MAX_IF_COPLANAR1_p15`, `TWO_DIAGONAL_AT_MOST1_p15`, `VPWSHTO1_p15`,
  `VPWSHTO200_p15`, `VPWSHTO2_p15`, `VPWSHTO_p15`.
-/

import Kepler.Text.LocalAuto4
import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section A (source order): point-wise geometry, fold and chain lemmas -/

/-- HOL `NORM_COS_ANGLE_LT` (VPWSHTO.hl:29): equal legs, the longer base
carries the smaller angle. -/
theorem NORM_COS_ANGLE_LT_p15 : ∀ v v1 u u1 w w1 : V3,
    norm (v - w) = norm (v1 - w1) →
    norm (v - u) = norm (v1 - u1) →
    v ≠ u → v ≠ w → v1 ≠ w1 →
    (norm (u - w) < norm (u1 - w1) ↔ angle_p4 u v w < angle_p4 u1 v1 w1) := by
  intro v v1 u u1 w w1 hw hvu hvne hvwne hv1w1
  -- the two legs; equal-leg hypotheses and positivity
  have hA : ‖v - u‖ = ‖v1 - u1‖ := hvu
  have hB : ‖v - w‖ = ‖v1 - w1‖ := hw
  have hApos : 0 < ‖v - u‖ := by
    rw [← dist_eq_norm]
    exact dist_pos.mpr hvne
  have hBpos : 0 < ‖v - w‖ := by
    rw [← dist_eq_norm]
    exact dist_pos.mpr hvwne
  have hABpos : 0 < ‖v - u‖ * ‖v - w‖ := mul_pos hApos hBpos
  have hd0 : (‖v - u‖ * ‖v - w‖) ≠ 0 := ne_of_gt hABpos
  have hden : ‖u - v‖ * ‖w - v‖ = ‖v - u‖ * ‖v - w‖ := by
    rw [norm_sub_rev (a := u) (b := v), norm_sub_rev (a := w) (b := v)]
  have hden1 : ‖u1 - v1‖ * ‖w1 - v1‖ = ‖v - u‖ * ‖v - w‖ := by
    rw [hA, hB, norm_sub_rev (a := v1) (b := u1), norm_sub_rev (a := v1) (b := w1)]
  have hpos : 0 < ‖u - v‖ * ‖w - v‖ := by rw [hden]; exact hABpos
  have hpos1 : 0 < ‖u1 - v1‖ * ‖w1 - v1‖ := by rw [hden1]; exact hABpos
  -- law of cosines for both bases
  have e1 : ‖u - w‖ ^ 2
      = ‖v - u‖ ^ 2 - 2 * inner ℝ (u - v) (w - v) + ‖v - w‖ ^ 2 := by
    have h4 : (u - v) - (w - v) = u - w := by simp [sub_sub_sub_comm]
    have h5 := real_inner_sub_sub_self (x := u - v) (y := w - v)
    rw [h4] at h5
    simp only [real_inner_self_eq_norm_sq] at h5
    rw [norm_sub_rev (a := u) (b := v), norm_sub_rev (a := w) (b := v)] at h5
    exact h5
  have e2 : ‖u1 - w1‖ ^ 2
      = ‖v - u‖ ^ 2 - 2 * inner ℝ (u1 - v1) (w1 - v1) + ‖v - w‖ ^ 2 := by
    have h4 : (u1 - v1) - (w1 - v1) = u1 - w1 := by simp [sub_sub_sub_comm]
    have h5 := real_inner_sub_sub_self (x := u1 - v1) (y := w1 - v1)
    rw [h4] at h5
    simp only [real_inner_self_eq_norm_sq] at h5
    rw [norm_sub_rev (a := u1) (b := v1), norm_sub_rev (a := w1) (b := v1),
      ← hA, ← hB] at h5
    exact h5
  -- division by the (common, positive) leg product is order-reflecting
  have hdivlt : ∀ a b : ℝ,
      a / (‖v - u‖ * ‖v - w‖) < b / (‖v - u‖ * ‖v - w‖) ↔ a < b := by
    intro a b
    constructor
    · intro h
      have h2 := (div_lt_iff₀ hABpos).mp h
      rwa [div_mul_cancel₀ _ hd0] at h2
    · intro h
      rw [div_lt_iff₀ hABpos, div_mul_cancel₀ _ hd0]
      exact h
  have hdivle : ∀ a b : ℝ,
      a / (‖v - u‖ * ‖v - w‖) ≤ b / (‖v - u‖ * ‖v - w‖) ↔ a ≤ b := by
    intro a b
    constructor
    · intro h
      have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hABpos)
      simpa only [div_mul_cancel₀ _ hd0] using h2
    · intro h
      rw [div_le_iff₀ hABpos, div_mul_cancel₀ _ hd0]
      exact h
  -- reduce the norm comparison to the inner-product (cosine) comparison
  have hsqlt : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a < b ↔ a ^ 2 < b ^ 2) := by
    intro a b ha hb
    constructor
    · intro h
      have hbp : 0 < b - a := sub_pos.mpr h
      have h1 : a ^ 2 ≤ a * b := by nlinarith [mul_nonneg ha (le_of_lt hbp)]
      have h2 : a * b < b * b := by
        have hb2 : 0 < b := lt_of_le_of_lt ha h
        have h3 : 0 < b * (b - a) := mul_pos hb2 hbp
        have h4 : b * b - a * b = b * (b - a) := by ring
        linarith
      linarith
    · intro h
      by_contra hge
      push_neg at hge
      have hbp : 0 ≤ a - b := by linarith
      have h1 : b * b ≤ a * b := by nlinarith [mul_nonneg hb hbp]
      have h2 : a * b ≤ a * a := by nlinarith [mul_nonneg ha hbp]
      have h3 : b ^ 2 ≤ a ^ 2 := by nlinarith
      linarith
  have hsq : ‖u - w‖ < ‖u1 - w1‖ ↔
      inner ℝ (u1 - v1) (w1 - v1) < inner ℝ (u - v) (w - v) := by
    have hnn1 : 0 ≤ ‖u - w‖ := norm_nonneg _
    have hnn2 : 0 ≤ ‖u1 - w1‖ := norm_nonneg _
    constructor
    · intro h
      have h2 := (hsqlt _ _ hnn1 hnn2).mp h
      rw [e1, e2] at h2
      linarith
    · intro h
      have h2 : (‖v - u‖) ^ 2 - 2 * inner ℝ (u - v) (w - v) + (‖v - w‖) ^ 2
          < (‖v - u‖) ^ 2 - 2 * inner ℝ (u1 - v1) (w1 - v1) + (‖v - w‖) ^ 2 := by
        linarith
      rw [← e1, ← e2] at h2
      exact (hsqlt _ _ hnn1 hnn2).mpr h2
  -- the two cosines lie in [-1, 1]
  have hcub : -1 ≤ inner ℝ (u - v) (w - v) / (‖u - v‖ * ‖w - v‖)
      ∧ inner ℝ (u - v) (w - v) / (‖u - v‖ * ‖w - v‖) ≤ 1 := by
    have hb := abs_le.mp (abs_real_inner_le_norm (x := u - v) (y := w - v))
    rw [hden] at hb
    constructor
    · rw [le_div_iff₀ hpos, neg_one_mul]; linarith
    · rw [div_le_iff₀ hpos, one_mul]; linarith
  have hdub : -1 ≤ inner ℝ (u1 - v1) (w1 - v1) / (‖u1 - v1‖ * ‖w1 - v1‖)
      ∧ inner ℝ (u1 - v1) (w1 - v1) / (‖u1 - v1‖ * ‖w1 - v1‖) ≤ 1 := by
    have hb := abs_le.mp (abs_real_inner_le_norm (x := u1 - v1) (y := w1 - v1))
    rw [hden1] at hb
    constructor
    · rw [le_div_iff₀ hpos1, neg_one_mul]; linarith
    · rw [div_le_iff₀ hpos1, one_mul]; linarith
  constructor
  · intro h
    have hcos : inner ℝ (u1 - v1) (w1 - v1) < inner ℝ (u - v) (w - v) :=
      hsq.mp h
    have harg : inner ℝ (u1 - v1) (w1 - v1) / (‖u1 - v1‖ * ‖w1 - v1‖)
        < inner ℝ (u - v) (w - v) / (‖u - v‖ * ‖w - v‖) := by
      rw [hden1, hden]
      exact (hdivlt _ _).mpr hcos
    exact Real.strictAntiOn_arccos hdub hcub harg
  · intro harc
    have hcos : inner ℝ (u1 - v1) (w1 - v1) < inner ℝ (u - v) (w - v) := by
      by_contra hge
      push_neg at hge
      have hdc : inner ℝ (u - v) (w - v) / (‖u - v‖ * ‖w - v‖)
          ≤ inner ℝ (u1 - v1) (w1 - v1) / (‖u1 - v1‖ * ‖w1 - v1‖) := by
        rw [hden1, hden]
        exact (hdivle _ _).mpr hge
      exact absurd harc (not_lt.mpr (Real.antitone_arccos hdc))
    exact hsq.mpr hcos

/-- HOL `MAX_COPLANAR_4POINT` (VPWSHTO.hl:47): reflected `w1` keeps the
diagonal minimum. -/
theorem MAX_COPLANAR_4POINT_p15 : ∀ (v x u w w1 y : V3) (a t : ℝ),
    v ≠ x → v ≠ u → v ≠ w → x ≠ u → x ≠ w → u ≠ w →
    v ≠ w1 → x ≠ w1 → u ≠ w1 →
    norm (v - x) = t → norm (v - u) = a → norm (x - w) = a → norm (u - w) = a →
    y ∈ openSegment ℝ v w ∩ openSegment ℝ x u →
    norm (x - w1) = a → norm (u - w1) = a →
    min (norm (v - w1)) (norm (x - u)) ≤ min (norm (v - w)) (norm (x - u)) := by
  sorry

/-- HOL `SUM_4ANGLE_4POINT_EQ_2PI` (VPWSHTO.hl:111): the four angles around
the crossing of the two diagonals sum to `2π`. -/
theorem SUM_4ANGLE_4POINT_EQ_2PI_p15 : ∀ v x u w y : V3,
    v ≠ x → v ≠ u → v ≠ w → x ≠ u → x ≠ w → u ≠ w →
    y ∈ openSegment ℝ v w ∩ openSegment ℝ x u →
    angle_p4 x v u + angle_p4 v u w + angle_p4 u w x + angle_p4 w x v
      = 2 * Real.pi := by
  sorry

/-- HOL `EQ_DIAGONAL_MIN` (VPWSHTO.hl:171): if the second diagonal pair is
strictly larger the four-angle sum cannot stay `2π`; hence the bound. -/
theorem EQ_DIAGONAL_MIN_p15 : ∀ (v v1 x x1 u w u1 w1 y y1 : V3) (a t : ℝ),
    v ≠ x → v ≠ u → v ≠ w → x ≠ u → x ≠ w → u ≠ w →
    v1 ≠ x1 → v1 ≠ u1 → v1 ≠ w1 → x1 ≠ u1 → x1 ≠ w1 → u1 ≠ w1 →
    norm (v - x) = t → norm (v - u) = a → norm (x - w) = a → norm (u - w) = a →
    y ∈ openSegment ℝ v w ∩ openSegment ℝ x u →
    norm (v - w) = norm (x - u) →
    norm (v1 - x1) = t → norm (v1 - u1) = a → norm (x1 - w1) = a →
    norm (u1 - w1) = a →
    y1 ∈ openSegment ℝ v1 w1 ∩ openSegment ℝ x1 u1 →
    min (norm (v1 - w1)) (norm (x1 - u1)) ≤ norm (x - u) := by
  sorry

/-- HOL `TWO_DIAGONAL_AT_MOST` (VPWSHTO.hl:228): explicit rhombus yardstick
for `2 ≤ t ≤ 4`. -/
theorem TWO_DIAGONAL_AT_MOST_p15 : ∀ t : ℝ, 2 ≤ t → t ≤ 4 →
    ∃ u w v x y : V3,
      v ≠ x ∧ v ≠ u ∧ v ≠ w ∧ x ≠ u ∧ x ≠ w ∧ u ≠ w ∧
      norm (v - x) = t ∧ norm (v - u) = 2 ∧ norm (x - w) = 2 ∧ norm (u - w) = 2 ∧
      y ∈ openSegment ℝ v w ∩ openSegment ℝ x u ∧
      norm (v - w) = norm (x - u) ∧
      (t ≤ norm (v - w) → norm (v - w) ≤ 1 + Real.sqrt 5 ∧ t ≤ 1 + Real.sqrt 5) := by
  sorry

/-- HOL `MAX_IF_COPLANAR` (VPWSHTO.hl:388): the `MAX_COPLANAR_4POINT` fold
input exists — a reflected cap `w1` with `y` on both open segments. -/
theorem MAX_IF_COPLANAR_p15 : ∀ (v x u w : V3) (a t : ℝ),
    a ≤ t →
    v ≠ x → v ≠ u → v ≠ w → x ≠ u → x ≠ w → u ≠ w →
    ¬Collinear ℝ ({v, x, u} : Set V3) → ¬Collinear ℝ ({w, x, u} : Set V3) →
    norm (v - x) = t → norm (v - u) = a → norm (x - w) = a → norm (u - w) = a →
    t ≤ norm (x - u) →
    ∃ w1 y : V3,
      y ∈ openSegment ℝ v w1 ∩ openSegment ℝ x u ∧
      norm (x - w1) = a ∧ norm (u - w1) = a ∧ v ≠ w1 := by
  sorry

/-- HOL `MAX_IF_COPLANAR1` (VPWSHTO.hl:957): `MAX_IF_COPLANAR` specialized
to `a2 = t` (the leg equals the tip distance). -/
theorem MAX_IF_COPLANAR1_p15 : ∀ (v x u w : V3) (a a2 t : ℝ),
    a ≤ t →
    v ≠ x → v ≠ u → v ≠ w → x ≠ u → x ≠ w → u ≠ w →
    ¬Collinear ℝ ({v, x, u} : Set V3) → ¬Collinear ℝ ({w, x, u} : Set V3) →
    norm (v - x) = t → norm (v - u) = a → norm (x - w) = a2 → norm (u - w) = a2 →
    a2 = t → t ≤ norm (x - u) →
    ∃ w1 y : V3,
      y ∈ openSegment ℝ v w1 ∩ openSegment ℝ x u ∧
      norm (x - w1) = a2 ∧ norm (u - w1) = a2 ∧ v ≠ w1 := by
  sorry

/-- HOL `TWO_DIAGONAL_AT_MOST1` (VPWSHTO.hl:1535): the yardstick for
`0 < t ≤ 2`. -/
theorem TWO_DIAGONAL_AT_MOST1_p15 : ∀ t : ℝ, t ≤ 2 → 0 < t →
    ∃ u w v x y : V3,
      v ≠ x ∧ v ≠ u ∧ v ≠ w ∧ x ≠ u ∧ x ≠ w ∧ u ≠ w ∧
      norm (v - x) = t ∧ norm (v - u) = 2 ∧ norm (x - w) = 2 ∧ norm (u - w) = 2 ∧
      y ∈ openSegment ℝ v w ∩ openSegment ℝ x u ∧
      norm (v - w) = norm (x - u) ∧
      (t ≤ norm (v - w) → norm (v - w) ≤ 1 + Real.sqrt 5 ∧ t ≤ 1 + Real.sqrt 5) := by
  sorry

/-- HOL `VPWSHTO1` (VPWSHTO.hl:1698): straight-chain conclusion. -/
theorem VPWSHTO1_p15 : ∀ (v x u w : V3) (t : ℝ),
    t ≤ 4 →
    ¬Collinear ℝ ({v, x, u} : Set V3) → ¬Collinear ℝ ({w, x, u} : Set V3) →
    v ≠ w →
    norm (v - x) = t → norm (v - u) = 2 → norm (x - w) = 2 → norm (u - w) = 2 →
    t ≤ norm (x - u) → t ≤ norm (v - w) →
    min (norm (v - w)) (norm (x - u)) ≤ 1 + Real.sqrt 5 ∧
      t ≤ 1 + Real.sqrt 5 := by
  sorry

/-- HOL `VPWSHTO200` (VPWSHTO.hl:1810): full 5-point straight version with a
minimality (closest-pair) hypothesis. -/
theorem VPWSHTO200_p15 : ∀ v x u w w1 : V3,
    ¬Collinear ℝ ({v, x, u} : Set V3) → ¬Collinear ℝ ({w, x, u} : Set V3) →
    ¬Collinear ℝ ({w1, x, u} : Set V3) → ¬Collinear ℝ ({w, v, u} : Set V3) →
    ¬Collinear ℝ ({w1, v, u} : Set V3) → ¬Collinear ℝ ({w1, w, u} : Set V3) →
    ¬Collinear ℝ ({w, v, x} : Set V3) → ¬Collinear ℝ ({w1, v, x} : Set V3) →
    ¬Collinear ℝ ({w1, w, x} : Set V3) → ¬Collinear ℝ ({w1, w, v} : Set V3) →
    norm (v - x) = 2 → norm (x - u) = 2 → norm (u - w) = 2 →
    norm (w - w1) = 2 → norm (w1 - v) = 2 →
    norm (v - u) ≤ norm (v - w) → norm (v - u) ≤ norm (u - w1) →
    norm (v - u) ≤ norm (w1 - x) → norm (v - u) ≤ norm (x - w) →
    ∃ w2 : V3,
      w2 ∈ ({v, x, u, w, w1} : Set V3) ∧ x ≠ w2 ∧
      norm (v - u) ≤ 1 + Real.sqrt 5 ∧
      ((w1 ≠ w2 ∧ norm (v - w2) ≤ 1 + Real.sqrt 5) ∨
        (w ≠ w2 ∧ norm (u - w2) ≤ 1 + Real.sqrt 5)) := by
  sorry

/-- HOL `VPWSHTO2` (VPWSHTO.hl:1864): indexed 5-cycle version with the four
closest-diagonal hypotheses. -/
theorem VPWSHTO2_p15 : ∀ vv : ℕ → V3,
    ¬Collinear ℝ ({vv 0, vv 1, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 3, vv 1, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 1, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 3, vv 0, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 0, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 3, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 3, vv 0, vv 1} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 0, vv 1} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 3, vv 1} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 3, vv 0} : Set V3) →
    norm (vv 0 - vv 1) = 2 → norm (vv 1 - vv 2) = 2 → norm (vv 2 - vv 3) = 2 →
    norm (vv 3 - vv 4) = 2 → norm (vv 4 - vv 0) = 2 →
    norm (vv 0 - vv 2) ≤ norm (vv 0 - vv 3) →
    norm (vv 0 - vv 2) ≤ norm (vv 2 - vv 4) →
    norm (vv 0 - vv 2) ≤ norm (vv 4 - vv 1) →
    norm (vv 0 - vv 2) ≤ norm (vv 1 - vv 3) →
    ∃ i : ℕ, i ∈ Set.Icc (0 : ℕ) 4 ∧
      norm (vv i - vv ((i + 2) % 5)) ≤ 1 + Real.sqrt 5 ∧
      norm (vv i - vv ((i + 3) % 5)) ≤ 1 + Real.sqrt 5 := by
  sorry

/-! ## Section B (PROVED): the `MOD_ADD_*` index lemmas -/

/-- HOL `MOD_ADD_235` (VPWSHTO.hl:1919). -/
theorem MOD_ADD_235_p15 (i : ℕ) : ((i + 2) % 5 + 3) % 5 = i % 5 := by omega

/-- HOL `MOD_ADD_325` (VPWSHTO.hl:1924). -/
theorem MOD_ADD_325_p15 (i : ℕ) : ((i + 3) % 5 + 2) % 5 = i % 5 := by omega

/-- HOL `MOD_ADD_225` (VPWSHTO.hl:1928). -/
theorem MOD_ADD_225_p15 (i : ℕ) : ((i + 2) % 5 + 2) % 5 = (i + 4) % 5 := by omega

/-- HOL `MOD_ADD_335` (VPWSHTO.hl:1932). -/
theorem MOD_ADD_335_p15 (i : ℕ) : ((i + 3) % 5 + 3) % 5 = (i + 1) % 5 := by omega

/-- HOL `MOD_ADD_345` (VPWSHTO.hl:1937). -/
theorem MOD_ADD_345_p15 (i : ℕ) : ((i + 3) % 5 + 4) % 5 = (i + 2) % 5 := by omega

/-- HOL `MOD_ADD_245` (VPWSHTO.hl:1941). -/
theorem MOD_ADD_245_p15 (i : ℕ) : ((i + 2) % 5 + 4) % 5 = (i + 1) % 5 := by omega

/-- HOL `MOD_ADD_425` (VPWSHTO.hl:1945). -/
theorem MOD_ADD_425_p15 (i : ℕ) : ((i + 4) % 5 + 2) % 5 = (i + 1) % 5 := by omega

/-- HOL `MOD_ADD_435` (VPWSHTO.hl:1949). -/
theorem MOD_ADD_435_p15 (i : ℕ) : ((i + 4) % 5 + 3) % 5 = (i + 2) % 5 := by omega

/-- HOL `MOD_ADD_215` (VPWSHTO.hl:1962). -/
theorem MOD_ADD_215_p15 (i : ℕ) : ((i + 2) % 5 + 1) % 5 = (i + 3) % 5 := by omega

/-- HOL `MOD_ADD_125` (VPWSHTO.hl:1966). -/
theorem MOD_ADD_125_p15 (i : ℕ) : ((i + 1) % 5 + 2) % 5 = (i + 3) % 5 := by omega

/-- HOL `MOD_ADD_135` (VPWSHTO.hl:1970). -/
theorem MOD_ADD_135_p15 (i : ℕ) : ((i + 1) % 5 + 3) % 5 = (i + 4) % 5 := by omega

/-- HOL `MOD_ADD_315` (VPWSHTO.hl:1974). -/
theorem MOD_ADD_315_p15 (i : ℕ) : ((i + 3) % 5 + 1) % 5 = (i + 4) % 5 := by omega

/-! ## Section C: the 5-cycle conclusion and the ball-annulus chain -/

/-! ### Lane `vpwshto-w1` kit (PROVED 2026-11-12): direct proof of `VPWSHTO`

The HOL chain `VPWSHTO1` (VPWSHTO.hl:1698) → `VPWSHTO2` (:1864) → `VPWSHTO`
(:1978) is replaced by a self-contained analytic route that consumes no
sorried declaration of this file.

Analytic core (`p15w_chain4`): for `P Q R : V3` with `‖P‖ = ‖Q‖ = ‖R‖ = 2`,
`S = P + Q`, `τ = 1 + √5 ≤ ‖S‖` and `‖S - R‖ ≤ ‖S‖`, one has `‖R - Q‖ ≤ τ`.
Proof: `⟪S, R⟫ ≥ 2` and `⟪S, Q⟫ = ‖S‖²/2` follow from the two distance
constraints; splitting `R`, `Q` into components parallel/perpendicular to `S`
gives `⟪R, Q⟫ = ⟪S, R⟫/2 + ⟪R⊥, Q⊥⟫`, `‖R⊥‖² = 4 - ⟪S, R⟫²/‖S‖²`,
`‖Q⊥‖² = 4 - ‖S‖²/4`, and Cauchy–Schwarz bounds `⟪R⊥, Q⊥⟫ ≥ -‖R⊥‖‖Q⊥‖`; with
`z = ‖S‖² ≥ τ²` the golden-ratio identity
`z² - 12 z + 16 = (z - τ²) (z - (6 - 2√5)) ≥ 0` yields `‖R - Q‖² ≤ τ²`.
Sharp at the regular pentagon (all five diagonals `= τ`).

`p15w_yard` is the `VPWSHTO1` four-point conclusion from the same data
(case split on `‖v - w‖ ≤ τ`).  `p15w_vpwshto2` is the minimal-diagonal
`VPWSHTO2` step at an arbitrary minimal index `k` (the HOL five-fold
`MOD_ADD_*` rotation collapses into `omega` index arithmetic), and
`VPWSHTO_p15` picks a minimal diagonal among the five and applies it. -/

/-- Bundled side lengths of the 5-cycle: `‖vv j - vv (j+1)‖ = 2` for all
`j < 5` (indices modulo 5). -/
private theorem p15w_sides (vv : ℕ → V3)
    (hs01 : ‖vv 0 - vv 1‖ = 2) (hs12 : ‖vv 1 - vv 2‖ = 2)
    (hs23 : ‖vv 2 - vv 3‖ = 2) (hs34 : ‖vv 3 - vv 4‖ = 2)
    (hs40 : ‖vv 4 - vv 0‖ = 2) :
    ∀ j : ℕ, j < 5 → ‖vv j - vv ((j + 1) % 5)‖ = 2 := by
  intro j hj
  interval_cases j
  · have h : (0 + 1) % 5 = 1 := by norm_num
    rw [h]; exact hs01
  · have h : (1 + 1) % 5 = 2 := by norm_num
    rw [h]; exact hs12
  · have h : (2 + 1) % 5 = 3 := by norm_num
    rw [h]; exact hs23
  · have h : (3 + 1) % 5 = 4 := by norm_num
    rw [h]; exact hs34
  · have h : (4 + 1) % 5 = 0 := by norm_num
    rw [h]; exact hs40

/-- Core four-point yardstick (see the section note): `P, Q, R` are the three
links of an open chain of length `2`; if `S = P + Q` has `‖S‖ ≥ 1 + √5` and
the end-to-end vector `S - R` is no longer than `S`, then the other
"diagonal" `‖R - Q‖` stays below `1 + √5`. -/
private theorem p15w_chain4 (P Q R : V3)
    (hP : ‖P‖ = 2) (hQ : ‖Q‖ = 2) (hR : ‖R‖ = 2)
    (hb : 1 + Real.sqrt 5 ≤ ‖P + Q‖)
    (hmin : ‖P + Q - R‖ ≤ ‖P + Q‖) :
    ‖R - Q‖ ≤ 1 + Real.sqrt 5 := by
  have hSpos : 0 < ‖P + Q‖ := lt_of_lt_of_le (by positivity) hb
  -- (1) `2 ≤ ⟪P + Q, R⟫` from `‖P + Q - R‖ ≤ ‖P + Q‖`
  have hSR : (2 : ℝ) ≤ inner ℝ (P + Q) R := by
    have hsq : ‖(P + Q) - R‖ ^ 2 ≤ ‖P + Q‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hmin 2
    rw [norm_sub_sq_real, hR] at hsq
    linarith
  -- (2) `⟪P + Q, Q⟫ = ‖P + Q‖² / 2` from `‖(P+Q) - Q‖ = ‖P‖ = 2 = ‖Q‖`
  have hPQ : (P + Q) - Q = P := by abel
  have hSQ : inner ℝ (P + Q) Q = ‖P + Q‖ ^ 2 / 2 := by
    have hsq2 : ‖(P + Q) - Q‖ ^ 2 = ‖Q‖ ^ 2 := by rw [hPQ, hP, hQ]
    rw [norm_sub_sq_real] at hsq2
    linarith
  -- perpendicular decomposition of `R`, `Q` around `S := P + Q`
  set S : V3 := P + Q with hSdef
  set b2 : ℝ := ‖S‖ ^ 2 with hb2def
  have hb2pos : 0 < b2 := by rw [hb2def]; exact pow_pos hSpos 2
  have hb2ne : b2 ≠ 0 := ne_of_gt hb2pos
  set u : ℝ := inner ℝ S R with hudef
  set v : ℝ := inner ℝ S Q with hvdef
  set Rp : V3 := R - (u / b2) • S with hRpdef
  set Qp : V3 := Q - (v / b2) • S with hQpdef
  have hSS : inner ℝ S S = b2 := by rw [hb2def, real_inner_self_eq_norm_sq]
  have hRS : inner ℝ R S = u := by rw [hudef, real_inner_comm]
  have hQS : inner ℝ Q S = v := by rw [hvdef, real_inner_comm]
  have hu2 : (2 : ℝ) ≤ u := hSR
  have hv2 : v = b2 / 2 := by
    show inner ℝ S Q = b2 / 2
    rw [hSdef, hb2def]
    exact hSQ
  -- (3) `⟪R, Q⟫ = u * v / b2 + ⟪R⊥, Q⊥⟫`
  have hkey : inner ℝ R Q = u * v / b2 + inner ℝ Rp Qp := by
    rw [hRpdef, hQpdef]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hSS, hRS]
    field_simp
    ring
  -- (4) norms of the perpendicular parts
  have hRp_sq : ‖Rp‖ ^ 2 = 4 - u ^ 2 / b2 := by
    rw [hRpdef, norm_sub_sq_real, hR, real_inner_smul_right, hRS]
    have hnorm : ‖(u / b2) • S‖ ^ 2 = (u / b2) ^ 2 * b2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hb2def]
    rw [hnorm]
    field_simp
    ring
  have hQp_sq : ‖Qp‖ ^ 2 = 4 - b2 / 4 := by
    rw [hQpdef, norm_sub_sq_real, hQ, real_inner_smul_right, hQS]
    have hnorm : ‖(v / b2) • S‖ ^ 2 = (v / b2) ^ 2 * b2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hb2def]
    rw [hnorm, hv2]
    field_simp
    ring
  -- (5) Cauchy–Schwarz on the perpendicular parts
  have hcs : -(‖Rp‖ * ‖Qp‖) ≤ inner ℝ Rp Qp := by
    have h := abs_real_inner_le_norm Rp Qp
    have h2 : -|inner ℝ Rp Qp| ≤ inner ℝ Rp Qp := neg_abs_le _
    linarith
  have hRp_le : ‖Rp‖ ≤ Real.sqrt (4 - 4 / b2) := by
    rw [show ‖Rp‖ = Real.sqrt (‖Rp‖ ^ 2) from (Real.sqrt_sq (norm_nonneg Rp)).symm]
    rw [hRp_sq]
    apply Real.sqrt_le_sqrt
    have hu4 : (4 : ℝ) ≤ u ^ 2 := by nlinarith
    have hdiff : 0 ≤ (u ^ 2 - 4) / b2 := div_nonneg (by linarith) (le_of_lt hb2pos)
    have heq : u ^ 2 / b2 - 4 / b2 = (u ^ 2 - 4) / b2 := by ring
    linarith
  have hQp_le : ‖Qp‖ ≤ Real.sqrt (4 - b2 / 4) := by
    rw [show ‖Qp‖ = Real.sqrt (‖Qp‖ ^ 2) from (Real.sqrt_sq (norm_nonneg Qp)).symm,
      hQp_sq]
  have hprod : ‖Rp‖ * ‖Qp‖ ≤ Real.sqrt (4 - 4 / b2) * Real.sqrt (4 - b2 / 4) :=
    mul_le_mul hRp_le hQp_le (norm_nonneg Qp) (Real.sqrt_nonneg _)
  -- (6) lower bound for `⟪R, Q⟫`
  have hinner_lb :
      1 - Real.sqrt (4 - 4 / b2) * Real.sqrt (4 - b2 / 4) ≤ inner ℝ R Q := by
    have huv : u * v / b2 = u / 2 := by
      rw [hv2]
      field_simp
    rw [hkey, huv]
    linarith
  -- (7) golden-ratio arithmetic: `‖R - Q‖² ≤ τ²`
  have hns : ‖R - Q‖ ^ 2 = 8 - 2 * inner ℝ R Q := by
    rw [norm_sub_sq_real, hR, hQ]; ring
  have ha2 :
      ‖R - Q‖ ^ 2 ≤ 6 + 2 * (Real.sqrt (4 - 4 / b2) * Real.sqrt (4 - b2 / 4)) := by
    rw [hns]; linarith
  have hS_le : ‖S‖ ≤ 4 := by
    rw [hSdef]
    calc ‖P + Q‖ ≤ ‖P‖ + ‖Q‖ := norm_add_le _ _
      _ = 4 := by rw [hP, hQ]; norm_num
  have hb2_le : b2 ≤ 16 := by
    rw [hb2def]; nlinarith [norm_nonneg S]
  have hb2_ge1 : 1 ≤ b2 := by
    have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith [hb2def, hS_le]
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have htau2 : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by nlinarith
  have hz_ge : 6 + 2 * Real.sqrt 5 ≤ b2 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + Real.sqrt 5 by positivity) hb 2
    rw [hb2def]
    rwa [htau2] at h
  have hpoly : 0 ≤ b2 ^ 2 - 12 * b2 + 16 := by
    have hfac :
        b2 ^ 2 - 12 * b2 + 16 =
          (b2 - (6 + 2 * Real.sqrt 5)) * (b2 - (6 - 2 * Real.sqrt 5)) := by
      nlinarith [hsqrt5_sq]
    rw [hfac]
    apply mul_nonneg
    · linarith
    · linarith [Real.sqrt_nonneg 5]
  have hD_le : (4 - 4 / b2) * (4 - b2 / 4) ≤ 5 := by
    have hident : (4 - 4 / b2) * (4 - b2 / 4) = (17 * b2 - b2 ^ 2 - 16) / b2 := by
      field_simp
      ring
    rw [hident, div_le_iff₀ hb2pos]
    nlinarith
  have hA_nn : 0 ≤ 4 - 4 / b2 := by
    have h : 4 / b2 ≤ 4 := by rw [div_le_iff₀ hb2pos]; nlinarith
    linarith
  have hB_nn : 0 ≤ 4 - b2 / 4 := by
    have h : b2 / 4 ≤ 4 := by rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]; linarith
    linarith
  have hP_le : Real.sqrt (4 - 4 / b2) * Real.sqrt (4 - b2 / 4) ≤ Real.sqrt 5 := by
    have hP2 : (Real.sqrt (4 - 4 / b2) * Real.sqrt (4 - b2 / 4)) ^ 2 ≤ 5 := by
      rw [mul_pow, Real.sq_sqrt hA_nn, Real.sq_sqrt hB_nn]
      exact hD_le
    exact Real.le_sqrt_of_sq_le hP2
  have hfinal : ‖R - Q‖ ^ 2 ≤ (1 + Real.sqrt 5) ^ 2 := by
    rw [htau2]
    linarith
  have htarget : ‖R - Q‖ ≤ Real.sqrt ((1 + Real.sqrt 5) ^ 2) :=
    Real.le_sqrt_of_sq_le hfinal
  rwa [Real.sqrt_sq (by positivity)] at htarget

/-- `VPWSHTO1` (VPWSHTO.hl:1698): four-point folded-chain yardstick.  The
HOL hypotheses `t ≤ 4` and `v ≠ w` and both non-collinearity assumptions are
not needed by the analytic proof and are dropped here. -/
private theorem p15w_yard (v x u w : V3) (t : ℝ)
    (hvx : ‖v - x‖ = t)
    (hvu : ‖v - u‖ = 2) (hxw : ‖x - w‖ = 2) (huw : ‖u - w‖ = 2)
    (hta : t ≤ ‖x - u‖) (htb : t ≤ ‖v - w‖) :
    min (‖v - w‖) (‖x - u‖) ≤ 1 + Real.sqrt 5 ∧ t ≤ 1 + Real.sqrt 5 := by
  have hP : ‖v - u‖ = 2 := hvu
  have hQ : ‖u - w‖ = 2 := huw
  have hR : ‖x - w‖ = 2 := hxw
  have hS : (v - u) + (u - w) = v - w := by abel
  have hSR : (v - u) + (u - w) - (x - w) = v - x := by abel
  have hRQ : (x - w) - (u - w) = x - u := by abel
  have ht1 : ‖(v - u) + (u - w) - (x - w)‖ ≤ ‖(v - u) + (u - w)‖ := by
    rw [hSR, hvx, hS]
    exact htb
  have ht2 : t ≤ ‖(x - w) - (u - w)‖ := by
    rw [hRQ]
    exact hta
  by_cases hb : ‖(v - u) + (u - w)‖ ≤ 1 + Real.sqrt 5
  · have hbw : ‖v - w‖ ≤ 1 + Real.sqrt 5 := by rwa [hS] at hb
    exact ⟨le_trans (min_le_left _ _) hbw, le_trans htb hbw⟩
  · have hb' : 1 + Real.sqrt 5 ≤ ‖(v - u) + (u - w)‖ := le_of_lt (lt_of_not_ge hb)
    have hchain := p15w_chain4 (v - u) (u - w) (x - w) hP hQ hR hb' ht1
    have hmin' : ‖x - u‖ ≤ 1 + Real.sqrt 5 := by
      rw [← hRQ]
      exact hchain
    exact ⟨le_trans (min_le_right _ _) hmin', le_trans ht2 hchain⟩

/-- `VPWSHTO2` (VPWSHTO.hl:1864) at an arbitrary minimal diagonal index `k`:
the minimal diagonal is `d k = ‖vv k - vv ((k+2) % 5)‖`, and the other four
diagonals are `≥ d k`. -/
private theorem p15w_vpwshto2 (vv : ℕ → V3) (k : ℕ) (hk : k < 5)
    (hs : ∀ j : ℕ, j < 5 → ‖vv j - vv ((j + 1) % 5)‖ = 2)
    (hmin : ∀ j : ℕ, j < 5 → ‖vv k - vv ((k + 2) % 5)‖ ≤ ‖vv j - vv ((j + 2) % 5)‖) :
    ∃ i : ℕ, i ∈ Set.Icc (0 : ℕ) 4 ∧
      ‖vv i - vv ((i + 2) % 5)‖ ≤ 1 + Real.sqrt 5 ∧
      ‖vv i - vv ((i + 3) % 5)‖ ≤ 1 + Real.sqrt 5 := by
  have hk2 : (k + 2) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hk3 : (k + 3) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hk4 : (k + 4) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  -- distance data for the four-point yardstick
  have hvu : ‖vv k - vv ((k + 4) % 5)‖ = 2 := by
    have hidx : (((k + 4) % 5 + 1) % 5) = k % 5 := by omega
    have h := hs ((k + 4) % 5) hk4
    rw [hidx, Nat.mod_eq_of_lt hk] at h
    rwa [norm_sub_rev] at h
  have hxw : ‖vv ((k + 2) % 5) - vv ((k + 3) % 5)‖ = 2 := by
    have hidx : (((k + 2) % 5 + 1) % 5) = (k + 3) % 5 := by omega
    have h := hs ((k + 2) % 5) hk2
    rwa [hidx] at h
  have huw : ‖vv ((k + 4) % 5) - vv ((k + 3) % 5)‖ = 2 := by
    have hidx : (((k + 3) % 5 + 1) % 5) = (k + 4) % 5 := by omega
    have h := hs ((k + 3) % 5) hk3
    rw [hidx] at h
    rwa [norm_sub_rev] at h
  have hta : ‖vv k - vv ((k + 2) % 5)‖ ≤ ‖vv ((k + 2) % 5) - vv ((k + 4) % 5)‖ := by
    have hidx : (((k + 2) % 5 + 2) % 5) = (k + 4) % 5 := by omega
    have h := hmin ((k + 2) % 5) hk2
    rwa [hidx] at h
  have htb : ‖vv k - vv ((k + 2) % 5)‖ ≤ ‖vv k - vv ((k + 3) % 5)‖ := by
    have hidx : (((k + 3) % 5 + 2) % 5) = k % 5 := by omega
    have h := hmin ((k + 3) % 5) hk3
    rw [hidx, Nat.mod_eq_of_lt hk] at h
    rwa [norm_sub_rev (vv ((k + 3) % 5)) (vv k)] at h
  -- apply the four-point yardstick to `(vv k, vv (k+2), vv (k+4), vv (k+3))`
  have hyard := p15w_yard (vv k) (vv ((k + 2) % 5)) (vv ((k + 4) % 5))
    (vv ((k + 3) % 5)) (‖vv k - vv ((k + 2) % 5)‖) rfl hvu hxw huw hta htb
  obtain ⟨hminle, htle⟩ := hyard
  by_cases hcase :
      ‖vv ((k + 2) % 5) - vv ((k + 4) % 5)‖ ≤ ‖vv k - vv ((k + 3) % 5)‖
  · refine ⟨(k + 2) % 5, ?_, ?_, ?_⟩
    · rw [Set.mem_Icc]; omega
    · have hidx : (((k + 2) % 5 + 2) % 5) = (k + 4) % 5 := by omega
      rw [hidx]
      rwa [min_eq_right hcase] at hminle
    · have hidx : (((k + 2) % 5 + 3) % 5) = k % 5 := by omega
      rw [hidx, Nat.mod_eq_of_lt hk, norm_sub_rev]
      exact htle
  · refine ⟨k, ?_, ?_, ?_⟩
    · rw [Set.mem_Icc]; omega
    · exact htle
    · have hcase' :
          ‖vv k - vv ((k + 3) % 5)‖ ≤ ‖vv ((k + 2) % 5) - vv ((k + 4) % 5)‖ :=
        le_of_lt (lt_of_not_ge hcase)
      rwa [min_eq_left hcase'] at hminle

/-- HOL `VPWSHTO` (VPWSHTO.hl:1978): every 5-cycle of unit edges has a vertex
whose two pentagon diagonals are at most `1 + sqrt 5`. -/
theorem VPWSHTO_p15 : ∀ vv : ℕ → V3,
    ¬Collinear ℝ ({vv 0, vv 1, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 3, vv 1, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 1, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 3, vv 0, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 0, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 3, vv 2} : Set V3) →
    ¬Collinear ℝ ({vv 3, vv 0, vv 1} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 0, vv 1} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 3, vv 1} : Set V3) →
    ¬Collinear ℝ ({vv 4, vv 3, vv 0} : Set V3) →
    norm (vv 0 - vv 1) = 2 → norm (vv 1 - vv 2) = 2 → norm (vv 2 - vv 3) = 2 →
    norm (vv 3 - vv 4) = 2 → norm (vv 4 - vv 0) = 2 →
    ∃ i : ℕ, i ∈ Set.Icc (0 : ℕ) 4 ∧
      norm (vv i - vv ((i + 2) % 5)) ≤ 1 + Real.sqrt 5 ∧
      norm (vv i - vv ((i + 3) % 5)) ≤ 1 + Real.sqrt 5 := by
  intro vv h012 h312 h412 h302 h402 h432 h301 h401 h431 h430
    hs01 hs12 hs23 hs34 hs40
  -- the ten non-collinearity hypotheses are not needed by the analytic route
  clear h012 h312 h412 h302 h402 h432 h301 h401 h431 h430
  have hs := p15w_sides vv hs01 hs12 hs23 hs34 hs40
  obtain ⟨k, hkmem, hkmin⟩ := Finset.exists_min_image (Finset.range 5)
    (fun j : ℕ => ‖vv j - vv ((j + 2) % 5)‖) ⟨0, by simp⟩
  have hk : k < 5 := Finset.mem_range.mp hkmem
  exact p15w_vpwshto2 vv k hk hs (fun j hj => hkmin j (Finset.mem_range.mpr hj))

/-- HOL `POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR` (VPWSHTO.hl:2114): no annulus
packing point lies on the closed segment between two others.
PROVED 2026-11-05 (m1a-root-w4): Stewart/variance identity + the annulus
upper bound `2 * h0 = 2.52`; no external blocker. -/
theorem POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15 : ∀ u v w : V3,
    ({u, v, w} : Set V3) ⊆ ballAnnulus →
    Kepler.Packing ({u, v, w} : Set V3) →
    u ≠ v → u ≠ w → v ≠ w →
    v ∉ segment ℝ u w := by
  intro u v w hsub hp huv huw hvw hvseg
  -- annulus membership gives the two norm bounds
  have hu_ann : u ∈ ballAnnulus := hsub (by simp)
  have hv_ann : v ∈ ballAnnulus := hsub (by simp)
  have hw_ann : w ∈ ballAnnulus := hsub (by simp)
  rw [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
    dist_eq_norm, sub_zero] at hu_ann hv_ann hw_ann
  obtain ⟨hu_hi, hu_lo⟩ := hu_ann
  obtain ⟨hv_hi, hv_lo⟩ := hv_ann
  obtain ⟨hw_hi, hw_lo⟩ := hw_ann
  have hu2 : 2 ≤ ‖u‖ := le_of_not_gt hu_lo
  have hv2 : 2 ≤ ‖v‖ := le_of_not_gt hv_lo
  have hw2 : 2 ≤ ‖w‖ := le_of_not_gt hw_lo
  -- unpack the segment membership as an affine combination
  rw [mem_segment_iff_div] at hvseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hvseg
  set p : ℝ := a / (a + b) with hp_def
  set q : ℝ := b / (a + b) with hq_def
  have hp0 : 0 ≤ p := div_nonneg ha (le_of_lt hab)
  have hq0 : 0 ≤ q := div_nonneg hb (le_of_lt hab)
  have hpq1 : p + q = 1 := by
    rw [hp_def, hq_def, ← add_div, div_self (ne_of_gt hab)]
  have hveq : p • u + q • w = v := heq
  -- the two pieces of the segment
  have hcpos : 0 < dist u w := dist_pos.mpr huw
  have hcnonneg : 0 ≤ dist u w := le_of_lt hcpos
  have hvu : v - u = q • (w - u) := by
    rw [← hveq, show p = 1 - q by linarith]
    module
  have hvw' : v - w = p • (u - w) := by
    rw [← hveq, show q = 1 - p by linarith]
    module
  have hdist_vu : dist v u = q * dist u w := by
    rw [dist_eq_norm, dist_eq_norm, hvu, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hq0, norm_sub_rev w u]
  have hdist_vw : dist v w = p * dist u w := by
    rw [dist_eq_norm, dist_eq_norm, hvw', norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hp0]
  -- packing gives both pieces at least 2
  have hpv : v ∈ ({u, v, w} : Set V3) := by simp
  have hpu : u ∈ ({u, v, w} : Set V3) := by simp
  have hpw : w ∈ ({u, v, w} : Set V3) := by simp
  have h2vw : 2 ≤ dist v w := Packing.dist_ge_two hp hpv hpw hvw
  have h2vu : 2 ≤ dist v u := Packing.dist_ge_two hp hpv hpu (Ne.symm huv)
  -- hence p, q > 0
  have hppos : 0 < p := by
    rcases eq_or_lt_of_le hp0 with h | h
    · rw [← h] at hdist_vw
      simp only [zero_mul] at hdist_vw
      linarith
    · exact h
  have hqpos : 0 < q := by
    rcases eq_or_lt_of_le hq0 with h | h
    · rw [← h] at hdist_vu
      simp only [zero_mul] at hdist_vu
      linarith
    · exact h
  -- the variance identity
  have hvar : ‖v‖ ^ 2 = p * ‖u‖ ^ 2 + q * ‖w‖ ^ 2 - p * q * ‖u - w‖ ^ 2 := by
    have hexp : ‖v‖ ^ 2
        = p ^ 2 * ‖u‖ ^ 2 + 2 * (p * q) * inner ℝ u w + q ^ 2 * ‖w‖ ^ 2 := by
      rw [← hveq, norm_add_sq_real]
      simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left,
        real_inner_smul_right, mul_pow, sq_abs]
      ring
    have hsub : ‖u - w‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u w + ‖w‖ ^ 2 :=
      norm_sub_sq_real u w
    rw [hexp, hsub]
    have hp1 : p = 1 - q := by linarith
    rw [hp1]
    ring
  -- numerically: (2 h0)^2 - 4 < 4
  have hnum : (2 * h0) ^ 2 - 4 < 4 := by
    have hh : h0 = 1.26 := rfl
    rw [hh]
    norm_num
  -- pool the bounds
  have hub : ‖u‖ ^ 2 ≤ (2 * h0) ^ 2 := by
    have h2h0 : 0 ≤ 2 * h0 := by
      have hh : h0 = 1.26 := rfl
      rw [hh]; norm_num
    nlinarith [norm_nonneg u]
  have hwb : ‖w‖ ^ 2 ≤ (2 * h0) ^ 2 := by
    have h2h0 : 0 ≤ 2 * h0 := by
      have hh : h0 = 1.26 := rfl
      rw [hh]; norm_num
    nlinarith [norm_nonneg w]
  have h4pq : 4 ≤ p * q * ‖u - w‖ ^ 2 := by
    rw [hdist_vw] at h2vw
    rw [hdist_vu] at h2vu
    have hmul : (2 : ℝ) * 2 ≤ (p * dist u w) * (q * dist u w) :=
      mul_le_mul h2vw h2vu (by norm_num) (by nlinarith [h2vw])
    have hdw : ‖u - w‖ = dist u w := by rw [dist_eq_norm]
    rw [hdw]
    nlinarith [hmul]
  -- final arithmetic
  have hvc : 4 ≤ ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  nlinarith [hvar, hub, hwb, h4pq, hvc, hppos, hqpos]

private theorem triple_subset5_p15 {vv : ℕ → V3} {a b c : ℕ} (ha : a < 5) (hb : b < 5)
    (hc : c < 5) :
    ({vv a, vv b, vv c} : Set V3) ⊆ ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  have ha5 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
  have hb5 : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
  have hc5 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
  rcases hx with rfl | rfl | rfl
  · rcases ha5 with rfl | rfl | rfl | rfl | rfl <;> simp
  · rcases hb5 with rfl | rfl | rfl | rfl | rfl <;> simp
  · rcases hc5 with rfl | rfl | rfl | rfl | rfl <;> simp

private theorem triple_rotate_p15 (a b c : V3) : ({a, b, c} : Set V3) = {b, c, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem subsetRotate_p15 (a b c : V3) (h : ({a, b, c} : Set V3) ⊆ ballAnnulus) :
    ({b, c, a} : Set V3) ⊆ ballAnnulus := by
  rw [← triple_rotate_p15 a b c]
  exact h

private theorem packingRotate_p15 (a b c : V3) (h : Kepler.Packing ({a, b, c} : Set V3)) :
    Kepler.Packing ({b, c, a} : Set V3) := by
  rw [← triple_rotate_p15 a b c]
  exact h

/-- HOL `POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR2` (VPWSHTO.hl:2846): annulus
packing triples are not collinear (the three betweenness cases of
`COLLINEAR_BETWEEN_CASES` discharged by permuting the previous lemma). -/
theorem POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR2_p15 : ∀ u v w : V3,
    ({u, v, w} : Set V3) ⊆ ballAnnulus →
    Kepler.Packing ({u, v, w} : Set V3) →
    v ≠ u → v ≠ w → u ≠ w →
    ¬Collinear ℝ ({u, v, w} : Set V3) := by
  intro u v w hsub hp hvu hvw huw hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hb | hb | hb
  · exact POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15 u v w hsub hp hvu.symm huw hvw
      hb.mem_segment
  · exact POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15 v w u (subsetRotate_p15 u v w hsub)
      (packingRotate_p15 u v w hp) hvw hvu huw.symm hb.mem_segment
  · exact POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15 w u v
      (subsetRotate_p15 v w u (subsetRotate_p15 u v w hsub))
      (packingRotate_p15 v w u (packingRotate_p15 u v w hp)) huw.symm hvw.symm hvu.symm
      hb.mem_segment

/-- HOL `SUBSET_PACKING` (VPWSHTO.hl:2860, via `Geomdetail.SUB_PACKING`). -/
theorem SUBSET_PACKING_p15 : ∀ t s : Set V3, Kepler.Packing s → t ⊆ s →
    Kepler.Packing t := by
  intro t s hp hsub u _hu v _hv hd
  exact hp u (hsub _hu) v (hsub _hv) hd

private theorem notCollinear_triple_p15 {vv : ℕ → V3} (a b c : ℕ) (h5 : a < 5 ∧ b < 5 ∧ c < 5)
    (hsub : ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) ⊆ ballAnnulus)
    (hp : Kepler.Packing ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3))
    (hab : vv a ≠ vv b) (hac : vv a ≠ vv c) (hbc : vv b ≠ vv c) :
    ¬Collinear ℝ ({vv a, vv b, vv c} : Set V3) :=
  POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR2_p15 (vv a) (vv b) (vv c)
    (Set.Subset.trans (triple_subset5_p15 h5.1 h5.2.1 h5.2.2) hsub)
    (SUBSET_PACKING_p15 _ _ hp (triple_subset5_p15 h5.1 h5.2.1 h5.2.2))
    hab.symm hbc hac

/-- HOL `VPWSHTO_PRIME` (VPWSHTO.hl:2867): the annulus version of `VPWSHTO`;
the ten non-collinearity hypotheses of `VPWSHTO` are discharged from
`ball_annulus` + `packing` + distinctness, and the duplicated
`~(vv 0 = vv 1)` conjunct is kept verbatim. -/
theorem VPWSHTO_PRIME_p15 : ∀ vv : ℕ → V3,
    ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) ⊆ ballAnnulus →
    Kepler.Packing ({vv 0, vv 1, vv 2, vv 3, vv 4} : Set V3) →
    vv 0 ≠ vv 1 → vv 0 ≠ vv 1 → vv 0 ≠ vv 2 → vv 0 ≠ vv 3 →
    vv 0 ≠ vv 4 → vv 1 ≠ vv 2 → vv 1 ≠ vv 3 → vv 1 ≠ vv 4 →
    vv 2 ≠ vv 3 → vv 2 ≠ vv 4 → vv 3 ≠ vv 4 →
    norm (vv 0 - vv 1) = 2 → norm (vv 1 - vv 2) = 2 → norm (vv 2 - vv 3) = 2 →
    norm (vv 3 - vv 4) = 2 → norm (vv 4 - vv 0) = 2 →
    ∃ i : ℕ, i ∈ Set.Icc (0 : ℕ) 4 ∧
      norm (vv i - vv ((i + 2) % 5)) ≤ 1 + Real.sqrt 5 ∧
      norm (vv i - vv ((i + 3) % 5)) ≤ 1 + Real.sqrt 5 := by
  intro vv hsub hp _h01dup h01 h02 h03 h04 h12 h13 h14 h23 h24 h34
    hn01 hn12 hn23 hn34 hn40
  refine VPWSHTO_p15 vv (notCollinear_triple_p15 0 1 2 (by omega) hsub hp h01 h02 h12)
    (notCollinear_triple_p15 3 1 2 (by omega) hsub hp h13.symm h23.symm h12)
    (notCollinear_triple_p15 4 1 2 (by omega) hsub hp h14.symm h24.symm h12)
    (notCollinear_triple_p15 3 0 2 (by omega) hsub hp h03.symm h23.symm h02)
    (notCollinear_triple_p15 4 0 2 (by omega) hsub hp h04.symm h24.symm h02)
    (notCollinear_triple_p15 4 3 2 (by omega) hsub hp h34.symm h24.symm h23.symm)
    (notCollinear_triple_p15 3 0 1 (by omega) hsub hp h03.symm h13.symm h01)
    (notCollinear_triple_p15 4 0 1 (by omega) hsub hp h04.symm h14.symm h01)
    (notCollinear_triple_p15 4 3 1 (by omega) hsub hp h34.symm h14.symm h13.symm)
    (notCollinear_triple_p15 4 3 0 (by omega) hsub hp h34.symm h04.symm h03.symm)
    hn01 hn12 hn23 hn34 hn40

end Kepler.Text
