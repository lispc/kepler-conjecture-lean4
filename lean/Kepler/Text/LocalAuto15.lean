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

DISCHARGES (remaining `sorry`): `MAX_COPLANAR_4POINT_p15`,
  `SUM_4ANGLE_4POINT_EQ_2PI_p15`, `EQ_DIAGONAL_MIN_p15`,
  `TWO_DIAGONAL_AT_MOST_p15`, `MAX_IF_COPLANAR_p15`,
  `MAX_IF_COPLANAR1_p15`, `TWO_DIAGONAL_AT_MOST1_p15`, `VPWSHTO1_p15`,
  `VPWSHTO200_p15`, `VPWSHTO2_p15`, `VPWSHTO_p15`,
  `POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15`.
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
  sorry

/-- HOL `POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR` (VPWSHTO.hl:2114): no annulus
packing point lies on the closed segment between two others. -/
theorem POINTS_IN_BALL_ANNULUS_NOT_COLLINEAR_p15 : ∀ u v w : V3,
    ({u, v, w} : Set V3) ⊆ ballAnnulus →
    Kepler.Packing ({u, v, w} : Set V3) →
    u ≠ v → u ≠ w → v ≠ w →
    v ∉ segment ℝ u w := by
  sorry

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
