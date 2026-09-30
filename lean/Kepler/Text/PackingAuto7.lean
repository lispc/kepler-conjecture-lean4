/-
Packing chapter, part B (Rogers.hl, part 2 of 2).

HOL source: Flyspeck `scripts/packing/Rogers.hl` (10872 lines, 111 all-caps
theorems + 13 lowercase `_lemma`s). PART BOUNDARY: this file ports the LAST
56 all-caps theorems, `ANGLE_GT_PI2` (Rogers.hl:5292, all-caps thm 56 of 111)
through `WQPRRDY` (Rogers.hl:10534, all-caps thm 111 of 111), plus the six
lowercase helpers interleaved in that line range (`ANGLE_SUM_lemma`,
`NEIGHBORHOOD_lemma`, `YIFVQDV_lemma_aff_dim`, `KSOQKWL_lemma0/lemma1` —
62 items total). Part A (thms 1..55, Rogers.hl:35..5252: face kit, GLTVHUM,
DUUNHOR, circumcenter kit, MHFTTZN, XYOFCGX_lemma0/1/2) is ported separately
into `PackingAuto6.lean`, which this file deliberately does NOT import
(does not exist reliably yet); any part-A statement needed here is stated
as a private `_p7` copy marked `NEEDS: PackingAuto6`.

Capstone: `WQPRRDY` — the main Rogers bound identity: the hull of a
barfixed simplex equals the union of its Rogers simplices over all vertex
orderings. Stated verbatim; proof body `sorry`.

Encoding notes (following PackingAuto2/5 conventions).
- HOL `real^N` / `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler.Geom);
  generic-`A` list statements are kept polymorphic where possible
  (`IVFICRK`), otherwise instantiated at `V3` (`IVFICRK_real3`).
- HL `angle(a,b,c)` ↔ `EuclideanGeometry.angle a b c`; HL `arcV`/`dihV` ↔
  `Kepler.Geom.arcV`/`dihV`; HL `azim` ↔ `Kepler.Geom.azim` (junk `0` on
  collinear arguments, so the unconditional HL azim identities remain
  provable by case analysis on collinearity).
- HL `projection(n,y)` (first argument the direction/normal) ↔
  `Kepler.Text.projection y n` (PackingAuto2 takes the point first).
- HL `~collinear {v,w,x}` ↔ `¬ Kepler.Geom.Collinear3 v w x`.
- HL `dist (x,y)` ↔ `dist x y`; `ball(x,r)` ↔ `Metric.ball x r`;
  `x pow 2` ↔ `^ 2`; `&2` ↔ `(2:ℝ)`; `pi` ↔ `Real.pi`; `CARD` ↔ `Nat.card`.
- HL `p permutes (0..k)` ↔ `PackingAuto2.permutes p (Set.Icc 0 k)` (weak,
  pointwise-on-set encoding — see PackingAuto5 encoding note: HL's
  complement-fixing `permutes` is strictly stronger). ENCODING-FIX
  (2026-09-30, user-approved batch A): the two `NOT_ID_IMP_*` statements
  below and `KSOQKWL` now carry the missing complement-fixing premise
  (`hfix`/`hpout : ∀ j, k < j → p j = j`), restoring HOL fidelity; their
  proof bodies remain `sorry` (GIANT). Linkage: the
  `PackingConcl.KSOQKWL_concl_discharged` call site predates `KSOQKWL`'s
  extra argument (to be re-threaded with SF item 25).
- HL `{f j | j IN 0..k}` ↔ `{f j | j ∈ Finset.Icc 0 k}`;
  `INTERS`/`UNIONS` ↔ `⋂₀`/`⋃₀`; `FAN`/`dart1_of_fan`/`set_of_edge` ↔
  `Kepler.Text.Fan.*`. HL `hypermap_of_fan` has no Lean counterpart yet
  (deferred in Kepler/Text/Fan.lean): `STRICT_CYCLIC_FAN_PROPERTIES` goes
  through the private placeholder `hypermapOfFan_p7`
  (`NEEDS: PackingAuto6`/fan lane to replace).
- HL `EL j l` ↔ `List.getD l j default` (junk-value convention of
  PackingAuto2); HL `DROP l i` ↔ `PackingAuto2.dropIth l i`.
- Statements are verbatim-faithful; the short/mechanical ones are proved,
  the geometric giants carry `sorry` (same skeleton discipline as
  PackingAuto5).
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Private helpers (π/2–cosine bridge; HL proves these inline) -/

/-- For `a ∈ [0,π]`: `π/2 < a ↔ cos a < 0` (used by `ANGLE_GT_PI2`,
`ARCV_GT_PI2`, `DIHV_GT_PI2`, `OBTUSE_ANGLE_PROJECTION`). -/
private theorem p7_pi2_cos (a : ℝ) (h0 : 0 ≤ a) (hp : a ≤ Real.pi) :
    Real.pi / 2 < a ↔ Real.cos a < 0 := by
  constructor
  · intro h
    have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 2) (y := a)
      (by linarith [Real.pi_pos]) hp h
    rwa [Real.cos_pi_div_two] at h2
  · intro h
    by_contra hc
    have h2 : Real.cos (Real.pi / 2) ≤ Real.cos a :=
      Real.strictAntiOn_cos.antitoneOn (a := a) (b := Real.pi / 2) ⟨h0, hp⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith)
    rw [Real.cos_pi_div_two] at h2
    exact absurd h (not_lt.mpr h2)

/-- Junk-safe `arcV`/`dihV` bridge: `π/2 < arcV u v w ↔ cos (arcV u v w) < 0`
(`arcV` is an `arccos`, hence valued in `[0,π]`, junk cases included). -/
private theorem p7_arcV_pi2 (u v w : V3) :
    Real.pi / 2 < arcV u v w ↔ Real.cos (arcV u v w) < 0 := by
  unfold arcV
  exact p7_pi2_cos _ (Real.arccos_nonneg _) (Real.arccos_le_pi _)

/-- Self-dot of a nonzero vector is nonzero. -/
private theorem p7_dot_self_ne_zero (n : V3) (hn : n ≠ 0) : n ⬝ᵥ n ≠ 0 := by
  have hnsq : ‖n‖ ^ 2 = n ⬝ᵥ n := norm_sq_eq_dot n
  intro h0
  have h2 : ‖n‖ ^ (2:ℕ) = 0 := by rw [hnsq]; exact h0
  have h3 : ‖n‖ = 0 := sq_eq_zero_iff.mp h2
  exact hn (norm_eq_zero.mp h3)

/-- Dot square of a scaled vector (via the inner-product bridge). -/
private theorem p7_smul_sq_dot (s : ℝ) (n : V3) :
    ((s • n : V3)) ⬝ᵥ ((s • n : V3)) = s * s * (n ⬝ᵥ n) := by
  rw [← inner_eq_dot (s • n) (s • n), real_inner_smul_left, real_inner_smul_right,
    ← inner_eq_dot n n]
  ring

/-! ## ANGLE_GT_PI2 (Rogers.hl:5292, thm 56) .. OBTUSE_ANGLE_PROJECTION -/

/-- Vector-level π/2 bridge (inner form; HL proves these inline). -/
private theorem p7_vec_pi2 (x y : V3) :
    Real.pi / 2 < InnerProductGeometry.angle x y ↔ inner ℝ x y < 0 := by
  have hrange := p7_pi2_cos (InnerProductGeometry.angle x y)
    (InnerProductGeometry.angle_nonneg x y) (InnerProductGeometry.angle_le_pi x y)
  rw [hrange, InnerProductGeometry.cos_angle]
  by_cases hnorm : ‖(x : V3)‖ * ‖(y : V3)‖ = 0
  · rw [hnorm, div_zero]
    have hx0 : inner ℝ x y = 0 := by
      rcases mul_eq_zero.mp hnorm with hx | hy
      · rw [norm_eq_zero.mp hx]; exact inner_zero_left y
      · rw [norm_eq_zero.mp hy]; exact inner_zero_right x
    simp [hx0]
  · have hpos : (0:ℝ) < ‖(x : V3)‖ * ‖(y : V3)‖ :=
      mul_pos (norm_pos_iff.mpr fun hz => hnorm (by simp [hz]))
        (norm_pos_iff.mpr fun hz => hnorm (by simp [hz]))
    constructor
    · intro h
      have h2 := mul_lt_mul_of_pos_right h hpos
      rw [div_mul_cancel₀ _ (ne_of_gt hpos), zero_mul] at h2
      exact h2
    · intro h
      by_contra hc
      have hc' : 0 ≤ inner ℝ x y / (‖(x : V3)‖ * ‖(y : V3)‖) := le_of_not_gt hc
      have h2 := mul_nonneg hc' (le_of_lt hpos)
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
      exact absurd h (not_lt.mpr h2)

/-- Vector-level π/2 bridge (dot form). -/
private theorem p7_vec_pi2_dot (x y : V3) :
    Real.pi / 2 < InnerProductGeometry.angle x y ↔ x ⬝ᵥ y < 0 := by
  rw [← inner_eq_dot x y]
  exact p7_vec_pi2 x y

/-- HL `ANGLE_GT_PI2` (Rogers.hl:5292): an angle exceeds `π/2` iff the
underlying dot product is negative. -/
theorem ANGLE_GT_PI2 (a b c : V3) :
    Real.pi / 2 < EuclideanGeometry.angle a b c ↔ (a - b) ⬝ᵥ (c - b) < 0 :=
  p7_vec_pi2_dot (a - b) (c - b)

/-- HL `ARCV_GT_PI2` (Rogers.hl:5003). -/
theorem ARCV_GT_PI2 (p u v : V3) :
    Real.pi / 2 < arcV p u v ↔ Real.cos (arcV p u v) < 0 :=
  p7_arcV_pi2 p u v

/-- HL `DIHV_GT_PI2` (Rogers.hl:6370). -/
theorem DIHV_GT_PI2 (v w x y : V3) :
    Real.pi / 2 < dihV v w x y ↔ Real.cos (dihV v w x y) < 0 := by
  unfold dihV
  exact p7_arcV_pi2 0 _ _

/-- HL `AZIM_COMPL_EXT` (Rogers.hl:5348). -/
theorem AZIM_COMPL_EXT (v w a b : V3) :
    azim v w b a = if azim v w a b = 0 then 0 else 2 * Real.pi - azim v w a b := by
  by_cases ha : Collinear3 v w a
  · simp [azim, ha]
  · by_cases hb : Collinear3 v w b
    · simp [azim, hb]
    · exact azim_compl ha hb

/-- HL `AZIM_EQ_SYM` (Rogers.hl:5365). -/
theorem AZIM_EQ_SYM (v w a b c : V3) :
    azim v w b a = azim v w c a ↔ azim v w a b = azim v w a c := by
  by_cases ha : Collinear3 v w a
  · simp [azim, ha]
  · by_cases hb : Collinear3 v w b
    · have h0b : azim v w b a = 0 ∧ azim v w a b = 0 :=
        ⟨by simp [azim, hb], by simp [azim, hb]⟩
      by_cases hc : Collinear3 v w c
      · have h0c : azim v w c a = 0 ∧ azim v w a c = 0 :=
          ⟨by simp [azim, hc], by simp [azim, hc]⟩
        simp [h0b.1, h0b.2, h0c.1, h0c.2]
      · constructor
        · intro h
          have hca : azim v w c a = 0 := h.symm.trans h0b.1
          have hac : azim v w a c = 0 := (azim_eq_zero_symm hc ha).mp hca
          rw [h0b.2, hac]
        · intro h
          have hac : azim v w a c = 0 := h.symm.trans h0b.2
          have hca : azim v w c a = 0 := (azim_eq_zero_symm hc ha).mpr hac
          rw [h0b.1, hca]
    · by_cases hc : Collinear3 v w c
      · have h0c : azim v w c a = 0 ∧ azim v w a c = 0 :=
          ⟨by simp [azim, hc], by simp [azim, hc]⟩
        constructor
        · intro h
          have hba : azim v w b a = 0 := h.trans h0c.1
          have hab : azim v w a b = 0 := (azim_eq_zero_symm hb ha).mp hba
          rw [hab, h0c.2]
        · intro h
          have hab : azim v w a b = 0 := h.trans h0c.2
          have hba : azim v w b a = 0 := (azim_eq_zero_symm hb ha).mpr hab
          rw [hba, h0c.1]
      · constructor
        · intro h
          rw [azim_compl hb ha, azim_compl hc ha, h]
        · intro h
          rw [azim_compl ha hb, azim_compl ha hc, h]

/-- HL `STRICT_CYCLIC_IMP_FAN` (Rogers.hl:5373). -/
theorem STRICT_CYCLIC_IMP_FAN (V : Set V3) (p : V3) (hfin : V.Finite)
    (hcard : 2 ≤ Nat.card V)
    (hazim : ∀ v w, v ∈ V → w ∈ V → v ≠ w → 0 < azim 0 p v w) :
    Kepler.Text.Fan.FAN 0 (V ∪ {p}) {e : Set V3 | ∃ v ∈ V, e = {p, v}} := by
  sorry

/-- HL `hypermap_of_fan (V,E)` (fan_defs.hl): deferred in
Kepler/Text/Fan.lean; private placeholder for
`STRICT_CYCLIC_FAN_PROPERTIES`. NEEDS: PackingAuto6 / fan lane to replace
the placeholder by the real `hypermapOfFan`. -/
private noncomputable def hypermapOfFan_p7 (W : Set V3) (E : Set (Set V3)) :
    Hypermap (V3 × V3) := by sorry

/-- HL `STRICT_CYCLIC_FAN_PROPERTIES` (Rogers.hl:5832). -/
theorem STRICT_CYCLIC_FAN_PROPERTIES (V : Set V3) (p : V3)
    (hf : Kepler.Text.Fan.FAN 0 (V ∪ {p}) {e : Set V3 | ∃ v ∈ V, e = {p, v}}) :
    (∀ v, v ∈ V → (p, v) ∈ Kepler.Text.Fan.dart1OfFan (V ∪ {p})
      {e : Set V3 | ∃ v ∈ V, e = {p, v}}) ∧
    Kepler.Text.Fan.setOfEdge p (V ∪ {p}) {e : Set V3 | ∃ v ∈ V, e = {p, v}} = V ∧
    (∀ v, v ∈ V → Hypermap.node (hypermapOfFan_p7 (V ∪ {p})
      {e : Set V3 | ∃ v ∈ V, e = {p, v}}) (p, v) = {(p, w) | w ∈ V}) := by
  sorry

/-- HL `ANGLE_SUM_lemma` (Rogers.hl:5901): the cyclic ordering pairing each
point to its azim-successor realizes the full angle sum `2π`. -/
theorem ANGLE_SUM_lemma (V : Set V3) (p : V3) (hfin : V.Finite)
    (hcard : 2 ≤ Nat.card V)
    (hazim : ∀ v w, v ∈ V → w ∈ V → v ≠ w → 0 < azim 0 p v w) :
    ∃ f : V3 → V3, (∀ x, x ∈ V → f x ∈ V ∧ x ≠ f x) ∧
      setSum V (fun x => azim 0 p x (f x)) = 2 * Real.pi := by
  sorry

/-- HL `ANGLE_SUM_BOUND` (Rogers.hl:5992). -/
theorem ANGLE_SUM_BOUND (V : Set V3) (p : V3) (a : ℝ) (ha : 0 ≤ a)
    (hfin : V.Finite) (hcard : 2 ≤ Nat.card V)
    (hazim : ∀ v w, v ∈ V → w ∈ V → v ≠ w → a < azim 0 p v w) :
    a * (Nat.card V) < 2 * Real.pi := by
  have hazim' : ∀ v w : V3, v ∈ V → w ∈ V → v ≠ w → 0 < azim 0 p v w :=
    fun v w hv hw hne => lt_of_le_of_lt ha (hazim v w hv hw hne)
  obtain ⟨f, hf, hsum⟩ := ANGLE_SUM_lemma V p hfin hcard hazim'
  haveI : Fintype (↑V : Set V3) := Set.Finite.fintype hfin
  have hcardF : Nat.card V = hfin.toFinset.card := by
    rw [Nat.card_eq_fintype_card, Set.Finite.card_toFinset hfin]
  have hsum2 : ∑ w ∈ hfin.toFinset, azim 0 p w (f w) = 2 * Real.pi := by
    unfold setSum at hsum
    rw [dif_pos hfin] at hsum
    exact hsum
  rw [← hsum2, hcardF]
  have hFne : hfin.toFinset.Nonempty := by
    have h2 : 0 < hfin.toFinset.card := by
      rw [← hcardF]
      exact lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) hcard
    exact Finset.card_pos.mp h2
  have hmem : ∀ w ∈ hfin.toFinset, a < azim 0 p w (f w) := by
    intro w hw
    have hwV : w ∈ V := by simpa using hw
    exact hazim w (f w) hwV ((hf w hwV).1) (hf w hwV).2
  show a * hfin.toFinset.card < ∑ w ∈ hfin.toFinset, azim 0 p w (f w)
  calc a * hfin.toFinset.card = ∑ w ∈ hfin.toFinset, a := by
        simp; ring
    _ < ∑ w ∈ hfin.toFinset, azim 0 p w (f w) :=
        Finset.sum_lt_sum_of_nonempty hFne hmem

/-- HL `DIHV_LE_AZIM` (Rogers.hl:6037). -/
theorem DIHV_LE_AZIM (v w x y : V3) (h1 : ¬ Collinear3 v w x)
    (h2 : ¬ Collinear3 v w y) : dihV v w x y ≤ azim v w x y := by
  sorry

/-- HL `IN_PLANE_NOT_COLLINEAR` (Rogers.hl:6049). -/
theorem IN_PLANE_NOT_COLLINEAR (v n : V3) (hv : v ≠ 0) (hn : n ≠ 0)
    (horth : n ⬝ᵥ v = 0) : ¬ Collinear3 0 n v := by
  intro hcol
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := 0) (w := n) (w1 := v) hn).mp hcol
  have hv' : v = c • n := by simpa using hc
  have h1 : n ⬝ᵥ v = c * (n ⬝ᵥ n) := by
    rw [hv', ← inner_eq_dot n (c • n), real_inner_smul_right, ← inner_eq_dot n n]
  rw [horth] at h1
  have hnn : (0:ℝ) < n ⬝ᵥ n := by
    have hnsq : ‖(n : V3)‖ ^ 2 = n ⬝ᵥ n := norm_sq_eq_dot n
    rw [← hnsq]
    positivity
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp h1.symm with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hnn)
  rw [hc0] at hv'
  simp at hv'
  exact hv hv'

/-- HL `ANGLE_EQ_DIHV` (Rogers.hl:6059). -/
theorem ANGLE_EQ_DIHV (v w n : V3) (hv : v ≠ 0) (hw : w ≠ 0) (hn : n ≠ 0)
    (h1 : n ⬝ᵥ v = 0) (h2 : n ⬝ᵥ w = 0) :
    EuclideanGeometry.angle v 0 w = dihV 0 n v w := by
  sorry

/-- HL `PYTHAGORAS_PROJECTION` (Rogers.hl:6079): with `x` in the hyperplane
orthogonal to `n`, the segment to any `y` splits at the projection foot. -/
theorem PYTHAGORAS_PROJECTION (x y n : V3) (h : x ⬝ᵥ n = 0) :
    dist x y ^ 2 = dist x (projection y n) ^ 2 + dist (projection y n) y ^ 2 := by
  rcases eq_or_ne n 0 with h0 | hn
  · subst h0
    simp [projection]
  have hnn := p7_dot_self_ne_zero n hn
  have hproj : projection y n = y - ((y ⬝ᵥ n) / (n ⬝ᵥ n)) • n := rfl
  set c := (y ⬝ᵥ n) / (n ⬝ᵥ n) with hcd
  have hcn : c * (n ⬝ᵥ n) = y ⬝ᵥ n := by
    rw [hcd]; field_simp
  have hinn : inner ℝ x n = 0 := by rw [inner_eq_dot]; exact h
  have d2i : ∀ z t : V3, dist z t ^ 2 = inner ℝ (z - t) (z - t) := by
    intro z t
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  have v1 : inner ℝ (x - y) n = -inner ℝ y n := by
    rw [inner_sub_left, hinn]; ring
  have v2 : inner ℝ n (x - y) = -inner ℝ y n := by
    rw [real_inner_comm]; exact v1
  have v3 : c * inner ℝ n n = inner ℝ y n := by
    rw [inner_eq_dot n n, inner_eq_dot y n]; exact hcn
  have e4 : x - (y - c • n) = (x - y) + c • n := by abel
  have e5 : (y - c • n) - y = ((-1 : ℝ) • (c • n) : V3) := by module
  rw [hproj, d2i, d2i, d2i, e4, e5, inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right, v1, v2, v3,
    inner_eq_dot (x - y) (x - y), inner_eq_dot y n]
  ring

/-- HL `OBTUSE_ANGLE_PROJECTION` (Rogers.hl:6113). -/
theorem OBTUSE_ANGLE_PROJECTION (a w n : V3)
    (h : Real.pi / 2 < EuclideanGeometry.angle a 0 w) (ha : a ⬝ᵥ n = 0) :
    Real.pi / 2 < EuclideanGeometry.angle a 0 (projection w n) := by
  have h1 := (ANGLE_GT_PI2 a 0 w).mp h
  have hia : inner ℝ a n = 0 := by rw [inner_eq_dot]; exact ha
  have hi : inner ℝ a (projection w n) = inner ℝ a w := by
    simp only [projection]
    rw [inner_sub_right, real_inner_smul_right, hia]
    ring
  have hsub : inner ℝ (a - 0) (projection w n - 0) = inner ℝ (a - 0) (w - 0) := by
    rw [inner_sub_right, inner_sub_right, inner_zero_right, sub_zero, sub_zero, hi,
      sub_zero]
  have hP : inner ℝ (a - 0) (projection w n - 0) < 0 := by
    rw [hsub, inner_eq_dot (a - 0) (w - 0)]
    exact (p7_vec_pi2_dot (a - 0) (w - 0)).mp h
  change Real.pi / 2 < InnerProductGeometry.angle (a - 0) (projection w n - 0)
  exact (p7_vec_pi2 (a - 0) (projection w n - 0)).mpr hP

/-! ## XYOFCGX (nearest-neighbor gap) .. XNHPWAB1 -/

/-- HL `XYOFCGX_3_0` (Rogers.hl:6121): in a packing, no point of `V \ S`
is nearer the circumcenter than any point of `S` (3-point case). -/
theorem XYOFCGX_3_0 (V S : Set V3) (hV : Packing V) (hSV : S ⊆ V)
    (hind : ¬ affineDependent S) (hc : circumcenter S = 0)
    (hr : radV S < Real.sqrt 2) (hcard : Nat.card S = 3) :
    ∀ u v, u ∈ S → v ∈ V \ S → dist v 0 > dist u 0 := by
  sorry

/-- HL `XYOFCGX_4_0` (Rogers.hl:6377): the 4-point case. -/
theorem XYOFCGX_4_0 (V S : Set V3) (hV : Packing V) (hSV : S ⊆ V)
    (hind : ¬ affineDependent S) (hc : circumcenter S = 0)
    (hr : radV S < Real.sqrt 2) (hcard : Nat.card S = 4) :
    ∀ u v, u ∈ S → v ∈ V \ S → dist v 0 > dist u 0 := by
  sorry

/-- HL `XYOFCGX` (Rogers.hl:6559): the general circumcenter-gap statement. -/
theorem XYOFCGX (V S : Set V3) (p : V3) (hV : Packing V) (hSV : S ⊆ V)
    (hind : ¬ affineDependent S) (hp : p = circumcenter S)
    (hr : radV S < Real.sqrt 2) :
    ∀ u v, u ∈ S → v ∈ V \ S → dist v p > dist u p := by
  sorry

/-- HL `BARV_AFFINE_INDEPENDENT` (Rogers.hl:6650). -/
theorem BARV_AFFINE_INDEPENDENT (V : Set V3) (ul : List V3) (k : ℕ)
    (hV : Packing V) (hb : barV V k ul) : ¬ affineDependent (setOfList ul) := by
  sorry

/-- HL `BARV_IMP_LENGTH_EQ_CARD` (Rogers.hl:6680). -/
theorem BARV_IMP_LENGTH_EQ_CARD (V : Set V3) (ul : List V3) (k : ℕ)
    (hV : Packing V) (hb : barV V k ul) :
    ul.length = k + 1 ∧ Nat.card (setOfList ul) = k + 1 := by
  sorry

/-- HL `AFFINE_HULL_PROJECTION_EXISTS` (Rogers.hl:6694). -/
theorem AFFINE_HULL_PROJECTION_EXISTS (S : Set V3) (p : V3) (hne : S ≠ ∅) :
    ∃ x n : V3, p = x + n ∧ x ∈ (affineSpan ℝ S : Set V3) ∧
      ∀ v ∈ S, ∀ w ∈ S, (v - w) ⬝ᵥ n = 0 := by
  sorry

/-- HL `AFFINE_HULL_PROJECTION_DIST_EQ` (Rogers.hl:6776). -/
theorem AFFINE_HULL_PROJECTION_DIST_EQ (S : Set V3) (p v w x n : V3)
    (hv : v ∈ S) (hw : w ∈ S) (hdist : dist p v = dist p w) (hpxn : p = x + n)
    (hn : ∀ u ∈ S, ∀ z ∈ S, (u - z) ⬝ᵥ n = 0) : dist x v = dist x w := by
  sorry

/-- HL `ORTHOGONAL_TO_AFFINE_HULL_EQ` (Rogers.hl:6799). -/
theorem ORTHOGONAL_TO_AFFINE_HULL_EQ (S : Set V3) (n : V3) :
    (∀ v ∈ S, ∀ w ∈ S, (v - w) ⬝ᵥ n = 0) ↔
      ∀ v ∈ (affineSpan ℝ S : Set V3), ∀ w ∈ (affineSpan ℝ S : Set V3),
        (v - w) ⬝ᵥ n = 0 := by
  sorry

/-- HL `AFFINE_HULL_PROJECTION_DIST_LE` (Rogers.hl:6863). -/
theorem AFFINE_HULL_PROJECTION_DIST_LE (S : Set V3) (p v x n : V3)
    (hv : v ∈ S) (hpxn : p = x + n) (hx : x ∈ (affineSpan ℝ S : Set V3))
    (hn : ∀ u ∈ S, ∀ z ∈ S, (u - z) ⬝ᵥ n = 0) : dist x v ≤ dist p v := by
  sorry

/-- HL `AFFINE_HULL_PROJECTION_DIST_LT` (Rogers.hl:6889). -/
theorem AFFINE_HULL_PROJECTION_DIST_LT (S : Set V3) (p v x n : V3)
    (hv : v ∈ S) (hp : ¬ p ∈ (affineSpan ℝ S : Set V3)) (hpxn : p = x + n)
    (hx : x ∈ (affineSpan ℝ S : Set V3))
    (hn : ∀ u ∈ S, ∀ z ∈ S, (u - z) ⬝ᵥ n = 0) : dist x v < dist p v := by
  sorry

/-- HL `AFFINE_HULL_CIRCUMCENTER_PROJECTION` (Rogers.hl:6923). -/
theorem AFFINE_HULL_CIRCUMCENTER_PROJECTION (s t : Set V3)
    (hind : ¬ affineDependent s) (hts : t ⊆ s) (hne : t ≠ ∅) :
    ∃ n : V3, circumcenter s = circumcenter t + n ∧
      ∀ v ∈ t, ∀ w ∈ t, (v - w) ⬝ᵥ n = 0 := by
  sorry

/-- HL `AFFINE_HULL_CIRCUMCENTER_EQ` (Rogers.hl:6964). -/
theorem AFFINE_HULL_CIRCUMCENTER_EQ (s t : Set V3)
    (hind : ¬ affineDependent s) (hts : t ⊆ s) (hne : t ≠ ∅)
    (hmem : circumcenter s ∈ (affineSpan ℝ t : Set V3)) :
    circumcenter s = circumcenter t := by
  sorry

/-- HL `AFFINE_HULL_RADV` (Rogers.hl:6986): Pythagoras for circumradii. -/
theorem AFFINE_HULL_RADV (s t : Set V3) (hind : ¬ affineDependent s)
    (hts : t ⊆ s) (hne : t ≠ ∅) :
    radV s ^ 2 = radV t ^ 2 + dist (circumcenter t) (circumcenter s) ^ 2 ∧
      0 ≤ radV s ∧ 0 ≤ radV t := by
  sorry

/-- HL `RADV_MONO` (Rogers.hl:7030). -/
theorem RADV_MONO (s t : Set V3) (hind : ¬ affineDependent s) (hts : t ⊆ s)
    (hne : t ≠ ∅) : radV t ≤ radV s := by
  have h := AFFINE_HULL_RADV s t hind hts hne
  have h4 : radV t ^ 2 ≤ radV s ^ 2 := by
    rw [h.1]; linarith [pow_two_nonneg (dist (circumcenter t) (circumcenter s))]
  by_contra hcon
  have hcon' : radV s < radV t := lt_of_not_ge hcon
  have h7 : 0 < radV t + radV s := by linarith
  have h8 : 0 < (radV t - radV s) * (radV t + radV s) := by
    apply mul_pos <;> linarith
  have key : radV s ^ 2 < radV t ^ 2 := by nlinarith [h8]
  linarith [key, pow_two_nonneg (dist (circumcenter t) (circumcenter s))]

/-- HL `CIRCUMCENTER_LEMMA` (Rogers.hl:3816, part A): the circumcenter is
equidistant from all points of `S`, at distance `radV S`.
NEEDS: PackingAuto6 (part A worker owns this proof). -/
private theorem circumcenter_lemma_p7 (S : Set V3) (hne : S.Nonempty)
    (hind : ¬ affineDependent S) (w : V3) (hw : w ∈ S) :
    dist (circumcenter S) w = radV S :=
  (OAPVION2_concl S hind w hw).symm

/-- HL `HL_PROPERTIES` (Rogers.hl:7046). -/
theorem HL_PROPERTIES (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) :
    ∀ w ∈ setOfList ul, dist (circumcenter (setOfList ul)) w = hl ul := by
  intro w hw
  exact circumcenter_lemma_p7 (setOfList ul) ⟨w, hw⟩
    (BARV_AFFINE_INDEPENDENT V ul k hV hb) w hw

/-- HL `BARV_CIRCUMCENTER_EXISTS` (Rogers.hl:7057). -/
theorem BARV_CIRCUMCENTER_EXISTS (V : Set V3) (ul : List V3) (k : ℕ)
    (hV : Packing V) (hb : barV V k ul) :
    circumcenter (setOfList ul) ∈ (affineSpan ℝ (setOfList ul) : Set V3) :=
  OAPVION1_concl (setOfList ul)
    (Set.nonempty_iff_ne_empty.mp ⟨hdV ul, HD_IN_SET_OF_LIST ul (by rw [hb.1]; omega)⟩)
    (BARV_AFFINE_INDEPENDENT V ul k hV hb)

/-- HL `HL_EQ_DIST0` (Rogers.hl:7081). -/
theorem HL_EQ_DIST0 (V : Set V3) (k : ℕ) (ul : List V3) (hV : Packing V)
    (hb : barV V k ul) : hl ul = dist (circumcenter (setOfList ul)) (hdV ul) := by
  have hlen : 1 ≤ ul.length := by rw [hb.1]; omega
  cases ul with
  | nil =>
    have h0 := hb.1
    simp at h0
  | cons a t =>
    have hhd : hdV (a :: t) = a := rfl
    have hmem : a ∈ setOfList (a :: t) := by simp [setOfList]
    rw [hhd]
    exact (HL_PROPERTIES V (a :: t) k hV hb a hmem).symm

/-- HL `BARV_CIRCUMCENTER_PROJECTION` (Rogers.hl:7093). -/
theorem BARV_CIRCUMCENTER_PROJECTION (V : Set V3) (ul : List V3) (k i : ℕ)
    (hV : Packing V) (hb : barV V k ul) (hik : i ≤ k) :
    ∃ n : V3, circumcenter (setOfList ul)
        = circumcenter (setOfList (truncateSimplex i ul)) + n ∧
      ∀ v ∈ setOfList (truncateSimplex i ul), ∀ w ∈ setOfList (truncateSimplex i ul),
        (v - w) ⬝ᵥ n = 0 := by
  have hlen : i + 1 ≤ ul.length := by rw [hb.1]; omega
  have hinit : initialSublist (truncateSimplex i ul) ul :=
    (Classical.epsilon_spec
      (p := fun vl : List V3 => vl.length = i + 1 ∧ initialSublist vl ul)
      ⟨ul.take (i + 1), by rw [List.length_take]; omega,
        ⟨ul.drop (i + 1), (List.take_append_drop (i + 1) ul).symm⟩⟩).2
  exact AFFINE_HULL_CIRCUMCENTER_PROJECTION (setOfList ul)
    (setOfList (truncateSimplex i ul))
    (BARV_AFFINE_INDEPENDENT V ul k hV hb)
    (SET_OF_LIST_INITIAL_SUBLIST_SUBSET hinit)
    (Set.nonempty_iff_ne_empty.mp ⟨hdV (truncateSimplex i ul),
      HD_IN_SET_OF_LIST _ (by rw [LENGTH_TRUNCATE_SIMPLEX i ul hlen]; omega)⟩)

/-- HL `HL_DECREASE` (Rogers.hl:7135). -/
theorem HL_DECREASE (V : Set V3) (ul : List V3) (k i : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hik : i ≤ k) : hl (truncateSimplex i ul) ≤ hl ul := by
  have hlen : i + 1 ≤ ul.length := by rw [hb.1]; omega
  have hinit : initialSublist (truncateSimplex i ul) ul :=
    (Classical.epsilon_spec
      (p := fun vl : List V3 => vl.length = i + 1 ∧ initialSublist vl ul)
      ⟨ul.take (i + 1), by rw [List.length_take]; omega,
        ⟨ul.drop (i + 1), (List.take_append_drop (i + 1) ul).symm⟩⟩).2
  show radV (setOfList (truncateSimplex i ul)) ≤ radV (setOfList ul)
  exact RADV_MONO (setOfList ul) (setOfList (truncateSimplex i ul))
    (BARV_AFFINE_INDEPENDENT V ul k hV hb)
    (SET_OF_LIST_INITIAL_SUBLIST_SUBSET hinit)
    (Set.nonempty_iff_ne_empty.mp ⟨hdV (truncateSimplex i ul),
      HD_IN_SET_OF_LIST _ (by rw [LENGTH_TRUNCATE_SIMPLEX i ul hlen]; omega)⟩)

/-- HL `XNHPWAB1` (Rogers.hl:7194). -/
theorem XNHPWAB1 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    omegaList V ul = circumcenter (setOfList ul) := by
  sorry

/-! ## AFFINE_HULL_PROJECTION_SEPARATES .. AFFINE_HULL_VORONOI_LIST_SUBSET_INTERS_BIS -/

/-- HL `AFFINE_HULL_PROJECTION_SEPARATES` (Rogers.hl:7431). -/
theorem AFFINE_HULL_PROJECTION_SEPARATES (S : Set V3) (p : V3) (hfin : S.Finite)
    (hp : p ∈ (affineSpan ℝ S : Set V3)) (hnc : ¬ p ∈ convexHull ℝ S) :
    ∃ u ∈ S, ∀ x n : V3, p = x + n → x ∈ (affineSpan ℝ (S \ {u}) : Set V3) →
      (∀ v ∈ S \ {u}, ∀ w ∈ S \ {u}, (v - w) ⬝ᵥ n = 0) →
        (p - x) ⬝ᵥ (u - x) ≤ 0 := by
  sorry

/-- HL `XNHPWAB2` (Rogers.hl:7497). -/
theorem XNHPWAB2 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    omegaList V ul ∈ convexHull ℝ (setOfList ul) := by
  sorry

/-- HL `XNHPWAB4` (Rogers.hl:7691): the truncated circumradii increase
strictly. -/
theorem XNHPWAB4 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    ∀ i j : ℕ, i < j → j ≤ k →
      hl (truncateSimplex i ul) < hl (truncateSimplex j ul) := by
  sorry

/-- HL `OMEGA_LIST_N_IN_CONVEX_HULL` (Rogers.hl:7869). -/
theorem OMEGA_LIST_N_IN_CONVEX_HULL (V : Set V3) (ul : List V3) (k i : ℕ)
    (hV : Packing V) (hb : barV V k ul) (hik : i ≤ k)
    (hl2 : hl ul < Real.sqrt 2) :
    omegaListN V ul i ∈ convexHull ℝ (setOfList ul) := by
  sorry

/-- HL `XNHPWAB3` (Rogers.hl:7926). -/
theorem XNHPWAB3 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    affDim {omegaListN V ul j | j ∈ Finset.Icc 0 k} = (k : ℤ) := by
  sorry

/-- HL `IN_VORONOI_LIST_IMP_IN_BIS` (Rogers.hl:8145). -/
theorem IN_VORONOI_LIST_IMP_IN_BIS (V : Set V3) (ul : List V3) (k : ℕ) (x : V3)
    (hb : barV V k ul) (hx : x ∈ voronoiList V ul) :
    ∀ u ∈ setOfList ul, x ∈ bis (hdV ul) u := by
  have hhd_mem : hdV ul ∈ setOfList ul := by
    cases ul with
    | nil => exact absurd hb.1 (by simp)
    | cons a t => simp [setOfList, hdV]
  have hx' : ∀ w ∈ setOfList ul, x ∈ voronoiClosed V w := by
    have hx2 : x ∈ ⋂₀ {voronoiClosed V v | v ∈ setOfList ul} := hx
    intro w hw
    exact hx2 _ (by simpa using ⟨w, hw, rfl⟩)
  have hsub : setOfList ul ⊆ V := by
    obtain ⟨hlen, hnd⟩ := hb
    have hini : initialSublist ul ul := ⟨[], by simp⟩
    exact (hnd ul ⟨hini, by omega⟩).2.1
  intro u hu
  have huV : u ∈ V := hsub hu
  have hle1 : dist x u ≤ dist x (hdV ul) :=
    hx' u hu (hdV ul) (hsub hhd_mem)
  have hle2 : dist x (hdV ul) ≤ dist x u :=
    hx' (hdV ul) hhd_mem u huV
  exact le_antisymm hle2 hle1

/-- HL `WAUFCHE1` (Rogers.hl:8186). -/
theorem WAUFCHE1 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) : hl ul ≤ dist (omegaList V ul) (hdV ul) := by
  have hlen : 1 ≤ ul.length := by rw [hb.1]; omega
  have hdVmem : hdV ul ∈ setOfList ul := HD_IN_SET_OF_LIST ul hlen
  have hind := BARV_AFFINE_INDEPENDENT V ul k hV hb
  obtain ⟨x, n, hp, hx, hn⟩ := AFFINE_HULL_PROJECTION_EXISTS (setOfList ul)
    (omegaList V ul) (Set.nonempty_iff_ne_empty.mp ⟨hdV ul, hdVmem⟩)
  have homem := OMEGA_LIST_IN_VORONOI_LIST V ul k hb
  have hxeq : ∀ v ∈ setOfList ul, dist x v = dist x (hdV ul) := by
    intro v hv
    have hv2 : v ∈ V := BARV_SUBSET V k ul hb hv
    have hvd : hdV ul ∈ V := BARV_SUBSET V k ul hb hdVmem
    have h2 : omegaList V ul ∈ voronoiClosed V v := homem _ (by simpa using ⟨v, hv, rfl⟩)
    have h3 : omegaList V ul ∈ voronoiClosed V (hdV ul) :=
      homem _ (by simpa using ⟨hdV ul, hdVmem, rfl⟩)
    have h1 : dist (omegaList V ul) v = dist (omegaList V ul) (hdV ul) :=
      le_antisymm (h2 (hdV ul) hvd) (h3 v hv2)
    exact AFFINE_HULL_PROJECTION_DIST_EQ (setOfList ul) (omegaList V ul) v (hdV ul) x n
      hv hdVmem h1 hp hn
  have hxc : x = circumcenter (setOfList ul) :=
    OAPVION3_concl (setOfList ul) hind x hx ⟨dist x (hdV ul), fun w hw => hxeq w hw⟩
  have hle : dist x (hdV ul) ≤ dist (omegaList V ul) (hdV ul) :=
    AFFINE_HULL_PROJECTION_DIST_LE (setOfList ul) (omegaList V ul) (hdV ul) x n
      hdVmem hp hx hn
  show radV (setOfList ul) ≤ dist (omegaList V ul) (hdV ul)
  rw [OAPVION2_concl (setOfList ul) hind (hdV ul) hdVmem, ← hxc]
  exact hle

/-- HL `WAUFCHE2` (Rogers.hl:8249). -/
theorem WAUFCHE2 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    hl ul = dist (omegaList V ul) (hdV ul) := by
  sorry

/-- HL `CIRCUMCENTER_IN_VORONOI_SET` (Rogers.hl:8276). -/
theorem CIRCUMCENTER_IN_VORONOI_SET (V S : Set V3) (hV : Packing V)
    (hSV : S ⊆ V) (hind : ¬ affineDependent S) (hr : radV S < Real.sqrt 2) :
    circumcenter S ∈ voronoiSet V S := by
  have hxy := XYOFCGX V S (circumcenter S) hV hSV hind rfl hr
  show circumcenter S ∈ ⋂₀ {voronoiClosed V v | v ∈ S}
  rw [Set.mem_sInter]
  intro T hT
  obtain ⟨w, hwS, rfl⟩ := by simpa using hT
  intro w' hw'
  by_cases hmem : w' ∈ S
  · have h1 := OAPVION2_concl S hind w hwS
    have h2 := OAPVION2_concl S hind w' hmem
    rw [← h1, ← h2]
  · have hw'V : w' ∈ V \ S := ⟨hw', hmem⟩
    have hgap := hxy w w' hwS hw'V
    rw [dist_comm w' (circumcenter S), dist_comm w (circumcenter S)] at hgap
    exact le_of_lt hgap

/-- HL `NEIGHBORHOOD_lemma` (Rogers.hl:8305). -/
theorem NEIGHBORHOOD_lemma (V S : Set V3) (p : V3) (hV : Packing V)
    (hSV : S ⊆ V)
    (hgap : ∀ u ∈ S, ∀ v ∈ V \ S, dist v p > dist u p) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Metric.ball p r, ∀ u ∈ S, ∀ v ∈ V \ S,
      dist v x > dist u x := by
  by_cases hSE : S = ∅
  · refine ⟨1, by norm_num, ?_⟩
    rw [hSE]
    intro x _ u hu
    exact absurd hu (by simp)
  by_cases hVE : V \ S = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro x _ u _ v hv
    exact absurd hv (by simp [hVE])
  obtain ⟨v0, hv0⟩ := Set.nonempty_iff_ne_empty.mpr hVE
  have hR : ∀ u ∈ S, dist u p < dist v0 p := fun u hu => hgap u hu v0 hv0
  have hfin1 : (V ∩ Metric.ball p (dist v0 p)).Finite := KIUMVTC p (dist v0 p) V hV
  have hfin2 : (V ∩ Metric.ball p (dist v0 p + 2)).Finite :=
    KIUMVTC p (dist v0 p + 2) V hV
  have hSfin : S.Finite := hfin1.subset fun u hu =>
    ⟨hSV hu, Metric.mem_ball.mpr (hR u hu)⟩
  have hWfin : ((V \ S) ∩ Metric.ball p (dist v0 p + 2)).Finite :=
    hfin2.subset fun z hz => ⟨hz.1.1, hz.2⟩
  obtain ⟨u0, hu0⟩ := Set.nonempty_iff_ne_empty.mpr hSE
  have hv0b : v0 ∈ Metric.ball p (dist v0 p + 2) :=
    Metric.mem_ball.mpr (show dist v0 p < dist v0 p + 2 by linarith)
  have hv0W : v0 ∈ (V \ S) ∩ Metric.ball p (dist v0 p + 2) := ⟨hv0, hv0b⟩
  have hPW : (S ×ˢ ((V \ S) ∩ Metric.ball p (dist v0 p + 2))).Finite :=
    hSfin.prod hWfin
  have hmem0 : (u0, v0) ∈ S ×ˢ ((V \ S) ∩ Metric.ball p (dist v0 p + 2)) :=
    ⟨hu0, hv0W⟩
  have hPWne : (S ×ˢ ((V \ S) ∩ Metric.ball p (dist v0 p + 2))).Nonempty :=
    ⟨(u0, v0), hmem0⟩
  have hgapU : (fun z : V3 × V3 => dist z.2 p - dist z.1 p) (u0, v0) ∈
      (Set.Finite.toFinset hPW).image
        (fun z : V3 × V3 => dist z.2 p - dist z.1 p) := by
    refine Finset.mem_image.mpr ⟨(u0, v0), ?_, rfl⟩
    exact Set.Finite.mem_toFinset _ |>.mpr hmem0
  have hgne : ((Set.Finite.toFinset hPW).image
      (fun z : V3 × V3 => dist z.2 p - dist z.1 p)).Nonempty :=
    ⟨_, hgapU⟩
  set gaps : Finset ℝ := (Set.Finite.toFinset hPW).image
      (fun z : V3 × V3 => dist z.2 p - dist z.1 p) with hgdef
  set d : ℝ := Finset.min' gaps hgne with hddef
  have hdmin2 : ∀ b ∈ gaps, d ≤ b := fun b hb => Finset.min'_le gaps b hb
  have hdm0 : d ≤ dist v0 p - dist u0 p := by
    have h1 := hdmin2 ((fun z : V3 × V3 => dist z.2 p - dist z.1 p) (u0, v0)) hgapU
    simpa using h1
  have hdin2 : d ∈ gaps := Finset.min'_mem gaps hgne
  obtain ⟨w, hwU, hdweq⟩ := Finset.mem_image.mp hdin2
  have hwP : w ∈ S ×ˢ ((V \ S) ∩ Metric.ball p (dist v0 p + 2)) :=
    (Set.Finite.mem_toFinset _).mp hwU
  have hdw : dist w.2 p - dist w.1 p = d := hdweq
  have hgtw : dist w.1 p < dist w.2 p := hgap w.1 hwP.1 w.2 hwP.2.1
  have hdpos : 0 < d := by rw [← hdw]; linarith
  refine ⟨min (d / 2) (1 / 2), lt_min (by linarith) (by norm_num), ?_⟩
  intro x hx u hu v hv
  have hxp : dist p x < min (d / 2) (1 / 2) := by
    rw [dist_comm]; exact Metric.mem_ball.mp hx
  have hxd : dist p x < d / 2 := lt_of_lt_of_le hxp (min_le_left _ _)
  have hxh : dist p x < 1 / 2 := lt_of_lt_of_le hxp (min_le_right _ _)
  have hsymm : dist p x = dist x p := dist_comm p x
  by_cases hvin : v ∈ (V \ S) ∩ Metric.ball p (dist v0 p + 2)
  · have hmem2 : (u, v) ∈ S ×ˢ ((V \ S) ∩ Metric.ball p (dist v0 p + 2)) :=
      ⟨hu, hvin⟩
    have hd' : d ≤ dist v p - dist u p := by
      have h1 := hdmin2 ((fun z : V3 × V3 => dist z.2 p - dist z.1 p) (u, v))
        (Finset.mem_image.mpr ⟨(u, v), Set.Finite.mem_toFinset _ |>.mpr hmem2, rfl⟩)
      simpa using h1
    have h1 : dist v p ≤ dist v x + dist x p := dist_triangle v x p
    have h2 : dist u x ≤ dist u p + dist p x := dist_triangle u p x
    linarith
  · have hfar : dist v0 p + 2 ≤ dist v p := by
      have h1' : ¬ dist v p < dist v0 p + 2 := fun h =>
        hvin ⟨hv, Metric.mem_ball.mpr h⟩
      exact le_of_not_gt h1'
    have h2' : dist u p < dist v0 p := hR u hu
    have h3 : dist v p - dist x p ≤ dist v x := by
      linarith [dist_triangle v x p]
    have h4' : dist u x ≤ dist u p + dist p x := dist_triangle u p x
    linarith
/-- HL `SUBSPACES_INTER_BALL_EQ_IMP_EQ` (Rogers.hl:8454). HL `subspace s`
(linear-subspace-as-set predicate) is rendered by the existential over
`Submodule ℝ V3`. -/
theorem SUBSPACES_INTER_BALL_EQ_IMP_EQ (s t : Set V3) (r : ℝ)
    (hs : ∃ K : Submodule ℝ V3, (K : Set V3) = s)
    (ht : ∃ K : Submodule ℝ V3, (K : Set V3) = t)
    (hr : 0 < r) (heq : s ∩ Metric.ball 0 r = t ∩ Metric.ball 0 r) :
    s = t := by
  obtain ⟨Ks, rfl⟩ := hs
  obtain ⟨Kt, rfl⟩ := ht
  have key : ∀ K₁ K₂ : Submodule ℝ V3,
      ((K₁ ∩ Metric.ball 0 r : Set V3) : Set V3) =
        ((K₂ ∩ Metric.ball 0 r : Set V3) : Set V3) →
      (K₁ : Set V3) ⊆ K₂ := by
    intro K₁ K₂ h'
    intro v hv
    rcases eq_or_ne v 0 with h0 | h0
    · exact h0.symm ▸ K₂.zero_mem
    · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr h0
      have hcpos : 0 < r / (‖v‖ + 1) := div_pos hr (by positivity)
      have hcne : r / (‖v‖ + 1) ≠ 0 := ne_of_gt hcpos
      have hcball : ‖((r / (‖v‖ + 1)) • v : V3)‖ < r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, div_mul_eq_mul_div,
          div_lt_iff₀ (by positivity : (0:ℝ) < ‖v‖ + 1)]
        linarith
      have hmem : ((r / (‖v‖ + 1)) • v : V3) ∈ (K₁ ∩ Metric.ball 0 r : Set V3) :=
        ⟨K₁.smul_mem _ hv, Metric.mem_ball.2 (by rw [dist_zero_right]; exact hcball)⟩
      have h3 : ((r / (‖v‖ + 1)) • v : V3) ∈ K₂ := by
        have h2 : ((r / (‖v‖ + 1)) • v : V3) ∈ (K₂ ∩ Metric.ball 0 r : Set V3) := by
          rw [← h']; exact hmem
        exact h2.1
      have h4 : ((r / (‖v‖ + 1))⁻¹ • ((r / (‖v‖ + 1)) • v) : V3) ∈ K₂ :=
        K₂.smul_mem _ h3
      rwa [inv_smul_smul₀ hcne] at h4
  refine Set.ext fun v => ⟨fun hv => key Ks Kt heq hv, fun hv => key Kt Ks heq.symm hv⟩

/-- HL `AFFINES_INTER_BALL_EQ_IMP_EQ` (Rogers.hl:8527). HL `affine s`
(affine-set predicate) is rendered by the existential over
`AffineSubspace ℝ V3`. -/
theorem AFFINES_INTER_BALL_EQ_IMP_EQ (s t : Set V3) (x : V3) (r : ℝ)
    (hs : ∃ K : AffineSubspace ℝ V3, (K : Set V3) = s)
    (ht : ∃ K : AffineSubspace ℝ V3, (K : Set V3) = t)
    (hr : 0 < r) (heq : s ∩ Metric.ball x r = t ∩ Metric.ball x r)
    (hx : x ∈ s) : s = t := by
  sorry

/-- HL `VORONOI_LIST_EQ_INTERS_BIS` (Rogers.hl:8576). -/
theorem VORONOI_LIST_EQ_INTERS_BIS (V : Set V3) (ul : List V3)
    (hsub : setOfList ul ⊆ V) (h1 : 1 ≤ ul.length) :
    voronoiList V ul =
      voronoiClosed V (hdV ul) ∩ ⋂₀ {bis (hdV ul) u | u ∈ setOfList ul} := by
  have hhd_mem : hdV ul ∈ setOfList ul := by
    cases ul with
    | nil => exact absurd h1 (by simp)
    | cons a t => simp [setOfList, hdV]
  ext x
  constructor
  · intro hx
    have hx2 : x ∈ ⋂₀ {voronoiClosed V v | v ∈ setOfList ul} := hx
    rw [Set.mem_sInter] at hx2
    have hx' : ∀ w ∈ setOfList ul, ∀ w' ∈ V, dist x w ≤ dist x w' := by
      intro w hw w' hw'
      have hzw : x ∈ voronoiClosed V w := hx2 _ (by simpa using ⟨w, hw, rfl⟩)
      exact hzw w' hw'
    have hA : ∀ w ∈ V, dist x (hdV ul) ≤ dist x w := hx' (hdV ul) hhd_mem
    have hB : ∀ w ∈ setOfList ul, dist x (hdV ul) = dist x w := by
      intro w hw
      exact le_antisymm (hA w (hsub hw)) (hx' w hw (hdV ul) (hsub hhd_mem))
    refine ⟨hA, ?_⟩
    rw [Set.mem_sInter]
    intro T hT
    obtain ⟨u, hu, rfl⟩ := by simpa using hT
    exact hB u hu
  · intro hx
    have hx1 : ∀ w' ∈ V, dist x (hdV ul) ≤ dist x w' := hx.1
    have hxI : ∀ T ∈ {bis (hdV ul) u | u ∈ setOfList ul}, x ∈ T := hx.2
    show x ∈ ⋂₀ {voronoiClosed V v | v ∈ setOfList ul}
    rw [Set.mem_sInter]
    intro U hU
    obtain ⟨u, hu, rfl⟩ := by simpa using hU
    intro w hw
    have hC : dist x (hdV ul) = dist x u := hxI _ (by simpa using ⟨u, hu, rfl⟩)
    rw [← hC]
    exact hx1 w hw

/-- HL `AFFINE_HULL_VORONOI_LIST_SUBSET_INTERS_BIS` (Rogers.hl:8623). -/
theorem AFFINE_HULL_VORONOI_LIST_SUBSET_INTERS_BIS (V : Set V3) (ul : List V3)
    (hsub : setOfList ul ⊆ V) :
    (affineSpan ℝ (voronoiList V ul) : Set V3) ⊆
      ⋂₀ {bis (hdV ul) u | u ∈ setOfList ul} := by
  cases ul with
  | nil =>
    intro z hz
    rw [Set.mem_sInter]
    intro T hT
    exact absurd hT (by simp [setOfList])
  | cons a t =>
    have h1 : 1 ≤ (a :: t).length := by
      show 1 ≤ t.length + 1
      exact Nat.succ_le_succ (Nat.zero_le t.length)
    rw [VORONOI_LIST_EQ_INTERS_BIS V (a :: t) hsub h1]
    intro z hz
    rw [Set.mem_sInter]
    intro T hT
    obtain ⟨u, hu, rfl⟩ := by simpa using hT
    obtain ⟨K, hK⟩ := AFFINE_BIS (hdV (a :: t)) u
    have hsubK : voronoiClosed V (hdV (a :: t)) ∩
        ⋂₀ {bis (hdV (a :: t)) u | u ∈ setOfList (a :: t)} ⊆ (K : Set V3) := by
      intro w hw
      have hw2 : w ∈ ⋂₀ {bis (hdV (a :: t)) u | u ∈ setOfList (a :: t)} := hw.2
      rw [Set.mem_sInter] at hw2
      rw [hK]
      exact hw2 _ (by simpa using ⟨u, hu, rfl⟩)
    have hle : affineSpan ℝ (voronoiClosed V (hdV (a :: t)) ∩
        ⋂₀ {bis (hdV (a :: t)) u | u ∈ setOfList (a :: t)}) ≤ K :=
      affineSpan_le.mpr hsubK
    have hzK : z ∈ (K : Set V3) := hle hz
    rw [hK] at hzK
    exact hzK

/-- HL `YIFVQDV_lemma_aff_dim` (Rogers.hl:8656). -/
theorem YIFVQDV_lemma_aff_dim (V : Set V3) (vl : List V3) (hV : Packing V)
    (hsub : setOfList vl ⊆ V) (hind : ¬ affineDependent (setOfList vl))
    (hl2 : hl vl < Real.sqrt 2) :
    affDim (voronoiList V vl) =
      affDim (⋂₀ {bis (hdV vl) v | v ∈ setOfList vl}) := by
  sorry

/-! ## YIFVQDV_1 (permutation invariance) .. WQPRRDY (capstone) -/

/-- HL `YIFVQDV_1` (Rogers.hl:8777). -/
theorem YIFVQDV_1 (V : Set V3) (ul : List V3) (k : ℕ) (p : Equiv.Perm ℕ)
    (hV : Packing V) (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2)
    (hperm : permutes p (Set.Icc 0 k)) :
    barV V k (leftActionList p ul) := by
  sorry

/-- HL `YIFVQDV` (Rogers.hl:9118). -/
theorem YIFVQDV (V : Set V3) (ul : List V3) (k : ℕ) (p : Equiv.Perm ℕ)
    (hV : Packing V) (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2)
    (hperm : permutes p (Set.Icc 0 k)) :
    barV V k (leftActionList p ul) ∧
      omegaList V (leftActionList p ul) = omegaList V ul := by
  sorry

/-- HL `HL_TRUNCATE_SIMPLEX_OMEGA_N` (Rogers.hl:9152). -/
theorem HL_TRUNCATE_SIMPLEX_OMEGA_N (V : Set V3) (k : ℕ) (ul : List V3) (j : ℕ)
    (hV : Packing V) (hb : barV V k ul) (hjk : j ≤ k)
    (hl2 : hl ul < Real.sqrt 2) :
    hl (truncateSimplex j ul) = dist (omegaListN V ul j) (hdV ul) := by
  have hlen : j + 1 ≤ ul.length := by rw [hb.1]; omega
  have htr : barV V j (truncateSimplex j ul) := TRUNCATE_SIMPLEX_BARV V j k ul hb hjk
  have hdec := HL_DECREASE V ul k j hV hb hjk
  have hlt : hl (truncateSimplex j ul) < Real.sqrt 2 := by linarith
  have hw := WAUFCHE2 V (truncateSimplex j ul) j hV htr hlt
  rw [hw, OMEGA_LIST_LEMMA V ul j hlen, HD_TRUNCATE_SIMPLEX ul j hlen]

/-- HL `KSOQKWL_lemma0` (Rogers.hl:9197). -/
theorem KSOQKWL_lemma0 (V : Set V3) (ul vl : List V3) (k : ℕ) (hV : Packing V)
    (hb1 : barV V k ul) (hb2 : barV V k vl) (hhd : ¬ (hdV ul = hdV vl)) :
    ¬ ({omegaListN V ul i | i ∈ Finset.Icc 0 k} =
        {omegaListN V vl i | i ∈ Finset.Icc 0 k}) := by
  intro heq
  have h0 : hdV ul ∈ {omegaListN V ul i | i ∈ Finset.Icc 0 k} := by
    rw [Set.mem_setOf_eq]
    exact ⟨0, Finset.mem_Icc.mpr (by omega), rfl⟩
  rw [heq] at h0
  rw [Set.mem_setOf_eq] at h0
  obtain ⟨j, hj, hjv⟩ := h0
  have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
  have hlen : j + 1 ≤ vl.length := by rw [hb2.1]; omega
  have hom : omegaListN V vl j ∈ voronoiList V (truncateSimplex j vl) :=
    OMEGA_LIST_N_IN_VORONOI_LIST V vl k j hb2 hjk
  have hcell : omegaListN V vl j ∈ voronoiClosed V (hdV vl) := by
    rw [← HD_TRUNCATE_SIMPLEX vl j hlen]
    exact (VORONOI_LIST_SUBSET_VORONOI_CLOSED _ _
      (by rw [LENGTH_TRUNCATE_SIMPLEX j vl hlen]; omega)) hom
  have hlenU : 1 ≤ ul.length := by rw [hb1.1]; omega
  have hsub : hdV ul ∈ V := BARV_SUBSET V k ul hb1 (HD_IN_SET_OF_LIST ul hlenU)
  have hz : dist (omegaListN V vl j) (hdV vl) ≤ dist (omegaListN V vl j) (hdV ul) :=
    hcell _ hsub
  rw [hjv, dist_self] at hz
  exact hhd (dist_eq_zero.mp (le_antisymm hz dist_nonneg))

/-- HL `KSOQKWL_lemma1` (Rogers.hl:9264). -/
theorem KSOQKWL_lemma1 (V : Set V3) (ul vl : List V3) (k j : ℕ) (hV : Packing V)
    (hb1 : barV V k ul) (hb2 : barV V k vl)
    (hl1 : hl ul < Real.sqrt 2) (hl2 : hl vl < Real.sqrt 2)
    (hj : 0 < j) (hjk : j ≤ k)
    (htr : truncateSimplex (j - 1) ul = truncateSimplex (j - 1) vl)
    (hhl : hl (truncateSimplex j ul) ≤ hl (truncateSimplex j vl))
    (homega : ¬ (omegaListN V ul j = omegaListN V vl j)) :
    ¬ ({omegaListN V ul i | i ∈ Finset.Icc 0 k} =
        {omegaListN V vl i | i ∈ Finset.Icc 0 k}) := by
  sorry

/-- HL `AFFINE_INDEPENDENT_OMEGA_LIST_N` (Rogers.hl:9354). -/
theorem AFFINE_INDEPENDENT_OMEGA_LIST_N (V : Set V3) (ul : List V3) (k : ℕ)
    (hV : Packing V) (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    ¬ affineDependent {omegaListN V ul i | i ∈ Finset.Icc 0 k} := by
  sorry

/-- HL `ROGERS_EQ` (Rogers.hl:9391). -/
theorem ROGERS_EQ (V : Set V3) (ul vl : List V3) (k : ℕ) (hV : Packing V)
    (hb1 : barV V k ul) (hb2 : barV V k vl)
    (hl1 : hl ul < Real.sqrt 2) (hl2 : hl vl < Real.sqrt 2) :
    rogers V ul = rogers V vl ↔
      {omegaListN V ul i | i ∈ Finset.Icc 0 k} =
        {omegaListN V vl i | i ∈ Finset.Icc 0 k} := by
  have hlen1 : ul.length = k + 1 := hb1.1
  have hlen2 : vl.length = k + 1 := hb2.1
  have hset1 : omegaListN V ul '' {j : ℕ | j < ul.length} =
      {omegaListN V ul i | i ∈ Finset.Icc 0 k} := by
    ext x
    constructor
    · intro him
      rw [Set.mem_image] at him
      obtain ⟨j, hj, hjx⟩ := him
      have hlt : j < ul.length := hj
      exact (⟨j, Finset.mem_Icc.mpr (by omega), hjx⟩ :
        ∃ i, i ∈ Finset.Icc 0 k ∧ omegaListN V ul i = x)
    · intro him
      rw [Set.mem_setOf_eq] at him
      obtain ⟨j, hj, hjx⟩ := him
      have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
      have hlt : j < ul.length := by omega
      rw [Set.mem_image]
      exact ⟨j, hlt, hjx⟩
  have hset2 : omegaListN V vl '' {j : ℕ | j < vl.length} =
      {omegaListN V vl i | i ∈ Finset.Icc 0 k} := by
    ext x
    constructor
    · intro him
      rw [Set.mem_image] at him
      obtain ⟨j, hj, hjx⟩ := him
      have hlt : j < vl.length := hj
      exact (⟨j, Finset.mem_Icc.mpr (by omega), hjx⟩ :
        ∃ i, i ∈ Finset.Icc 0 k ∧ omegaListN V vl i = x)
    · intro him
      rw [Set.mem_setOf_eq] at him
      obtain ⟨j, hj, hjx⟩ := him
      have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
      have hlt : j < vl.length := by omega
      rw [Set.mem_image]
      exact ⟨j, hlt, hjx⟩
  show convexHull ℝ (omegaListN V ul '' {j : ℕ | j < ul.length})
      = convexHull ℝ (omegaListN V vl '' {j : ℕ | j < vl.length}) ↔
    {omegaListN V ul i | i ∈ Finset.Icc 0 k} =
      {omegaListN V vl i | i ∈ Finset.Icc 0 k}
  rw [hset1, hset2]
  exact CONVEX_HULL_EQ_EQ_SET_EQ _ _
    (AFFINE_INDEPENDENT_OMEGA_LIST_N V ul k hV hb1 hl1)
    (AFFINE_INDEPENDENT_OMEGA_LIST_N V vl k hV hb2 hl2)

/-- HL `NUM_FINITE_IMP_MAX_EXISTS` (Rogers.hl:9409). -/
theorem NUM_FINITE_IMP_MAX_EXISTS (K : Set ℕ) (hK : K.Finite) (hne : K ≠ ∅) :
    ∃ m ∈ K, ∀ j ∈ K, j ≤ m := by
  have hne' : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image K id hK hne'
  exact ⟨m, hm, fun j hj => by simpa using hmax j hj⟩

/-- HL `NOT_ID_IMP_LISTS_NOT_EQ` (Rogers.hl:9450). ENCODING-FIX (SF item 23,
2026-09-30, user-approved batch A): the former "unprovable as encoded" note is
resolved by adding `hfix` — the complement-fixing conjunct of HL's `permutes`
(Library/permutations.ml:9) that the weak pointwise-on-set
`PackingAuto2.permutes` lacks (see the `PERMUTES_TRIVIAL` encoding note in
PackingAuto5; sweep report docs/encoding-risk-sweep.md §2.1 C2-1, probe
P1-P3). With `hfix` the statement matches the HOL original; the proof body
stays `sorry` (GIANT, later wave). -/
theorem NOT_ID_IMP_LISTS_NOT_EQ (ul : List V3) (p : Equiv.Perm ℕ) (k : ℕ)
    (hlen : ul.length = k + 1) (hcard : Nat.card (setOfList ul) = k + 1)
    (hperm : permutes p (Set.Icc 0 k))
    (hfix : ∀ j : ℕ, k < j → p j = j) (hpid : ¬ (p = Equiv.refl ℕ)) :
    ¬ (ul = leftActionList p ul) := by
  sorry

/-- HL `NOT_ID_IMP_EXISTS_MAX_EQ_TRUNCATE_SIMPLEX` (Rogers.hl:9490).
ENCODING-FIX (SF item 24, 2026-09-30, user-approved batch A): same shape as
`NOT_ID_IMP_LISTS_NOT_EQ` — complement-fixing `hfix` added (sweep report
docs/encoding-risk-sweep.md §2.1 C2-2, same probe P1-P3 counterexample
engine); with `hfix` the statement matches the HOL original; proof body
`sorry` (GIANT, later wave). -/
theorem NOT_ID_IMP_EXISTS_MAX_EQ_TRUNCATE_SIMPLEX (ul : List V3)
    (p : Equiv.Perm ℕ) (k : ℕ) (hlen : ul.length = k + 1)
    (hcard : Nat.card (setOfList ul) = k + 1)
    (hperm : permutes p (Set.Icc 0 k))
    (hfix : ∀ j : ℕ, k < j → p j = j) (hpid : ¬ (p = Equiv.refl ℕ)) :
    ¬ (hdV ul = hdV (leftActionList p ul)) ∨
      ∃ j : ℕ, j < k ∧
        truncateSimplex j ul = truncateSimplex j (leftActionList p ul) ∧
        ¬ ((ul.getD (j + 1) default) = ((leftActionList p ul).getD (j + 1) default)) := by
  sorry

/-- HL `KSOQKWL` (Rogers.hl:9588): Rogers uniqueness forces the identity.
ENCODING-FIX (SF15 / proposal 19', 2026-09-30, user-approved batch A):
`hpout` added — the complement-fixing conjunct of HL's `permutes`
(Library/permutations.ml:9); with it the statement matches the HOL original
(per docs/statement-fix-proposals-patches/15-KSOQKWL.patch). Proof body
stays `sorry` (GIANT Rogers uniqueness chain). Consumer linkage: the call
`KSOQKWL V ul p k hP hbar hl2 hperm hrog` in
`PackingConcl.KSOQKWL_concl_discharged` predates the extra argument and is
to be re-threaded together with SF item 25 (the
`PackingAuto2.KSOQKWL_concl` twin). -/
theorem KSOQKWL (V : Set V3) (ul : List V3) (p : Equiv.Perm ℕ) (k : ℕ)
    (hV : Packing V) (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2)
    (hperm : permutes p (Set.Icc 0 k))
    (hpout : ∀ x : ℕ, k < x → p x = x)
    (hrog : rogers V ul = rogers V (leftActionList p ul)) :
    p = Equiv.refl ℕ := by
  sorry

/-- HL `IVFICRK` (Rogers.hl:9929): explicit bijection giving the action of a
permutation on the list with one element dropped. -/
theorem IVFICRK {A : Type} [Inhabited A] (k : ℕ) :
    ∃ g : ℕ × Equiv.Perm ℕ → Equiv.Perm ℕ,
      Set.BijOn g {q : ℕ × Equiv.Perm ℕ | q.1 ∈ Set.Icc 0 (k + 1) ∧
          permutes q.2 (Set.Icc 0 k)}
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k + 1))} ∧
      ∀ (ul : List A) (i : ℕ) (σ : Equiv.Perm ℕ) (j : ℕ), ul.length = k + 2 →
        j ≤ k → i ∈ Set.Icc 0 (k + 1) → permutes σ (Set.Icc 0 k) →
          (leftActionList (g (i, σ)) ul).getD j default =
            (leftActionList σ (dropIth ul i)).getD j default := by
  sorry

/-- HL `IVFICRK_real3` (Rogers.hl:10230): the `real^3` instance. -/
theorem IVFICRK_real3 (k : ℕ) :
    ∃ g : ℕ × Equiv.Perm ℕ → Equiv.Perm ℕ,
      Set.BijOn g {q : ℕ × Equiv.Perm ℕ | q.1 ∈ Set.Icc 0 (k + 1) ∧
          permutes q.2 (Set.Icc 0 k)}
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (k + 1))} ∧
      ∀ (ul : List V3) (i : ℕ) (σ : Equiv.Perm ℕ) (j : ℕ), ul.length = k + 2 →
        j ≤ k → i ∈ Set.Icc 0 (k + 1) → permutes σ (Set.Icc 0 k) →
          (leftActionList (g (i, σ)) ul).getD j default =
            (leftActionList σ (dropIth ul i)).getD j default :=
  IVFICRK (A := V3) k

/-- HL `WQPRRDY` (Rogers.hl:10534) — CAPSTONE / main Rogers bound: the hull
of a barfixed simplex is the union of its Rogers simplices over all vertex
orderings. -/
theorem WQPRRDY (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    convexHull ℝ (setOfList ul) =
      ⋃₀ ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p ul)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 k)}) := by
  sorry

end Kepler.Text
