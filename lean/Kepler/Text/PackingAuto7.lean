/-
Packing chapter, part B (Rogers.hl, part 2 of 2).

HOL source: Flyspeck `scripts/packing/Rogers.hl` (10872 lines, 111 all-caps
theorems + 13 lowercase `_lemma`s). PART BOUNDARY: this file ports the LAST
56 all-caps theorems, `ANGLE_GT_PI2` (Rogers.hl:5292, all-caps thm 56 of 111)
through `WQPRRDY` (Rogers.hl:10534, all-caps thm 111 of 111), plus the six
lowercase helpers interleaved in that line range (`ANGLE_SUM_lemma`,
`NEIGHBORHOOD_lemma`, `YIFVQDV_lemma_aff_dim`, `KSOQKWL_lemma0/lemma1` —
62 items total). Part A (thms 1..55, Rogers.hl:35..5252: face kit, GLTVHUM,
DUUNHOR, circumcenter kit, MHFTTZN, XYOFCGX_lemma0/1/2) is ported in
`PackingAuto6.lean`, which this file now imports (PA7-XYOFCGX wave,
2026-10-08: PA6 is delivered and its olean is stable; the four part-B
statements PA7 used to duplicate — `ARCV_GT_PI2`, `ANGLE_GT_PI2`,
`AZIM_COMPL_EXT`, `AZIM_EQ_SYM` — are dropped from this file, being
byte-identical to PA6's, so every downstream name still resolves with the
same type). The private `_p7` copies below remain for statements PA6 keeps
private.

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
import Kepler.Text.PackingAuto6
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

/-- HL `ARCV_ANGLE`: `arcV u v w` is the Euclidean angle at `u`. -/
private theorem p7_arcV_eq_angle (u v w : V3) :
    arcV u v w = EuclideanGeometry.angle v u w := by
  rw [arcV, EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, InnerProductGeometry.angle,
    inner_eq_dot, ← dist_eq_norm, ← dist_eq_norm]
  simp only [WithLp.ofLp_sub]

/-- HL `DIHV_GT_PI2` (Rogers.hl:6370). -/
theorem DIHV_GT_PI2 (v w x y : V3) :
    Real.pi / 2 < dihV v w x y ↔ Real.cos (dihV v w x y) < 0 := by
  unfold dihV
  exact p7_arcV_pi2 0 _ _

-- (`ANGLE_GT_PI2`, `ARCV_GT_PI2`, `AZIM_COMPL_EXT`, `AZIM_EQ_SYM` live in
-- `PackingAuto6` byte-identically; PA7 no longer duplicates them.)

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

/-- Nondegenerate azimuth forces both points off the `0p` axis (junk case of
`azim`'s definition: a collinear argument zeroes the azimuth). -/
private theorem p7_ncol_of_azim_pos {p z w : V3} (h : 0 < azim 0 p z w) :
    ¬ Collinear3 0 p z ∧ ¬ Collinear3 0 p w := by
  constructor
  · intro hcol
    unfold azim at h
    rw [if_pos (Or.inl hcol)] at h
    exact lt_irrefl 0 h
  · intro hcol
    unfold azim at h
    rw [if_pos (Or.inr hcol)] at h
    exact lt_irrefl 0 h

/-- Phase composition: azimuths around a common apex/axis add on the unit
circle. With the frame aligned to the axis, `azim_frame_spec` exhibits each
point's polar phase; chaining the three pairwise phase representations and
cancelling the common phases gives `e^{i(θ_ab+θ_bc)} = e^{i θ_ac}` (the
exponential form of the azim additivity behind Rogers.hl:5901). -/
private theorem p7_azim_exp_comp {p a b c : V3} (hp : p ≠ 0)
    (ha : ¬ Collinear3 0 p a) (hb : ¬ Collinear3 0 p b) (hc : ¬ Collinear3 0 p c) :
    Complex.exp (((azim 0 p a b + azim 0 p b c : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((azim 0 p a c : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (p - 0) (sub_ne_zero.mpr hp)
  have hax : (p - 0 : V3) = dist p 0 • f3 := by rw [dist_eq_norm]; exact halign
  obtain ⟨ψ₁, r₁, s₁, hr₁, hs₁, hz₁, hzz₁⟩ := azim_frame_spec ha hb hon hax hp
  obtain ⟨ψ₂, r₂, s₂, hr₂, hs₂, hz₂, hzz₂⟩ := azim_frame_spec hb hc hon hax hp
  obtain ⟨ψ₃, r₃, s₃, hr₃, hs₃, hz₃, hzz₃⟩ := azim_frame_spec ha hc hon hax hp
  -- the two representations of `a` share the phase
  have hA : Complex.exp (((ψ₁ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ₃ : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hr₁ hr₃ (hz₁.symm.trans hz₃)
  -- the two representations of `b`
  have hB : Complex.exp ((((ψ₁ + azim 0 p a b : ℝ) : ℂ)) * Complex.I)
      = Complex.exp (((ψ₂ : ℝ) : ℂ) * Complex.I) :=
    exp_pos_mul_eq hs₁ hr₂ (hzz₁.symm.trans hz₂)
  -- the two representations of `c`
  have hC : Complex.exp ((((ψ₂ + azim 0 p b c : ℝ) : ℂ)) * Complex.I)
      = Complex.exp ((((ψ₃ + azim 0 p a c : ℝ) : ℂ)) * Complex.I) :=
    exp_pos_mul_eq hs₂ hs₃ (hzz₂.symm.trans hzz₃)
  have h1 : Complex.exp (((ψ₂ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ₁ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim 0 p a b : ℝ) : ℂ) * Complex.I) := by
    rw [← hB]
    exact exp_add_I ψ₁ (azim 0 p a b)
  have h2 : Complex.exp (((ψ₃ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim 0 p a c : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ₂ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim 0 p b c : ℝ) : ℂ) * Complex.I) := by
    rw [← exp_add_I ψ₃ (azim 0 p a c), ← hC]
    exact exp_add_I ψ₂ (azim 0 p b c)
  have hkey : Complex.exp (((ψ₃ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim 0 p a b + azim 0 p b c : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((ψ₃ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim 0 p a c : ℝ) : ℂ) * Complex.I) := by
    calc Complex.exp (((ψ₃ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim 0 p a b + azim 0 p b c : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((ψ₃ : ℝ) : ℂ) * Complex.I)
            * (Complex.exp (((azim 0 p a b : ℝ) : ℂ) * Complex.I)
              * Complex.exp (((azim 0 p b c : ℝ) : ℂ) * Complex.I)) :=
          by rw [exp_add_I]
      _ = Complex.exp (((ψ₁ : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((azim 0 p a b : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((azim 0 p b c : ℝ) : ℂ) * Complex.I) := by
          rw [hA]; ring
      _ = Complex.exp (((ψ₂ : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((azim 0 p b c : ℝ) : ℂ) * Complex.I) := by
          rw [← h1]
      _ = Complex.exp (((ψ₃ : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((azim 0 p a c : ℝ) : ℂ) * Complex.I) := h2.symm
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) hkey

/-- The resolved form: with `θ z = azim 0 p e₀ z`, every azimuth is the cyclic
θ-difference (values in `[0,2π)`, so the wrap branch adds `2π`). -/
private theorem p7_theta_comp {p e₀ a c : V3} (hp : p ≠ 0)
    (he : ¬ Collinear3 0 p e₀) (ha : ¬ Collinear3 0 p a) (hc : ¬ Collinear3 0 p c) :
    azim 0 p a c = azim 0 p e₀ c - azim 0 p e₀ a ∨
      azim 0 p a c = azim 0 p e₀ c - azim 0 p e₀ a + 2 * Real.pi := by
  have hcomp := p7_azim_exp_comp hp he ha hc
  have h3 : Complex.exp (((azim 0 p a c : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((((azim 0 p e₀ c - azim 0 p e₀ a : ℝ) : ℂ)) * Complex.I) := by
    have harg : ((azim 0 p e₀ a + (azim 0 p e₀ c - azim 0 p e₀ a) : ℝ) : ℂ)
        = ((azim 0 p e₀ c : ℝ) : ℂ) := by
      push_cast; ring
    have he1 : Complex.exp (((azim 0 p e₀ a : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((azim 0 p a c : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((azim 0 p e₀ c : ℝ) : ℂ) * Complex.I) := by
      rw [← exp_add_I]; exact hcomp
    have he2 : Complex.exp (((azim 0 p e₀ a : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((((azim 0 p e₀ c - azim 0 p e₀ a : ℝ) : ℂ)) * Complex.I)
        = Complex.exp (((azim 0 p e₀ c : ℝ) : ℂ) * Complex.I) := by
      rw [← exp_add_I, harg]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) (he1.trans he2.symm)
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h3
  -- lift the complex phase equation to a real equation
  have hkR : (azim 0 p a c : ℝ)
      = azim 0 p e₀ c - azim 0 p e₀ a + (k : ℝ) * (2 * Real.pi) := by
    have h2 : ((azim 0 p a c : ℝ) : ℂ) * Complex.I
        = (((azim 0 p e₀ c - azim 0 p e₀ a + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I := by
      rw [hk]; push_cast; ring
    have := mul_right_cancel₀ Complex.I_ne_zero h2
    exact_mod_cast this
  have h2pi : (0:ℝ) < 2 * Real.pi := by positivity
  have hrng : 0 ≤ azim 0 p a c ∧ azim 0 p a c < 2 * Real.pi :=
    ⟨azim_nonneg 0 p a c, azim_lt_two_pi 0 p a c⟩
  have hδlo : -(2 * Real.pi) < azim 0 p e₀ c - azim 0 p e₀ a := by
    linarith [azim_nonneg 0 p e₀ c, azim_lt_two_pi 0 p e₀ a]
  have hδhi : azim 0 p e₀ c - azim 0 p e₀ a < 2 * Real.pi := by
    linarith [azim_nonneg 0 p e₀ a, azim_lt_two_pi 0 p e₀ c]
  rcases Int.lt_trichotomy k 0 with hk0 | hk1 | hk2
  · exfalso
    have hle : ((k:ℤ) : ℝ) ≤ -1 := by
      have := (by omega : (k:ℤ) ≤ -1); exact_mod_cast this
    have hprod : ((k:ℤ) : ℝ) * (2 * Real.pi) ≤ -(2 * Real.pi) :=
      by linarith [mul_le_mul_of_nonneg_right hle h2pi.le]
    linarith [hkR, hprod, hδlo, hrng.1]
  · refine Or.inl ?_
    rw [hk1, Int.cast_zero, zero_mul] at hkR
    linarith
  · rcases Int.lt_trichotomy k 1 with hklt | hkeq | hkgt
    · exfalso
      omega
    · refine Or.inr ?_
      rw [hkeq, Int.cast_one, one_mul] at hkR
      linarith
    · exfalso
      have hge : ((k:ℤ) : ℝ) ≥ 2 := by
        have := (by omega : (k:ℤ) ≥ 2); exact_mod_cast this
      have hprod : ((k:ℤ) : ℝ) * (2 * Real.pi) ≥ 2 * (2 * Real.pi) :=
        by linarith [mul_le_mul_of_nonneg_right hge h2pi.le]
      linarith [hkR, hprod, hδlo, hrng.2]

/-- HL `ANGLE_SUM_lemma` (Rogers.hl:5901): the cyclic ordering pairing each
point to its azim-successor realizes the full angle sum `2π`.
Proof (direct θ-cycle, bypassing the HOL FAN/hypermap route): rank the points
by `θ z = azim 0 p e₀ z`, map each point to its θ-successor (θ-max wrapping to
the θ-min), and telescope the gaps around the circle. -/
theorem ANGLE_SUM_lemma (V : Set V3) (p : V3) (hfin : V.Finite)
    (hcard : 2 ≤ Nat.card V)
    (hazim : ∀ v w, v ∈ V → w ∈ V → v ≠ w → 0 < azim 0 p v w) :
    ∃ f : V3 → V3, (∀ x, x ∈ V → f x ∈ V ∧ x ≠ f x) ∧
      setSum V (fun x => azim 0 p x (f x)) = 2 * Real.pi := by
  classical
  -- finiteness bookkeeping
  set S := hfin.toFinset with hSdef
  haveI : Fintype ↥V := hfin.fintype
  have hcardF : Nat.card ↥V = S.card := by
    rw [Nat.card_eq_fintype_card]; exact (Set.Finite.card_toFinset hfin).symm
  have h2le : 2 ≤ S.card := by rw [← hcardF]; exact hcard
  have hne : S.Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    rw [h0, Finset.card_empty] at h2le
    omega
  have hmem : ∀ x ∈ S, x ∈ V := fun x hx => hfin.mem_toFinset.mp hx
  have hmem' : ∀ x ∈ V, x ∈ S := fun x hx => hfin.mem_toFinset.mpr hx
  -- two distinct points, per-point witness
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := Finset.one_lt_card.mp h2le
  have hother : ∀ z ∈ S, ∃ w ∈ S, w ≠ z := by
    intro z hz
    by_cases haz : a₀ = z
    · refine ⟨b₀, hb₀, ?_⟩
      intro hcon
      rw [haz] at hab₀
      exact hab₀ hcon.symm
    · exact ⟨a₀, ha₀, haz⟩
  -- every point of V is off the 0p axis, and so is p
  have hncol : ∀ z ∈ S, ¬ Collinear3 0 p z := by
    intro z hz
    obtain ⟨w, hwS, hwz⟩ := hother z hz
    exact (p7_ncol_of_azim_pos (hazim z w (hmem z hz) (hmem w hwS) hwz.symm)).1
  obtain ⟨e₀, he₀S⟩ := hne
  have he₀ : ¬ Collinear3 0 p e₀ := hncol e₀ he₀S
  have hp : p ≠ 0 := by
    intro h0
    rw [h0] at he₀
    exact he₀ (by
      show Collinear ℝ ({(0:V3), 0, e₀} : Set V3)
      have h2 : ({(0:V3), 0, e₀} : Set V3) = {(0:V3), e₀} := by ext q; simp
      rw [h2]
      exact collinear_pair ℝ (0:V3) e₀)
  -- θ-coordinates and their injectivity on V
  set theta : V3 → ℝ := fun z => azim 0 p e₀ z with htheta
  have hthetaeq : ∀ z : V3, theta z = azim 0 p e₀ z := fun _ => rfl
  have hinj : ∀ x ∈ S, ∀ y ∈ S, theta x = theta y → x = y := by
    intro x hx y hy hθ
    rw [hthetaeq] at hθ
    by_contra hne2
    have hpos := hazim x y (hmem x hx) (hmem y hy) hne2
    have hlt := azim_lt_two_pi 0 p x y
    rcases p7_theta_comp hp he₀ (hncol x hx) (hncol y hy) with h | h
    · rw [hθ] at h; linarith
    · rw [hθ] at h; linarith
  -- θ-min and θ-max values and realizing points
  have himgne : (S.image theta).Nonempty := ⟨theta e₀, Finset.mem_image.mpr ⟨e₀, he₀S, rfl⟩⟩
  obtain ⟨tMax, htMaxmem, htMaxle⟩ : ∃ t, t ∈ S.image theta ∧
      ∀ t' ∈ S.image theta, t' ≤ t :=
    ⟨(S.image theta).max' himgne, (S.image theta).max'_mem himgne,
      fun t' ht' => Finset.le_max' (S.image theta) t' ht'⟩
  obtain ⟨tMin, htMinmem, htMinge⟩ : ∃ t, t ∈ S.image theta ∧
      ∀ t' ∈ S.image theta, t ≤ t' :=
    ⟨(S.image theta).min' himgne, (S.image theta).min'_mem himgne,
      fun t' ht' => Finset.min'_le (S.image theta) t' ht'⟩
  obtain ⟨xM, hxMS, hxMθ⟩ := Finset.mem_image.mp htMaxmem
  obtain ⟨yM, hyMS, hyMθ⟩ := Finset.mem_image.mp htMinmem
  have hxMax : ∀ w ∈ S, theta w ≤ tMax := by
    intro w hw; exact htMaxle (theta w) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  have hyMin : ∀ w ∈ S, tMin ≤ theta w := by
    intro w hw; exact htMinge (theta w) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  have hθne : theta a₀ ≠ theta b₀ := fun hh => hab₀ (hinj a₀ ha₀ b₀ hb₀ hh)
  have hstrict : tMin < tMax := by
    rcases lt_trichotomy (theta a₀) (theta b₀) with h | h | h
    · linarith [hyMin a₀ ha₀, h, hxMax b₀ hb₀]
    · exact absurd h hθne
    · linarith [hyMin b₀ hb₀, h, hxMax a₀ ha₀]
  -- the successor function: θ-successor, with the θ-max wrapping to the θ-min
  set f : V3 → V3 := fun x =>
    if theta x = tMax then yM else
      Classical.epsilon (fun w => w ∈ S ∧ theta x < theta w ∧
        ∀ w₁ ∈ S, theta x < theta w₁ → theta w ≤ theta w₁) with hfdef
  have hfmax : f xM = yM := by simp only [hfdef]; exact if_pos hxMθ
  have hfA : ∀ x ∈ S, theta x ≠ tMax →
      f x ∈ S ∧ theta x < theta (f x) ∧ ∀ w₁ ∈ S, theta x < theta w₁ → theta (f x) ≤ theta w₁ := by
    intro x hx hne
    simp only [hfdef, if_neg hne]
    -- the upper set {w ∈ S | theta x < theta w} is finite nonempty, take its θ-min
    have hUne : ((S.filter (fun w => theta x < theta w)).image theta).Nonempty :=
      ⟨theta xM, Finset.mem_image.mpr ⟨xM, Finset.mem_filter.mpr ⟨hxMS, by
        rw [hxMθ]; exact lt_of_le_of_ne (hxMax x hx) hne⟩, rfl⟩⟩
    obtain ⟨u, huU, huθ⟩ := Finset.mem_image.mp
      (((S.filter (fun w => theta x < theta w)).image theta).min'_mem hUne)
    have humin : ∀ t' ∈ (S.filter (fun w => theta x < theta w)).image theta,
        theta u ≤ t' := by
      intro t' ht'
      rw [huθ]
      exact Finset.min'_le
        ((S.filter (fun w => theta x < theta w)).image theta) t' ht'
    have huF : u ∈ S ∧ theta x < theta u := Finset.mem_filter.mp huU
    have hmin1 : ∀ w₁ ∈ S, theta x < theta w₁ → theta u ≤ theta w₁ := fun w₁ hw₁ hlt =>
      humin (theta w₁) (Finset.mem_image.mpr ⟨w₁, Finset.mem_filter.mpr ⟨hw₁, hlt⟩, rfl⟩)
    exact Classical.epsilon_spec (p := fun w => w ∈ S ∧ theta x < theta w ∧
      ∀ w₁ ∈ S, theta x < theta w₁ → theta w ≤ theta w₁) ⟨u, huF.1, huF.2, hmin1⟩
  have hfmem : ∀ x ∈ S, f x ∈ S := by
    intro x hx
    by_cases hne : theta x = tMax
    · simp only [hfdef, if_pos hne]; exact hyMS
    · exact (hfA x hx hne).1
  have hfne : ∀ x ∈ S, x ≠ f x := by
    intro x hx
    by_cases hxm : x = xM
    · rw [hxm, hfmax]
      intro heq
      exact absurd (by rw [← hyMθ, ← heq, ← hxMθ]) hstrict.ne
    · have hlt : theta x < theta (f x) :=
        (hfA x hx (fun hh => hxm (hinj x hx xM hxMS (hh.trans hxMθ.symm)))).2.1
      intro hcon
      rw [← hcon] at hlt
      exact lt_irrefl _ hlt
  refine ⟨f, fun x hx => ⟨hmem _ (hfmem x (hmem' x hx)), hfne x (hmem' x hx)⟩, ?_⟩
  unfold setSum
  rw [dif_pos hfin]
  -- split off the θ-max point
  have hsplit := Finset.sum_erase_add S (fun x => azim 0 p x (f x)) hxMS
  rw [← hsplit, hfmax]
  -- inner edges: azimuth = forward θ-gap
  have hxne : ∀ x ∈ S.erase xM, theta x ≠ tMax := by
    intro x hx
    have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
    intro hh
    exact (Finset.mem_erase.mp hx).1 (hinj x hxS xM hxMS (hh.trans hxMθ.symm))
  have hxAB : ∀ x ∈ S.erase xM, theta x < theta (f x) := by
    intro x hx; exact (hfA x ((Finset.mem_erase.mp hx).2) (hxne x hx)).2.1
  have hinner : ∀ x ∈ S.erase xM, azim 0 p x (f x) = theta (f x) - theta x := by
    intro x hx
    have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
    have h2 := hxAB x hx
    rcases p7_theta_comp hp he₀ (hncol x hxS) (hncol (f x) (hfmem x hxS)) with h | h
    · exact h
    · exfalso
      linarith [h, azim_lt_two_pi 0 p x (f x), h2]
  rw [Finset.sum_congr rfl fun x hx => hinner x hx]
  -- the successor map restricts to a bijection `S.erase xM → S.erase yM`
  have hfB : ∀ x ∈ S.erase xM, f x ∈ S.erase yM := by
    intro x hx
    have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
    have hlt := hxAB x hx
    refine Finset.mem_erase.mpr ⟨fun heq => ?_, hfmem x hxS⟩
    rw [heq, hyMθ] at hlt
    linarith [hyMin x hxS]
  have hinjA : ∀ x₁ ∈ S.erase xM, ∀ x₂ ∈ S.erase xM, f x₁ = f x₂ → x₁ = x₂ := by
    intro x₁ h₁ x₂ h₂ heq
    by_contra hne2
    have hx₁ : x₁ ∈ S := (Finset.mem_erase.mp h₁).2
    have hx₂ : x₂ ∈ S := (Finset.mem_erase.mp h₂).2
    have hmin₁ : ∀ w₁ ∈ S, theta x₁ < theta w₁ → theta (f x₂) ≤ theta w₁ := by
      rw [← heq]; exact (hfA x₁ hx₁ (hxne x₁ h₁)).2.2
    have hmin₂ : ∀ w₁ ∈ S, theta x₂ < theta w₁ → theta (f x₁) ≤ theta w₁ := by
      rw [heq]; exact (hfA x₂ hx₂ (hxne x₂ h₂)).2.2
    rcases lt_trichotomy (theta x₁) (theta x₂) with h | h | h
    · exact absurd (hxAB x₂ h₂) (not_lt.mpr (hmin₁ x₂ hx₂ h))
    · exact hne2 (hinj x₁ hx₁ x₂ hx₂ h)
    · exact absurd (hxAB x₁ h₁) (not_lt.mpr (hmin₂ x₁ hx₁ h))
  have hbij : (S.erase xM).sum (fun x => theta (f x))
      = (S.erase yM).sum theta := by
    refine Finset.sum_bij (fun x _ => f x) hfB hinjA ?_ (fun _ _ => rfl)
    intro y hy
    have hyS : y ∈ S := (Finset.mem_erase.mp hy).2
    have hyNe : y ≠ yM := (Finset.mem_erase.mp hy).1
    have hyθ : theta y ≠ tMin := fun hh =>
      hyNe (hinj y hyS yM hyMS (hh.trans hyMθ.symm))
    -- the θ-predecessor of `y`: θ-max among the points strictly below θ y
    obtain ⟨w₀, hw₀T⟩ : (S.filter (fun w => theta w < theta y)).Nonempty := ⟨yM,
      Finset.mem_filter.mpr ⟨hyMS, by
        rw [hyMθ]
        exact lt_of_le_of_ne (hyMin y hyS) (fun hh => hyθ hh.symm)⟩⟩
    have hTimgne : ((S.filter (fun w => theta w < theta y)).image theta).Nonempty :=
      ⟨theta w₀, Finset.mem_image.mpr ⟨w₀, hw₀T, rfl⟩⟩
    obtain ⟨u, huTimg, huTmax⟩ : ∃ u ∈ (S.filter (fun w => theta w < theta y)).image theta,
        ∀ u' ∈ (S.filter (fun w => theta w < theta y)).image theta, u' ≤ u :=
      ⟨((S.filter (fun w => theta w < theta y)).image theta).max' hTimgne,
        ((S.filter (fun w => theta w < theta y)).image theta).max'_mem hTimgne,
        fun t' ht' => Finset.le_max' ((S.filter (fun w => theta w < theta y)).image theta) t' ht'⟩
    obtain ⟨x, hxT, hxθu⟩ := Finset.mem_image.mp huTimg
    have hxT' : x ∈ S ∧ theta x < theta y := Finset.mem_filter.mp hxT
    have hxMne : x ≠ xM := by
      intro heq
      rw [heq, hxMθ] at hxT'
      exact absurd hxT'.2 (not_lt.2 (hxMax y hyS))
    have hxtMax : theta x ≠ tMax := fun hh =>
      hxMne (hinj x hxT'.1 xM hxMS (hh.trans hxMθ.symm))
    have hxABx : theta x < theta (f x) := (hfA x hxT'.1 hxtMax).2.1
    have hxmin : ∀ w₁ ∈ S, theta x < theta w₁ → theta (f x) ≤ theta w₁ :=
      (hfA x hxT'.1 hxtMax).2.2
    have hle : theta (f x) ≤ theta y := hxmin y hyS hxT'.2
    have heqθ : theta (f x) = theta y := by
      rcases lt_or_eq_of_le hle with h | h
      · exfalso
        have hfT : f x ∈ S.filter (fun w => theta w < theta y) :=
          Finset.mem_filter.mpr ⟨hfmem x hxT'.1, h⟩
        have hmax := huTmax (theta (f x)) (Finset.mem_image.mpr ⟨f x, hfT, rfl⟩)
        rw [← hxθu] at hmax
        linarith [hmax, hxABx]
      · exact h
    refine ⟨x, Finset.mem_erase.mpr ⟨hxMne, hxT'.1⟩,
      hinj (f x) (hfmem x hxT'.1) y hyS heqθ⟩
  -- telescoping around the circle
  have hAsplit := Finset.sum_erase_add S theta hxMS
  have hBsplit := Finset.sum_erase_add S theta hyMS
  have hA2 : (S.erase xM).sum theta = S.sum theta - theta xM := by
    rw [← hAsplit]; ring
  have hB2 : (S.erase yM).sum theta = S.sum theta - theta yM := by
    rw [← hBsplit]; ring
  have hsub : (S.erase xM).sum (fun x => theta (f x) - theta x)
      + (S.erase xM).sum theta
      = (S.erase xM).sum (fun x => theta (f x)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => sub_add_cancel _ _
  have hsub2 : (S.erase xM).sum (fun x => theta (f x) - theta x)
      = (S.erase xM).sum (fun x => theta (f x)) - (S.erase xM).sum theta := by
    linarith [hsub]
  rw [hsub2, hbij, hB2, hA2]
  -- the wrap edge: azimuth from the θ-max to the θ-min
  have hxMθa : azim 0 p e₀ xM = tMax := hthetaeq xM ▸ hxMθ
  have hyMθa : azim 0 p e₀ yM = tMin := hthetaeq yM ▸ hyMθ
  have hwrap : azim 0 p xM yM = theta yM - theta xM + 2 * Real.pi := by
    rcases p7_theta_comp hp he₀ (hncol xM hxMS) (hncol yM hyMS) with h | h
    · exfalso
      have h1 : azim 0 p e₀ yM - azim 0 p e₀ xM < 0 := by
        rw [hyMθa, hxMθa]; linarith
      linarith [h, h1, azim_nonneg 0 p xM yM]
    · exact h
  rw [hwrap, hyMθ, hxMθ]
  linarith


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
  by_cases hge : Real.pi ≤ azim v w x y
  · have hdih : dihV v w x y ≤ Real.pi := by
      rw [dihV, arcV]
      exact Real.arccos_le_pi _
    rw [azim_dihv_compl h1 h2 hge]
    linarith [hdih, Real.pi_pos]
  · exact (azim_dihv_same h1 h2 (lt_of_not_ge hge)).symm.le

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
  have hnn : (0:ℝ) < n ⬝ᵥ n := by
    have hnsq : ‖(n:V3)‖ ^ 2 = n ⬝ᵥ n := norm_sq_eq_dot n
    rw [← hnsq]; positivity
  have hivn : inner ℝ v n = 0 := by
    rw [real_inner_comm, inner_eq_dot]
    exact h1
  have hiwn : inner ℝ w n = 0 := by
    rw [real_inner_comm, inner_eq_dot]
    exact h2
  have hcomm : (v ⬝ᵥ n) = (n ⬝ᵥ v) := dotProduct_comm v.ofLp n.ofLp
  have hcomm' : (w ⬝ᵥ n) = (n ⬝ᵥ w) := dotProduct_comm w.ofLp n.ofLp
  -- the orthogonal projections of `v` and `w` onto the plane perpendicular to `n`
  have hvap : ((n ⬝ᵥ n : ℝ) • v - (v ⬝ᵥ n) • n : V3) = (n ⬝ᵥ n) • v := by
    rw [hcomm, h1, zero_smul, sub_zero]
  have hvbp : ((n ⬝ᵥ n : ℝ) • w - (w ⬝ᵥ n) • n : V3) = (n ⬝ᵥ n) • w := by
    rw [hcomm', h2, zero_smul, sub_zero]
  have hvapne : ((n ⬝ᵥ n : ℝ) • v : V3) ≠ 0 := by
    simp only [smul_eq_zero, ne_eq, hnn.ne', hv, or_false, false_and, not_false_iff]
  have hvbpne : ((n ⬝ᵥ n : ℝ) • w : V3) ≠ 0 := by
    simp only [smul_eq_zero, ne_eq, hnn.ne', hw, or_false, false_and, not_false_iff]
  have h2' : dihV 0 n v w = Real.arccos (inner ℝ v w / (dist v 0 * dist w 0)) := by
    rw [dihV]
    simp only [sub_zero]
    rw [hvap, hvbp, p7_arcV_eq_angle, EuclideanGeometry.angle, vsub_eq_sub,
      vsub_eq_sub, sub_zero, sub_zero, InnerProductGeometry.angle,
      real_inner_smul_left, real_inner_smul_right, norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_pos hnn, ← dist_zero_right]
    congr 1
    field_simp [hnn.ne', (dist_pos.mpr hv).ne', (dist_pos.mpr hw).ne']
    have hdd : dist (n ⬝ᵥ n) 0 = (n ⬝ᵥ n : ℝ) := by
      rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hnn]
    rw [hdd]
    ring
  have h1' : EuclideanGeometry.angle v 0 w =
      Real.arccos (inner ℝ v w / (dist v 0 * dist w 0)) := by
    rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, sub_zero, sub_zero,
      InnerProductGeometry.angle, ← dist_zero_right, ← dist_zero_right]
  rw [h1', h2']

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

/-! ## XYOFCGX support kit (bridges; HL proves these inline) -/

/-- Cosine of `arcV u x y` (junk-free form, needs the two distances nonzero). -/
private theorem p7_cos_arcV (u x y : V3) (hxu : x ≠ u) (hyu : y ≠ u) :
    Real.cos (arcV u x y) = ((x - u) ⬝ᵥ (y - u)) / (dist x u * dist y u) := by
  have hpos : (0:ℝ) < dist x u * dist y u :=
    mul_pos (dist_pos.mpr hxu) (dist_pos.mpr hyu)
  have hcs : |((x - u : V3)) ⬝ᵥ (y - u)| ≤ dist x u * dist y u := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (x - u) (y - u)
    rw [Real.norm_eq_abs] at h
    rw [inner_eq_dot] at h
    rw [dist_eq_norm]
    exact h
  have hb1 : -(1:ℝ) ≤ ((x - u) ⬝ᵥ (y - u)) / (dist x u * dist y u) := by
    rw [le_div_iff₀ hpos]
    have h2 := (abs_le.mp hcs).1
    linarith
  have hb2 : ((x - u) ⬝ᵥ (y - u)) / (dist x u * dist y u) ≤ 1 := by
    rw [div_le_iff₀ hpos]
    have h2 := (abs_le.mp hcs).2
    linarith
  rw [arcV, Real.cos_arccos hb1 hb2]

/-- Squaring against `√2` (used throughout the XYOFCGX family). -/
private theorem p7_sq_lt_two {r : ℝ} (hr0 : 0 ≤ r) (hrlt : r < Real.sqrt 2) : r ^ 2 < 2 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have := sq_lt_sq' (by linarith [hr0, Real.sqrt_nonneg 2]) hrlt
  rwa [h2] at this

/-- Pi-level identity behind the `RLXWSTK` step of `XYOFCGX_4_0`: expanding
the dot of the two projected vectors (coercion-free at `Fin 3 → ℝ`, so the
`dotProduct` lemmas apply syntactically). -/
private theorem p7_dot_expand (x' y' v' : Fin 3 → ℝ) :
    ((v' ⬝ᵥ v') • x' - (x' ⬝ᵥ v') • v') ⬝ᵥ ((v' ⬝ᵥ v') • y' - (y' ⬝ᵥ v') • v')
        = (v' ⬝ᵥ v') * ((v' ⬝ᵥ v') * (x' ⬝ᵥ y') - (x' ⬝ᵥ v') * (y' ⬝ᵥ v')) := by
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

/-- A finite set of cardinality `3` is a triple of pairwise distinct points
(analogue of PA6's `CARD_1_IMP_SING` / `CARD_2_IMP_DOUBLE`). -/
private theorem p7_card_3_imp_triple {α : Type*} (s : Set α) (h1 : s.Finite)
    (h2 : Nat.card s = 3) :
    ∃ a b c : α, s = {a, b, c} ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  haveI := h1.fintype
  have hF : (h1.toFinset : Set α) = s := h1.coe_toFinset
  have hc : h1.toFinset.card = 3 := by
    have hct : h1.toFinset.card = Nat.card s := by
      rw [h1.card_toFinset, Nat.card_eq_fintype_card]
    omega
  have hpos : 0 < h1.toFinset.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have hmem : a ∈ s := by rw [← hF]; exact ha
  have hd : (↑(h1.toFinset.erase a) : Set α) = s \ ({a} : Set α) := by
    rw [Finset.coe_erase, hF]
  have h2' : Nat.card ↑(s \ ({a} : Set α)) = 2 := by
    rw [← hd, Nat.card_eq_fintype_card, ← Set.toFinset_card, Finset.toFinset_coe]
    have he := Finset.card_erase_of_mem ha
    omega
  obtain ⟨b, c, hSbc, hbc⟩ :=
    CARD_2_IMP_DOUBLE (s \ ({a} : Set α)) (h1.subset Set.sdiff_subset) h2'
  have hbS : b ∈ s \ ({a} : Set α) := by rw [hSbc]; simp
  have hba : b ≠ a := (Set.mem_sdiff_singleton.mp hbS).2
  have hcS : c ∈ s \ ({a} : Set α) := by rw [hSbc]; simp
  have hca : c ≠ a := (Set.mem_sdiff_singleton.mp hcS).2
  refine ⟨a, b, c, ?_, fun h => hba h.symm, fun h => hca h.symm, hbc⟩
  have hins : insert a (s \ ({a} : Set α)) = s := by
    rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hmem]
  rw [← hins, hSbc]

/-- If `0` lies in the affine hull of three points, a nonzero vector is
orthogonal to all three (the `LOWDIM_SUBSET_HYPERPLANE` route of the HOL
`XYOFCGX_3_0`, done by finrank arithmetic). -/
private theorem p7_exists_normal3 {a b c : V3}
    (h0 : (0:V3) ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3)) :
    ∃ n : V3, n ≠ 0 ∧ a ⬝ᵥ n = 0 ∧ b ⬝ᵥ n = 0 ∧ c ⬝ᵥ n = 0 := by
  classical
  set K : Submodule ℝ V3 := Submodule.span ℝ ({b - a, c - a} : Set V3) with hK
  have hmemBA : (b - a : V3) ∈ K := Submodule.subset_span (by simp)
  have hmemCA : (c - a : V3) ∈ K := Submodule.subset_span (by simp)
  have hKle : Module.finrank ℝ K ≤ 2 := by
    rcases eq_or_ne b c with hbc | hbc
    · have hK' : K = Submodule.span ℝ ({b - a} : Set V3) := by
        rw [hK]
        refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_mono ?_)
        · intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · simp
          · rw [hbc]
            simp
        · intro x hx
          simp only [Set.mem_singleton_iff] at hx
          simp [hx]
      rw [hK']
      have h := finrank_span_le_card (R := ℝ) (M := V3) ({b - a} : Set V3)
      rw [Set.toFinset_singleton, Finset.card_singleton] at h
      exact le_trans h (by norm_num)
    · have h := finrank_span_le_card (R := ℝ) (M := V3) ({b - a, c - a} : Set V3)
      rw [Set.toFinset_insert, Set.toFinset_singleton,
        Finset.card_insert_of_notMem (by simp [hbc])] at h
      exact le_trans h (by norm_num)
  -- every difference of two of `a b c` lies in `K`
  have hdiffs : ∀ p ∈ ({a, b, c} : Set V3), ∀ q ∈ ({a, b, c} : Set V3),
      p - q ∈ K := by
    intro p hp q hq
    have hpa : a = p ∨ b = p ∨ c = p := by
      rcases Set.mem_insert_iff.mp hp with h | h
      · exact Or.inl h.symm
      · rcases Set.mem_insert_iff.mp h with h2 | h2
        · exact Or.inr (Or.inl h2.symm)
        · exact Or.inr (Or.inr (Set.mem_singleton_iff.mp h2).symm)
    have hqa : a = q ∨ b = q ∨ c = q := by
      rcases Set.mem_insert_iff.mp hq with h | h
      · exact Or.inl h.symm
      · rcases Set.mem_insert_iff.mp h with h2 | h2
        · exact Or.inr (Or.inl h2.symm)
        · exact Or.inr (Or.inr (Set.mem_singleton_iff.mp h2).symm)
    rcases hpa with rfl | rfl | rfl <;> rcases hqa with rfl | rfl | rfl
    · simpa using Submodule.zero_mem K
    · rw [show (a - b : V3) = -(b - a) from by abel]
      exact Submodule.neg_mem K hmemBA
    · rw [show (a - c : V3) = -(c - a) from by abel]
      exact Submodule.neg_mem K hmemCA
    · exact hmemBA
    · simpa using Submodule.zero_mem K
    · rw [show (b - c : V3) = (b - a) - (c - a) from by abel]
      exact Submodule.sub_mem K hmemBA hmemCA
    · exact hmemCA
    · rw [show (c - b : V3) = -((b - a) - (c - a)) from by abel]
      exact Submodule.neg_mem K (Submodule.sub_mem K hmemBA hmemCA)
    · simpa using Submodule.zero_mem K
  have hvsle : vectorSpan ℝ ({a, b, c} : Set V3) ≤ K := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro x ⟨p, hp, q, hq, rfl⟩
    exact hdiffs p hp q hq
  have hmem0 : ((0:V3) -ᵥ a) ∈ vectorSpan ℝ ({a, b, c} : Set V3) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction h0 (mem_affineSpan ℝ (by simp))
  have hna : (-(a:V3)) ∈ K := by
    have h2 : ((0:V3) -ᵥ a) ∈ K := hvsle hmem0
    simpa using h2
  -- the orthogonal complement of `K` is nontrivial
  have hfdV3 : Module.Finite ℝ V3 := inferInstance
  have htop : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
  have hadd := K.finrank_add_finrank_orthogonal
  have hpos : (0:ℕ) < Module.finrank ℝ (Submodule.orthogonal K) := by omega
  obtain ⟨n, hnK, hn0⟩ : ∃ n ∈ Submodule.orthogonal K, n ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : Submodule.orthogonal K = ⊥ := by
      ext x
      constructor
      · intro hmem
        rw [Submodule.mem_bot]
        exact hcon x hmem
      · intro hzero
        rw [Submodule.mem_bot] at hzero
        simp [hzero]
    rw [hbot, finrank_bot] at hpos
    omega
  have horth : ∀ z ∈ K, inner ℝ n z = 0 := by
    rw [Submodule.mem_orthogonal'] at hnK
    exact hnK
  have hinna : inner ℝ n a = 0 := by
    have h2 : inner ℝ n (-(a:V3)) = 0 := horth _ hna
    rw [inner_neg_right] at h2
    linarith
  refine ⟨n, hn0, ?_, ?_, ?_⟩
  · rw [← inner_eq_dot, real_inner_comm]
    exact hinna
  · have h1 := horth (b - a) hmemBA
    rw [inner_sub_right] at h1
    rw [← inner_eq_dot, real_inner_comm]
    linarith
  · have h1 := horth (c - a) hmemCA
    rw [inner_sub_right] at h1
    rw [← inner_eq_dot, real_inner_comm]
    linarith


/-! ## XYOFCGX (nearest-neighbor gap) .. XNHPWAB1 -/

/-- HL `XYOFCGX_3_0` (Rogers.hl:6121): in a packing, no point of `V \ S`
is nearer the circumcenter than any point of `S` (3-point case). -/
theorem XYOFCGX_3_0 (V S : Set V3) (hV : Packing V) (hSV : S ⊆ V)
    (hind : ¬ affineDependent S) (hc : circumcenter S = 0)
    (hr : radV S < Real.sqrt 2) (hcard : Nat.card S = 3) :
    ∀ u v, u ∈ S → v ∈ V \ S → dist v 0 > dist u 0 := by
  intro u v hu hv
  have hfin : S.Finite :=
    finite_set_of_fin_dim_affineIndependent (k := ℝ) (not_not.mp hind)
  have hrad : ∀ z ∈ S, dist z 0 = radV S := fun z hz => by
    have h := OAPVION2 S hind z hz
    rw [hc, dist_comm] at h
    exact h.symm
  by_cases hcomp : dist v (0:V3) > dist u (0:V3)
  · exact hcomp
  · exfalso
    push_neg at hcomp
    have hdv : dist v 0 ≤ radV S := hcomp.trans (hrad u hu).le
    obtain ⟨a, b, c, hSab, hab, hac, hbc⟩ := p7_card_3_imp_triple S hfin hcard
    have hSne : S ≠ ∅ := by
      intro hcon
      rw [hcon] at hu
      exact hu
    have h0aff : (0:V3) ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := by
      rw [← hc, hSab]
      exact OAPVION1 _ (by rw [← hSab]; exact hSne) (by rw [← hSab]; exact hind)
    obtain ⟨n, hn0, han, hbn, hcn⟩ := p7_exists_normal3 h0aff
    have dotS : ∀ z ∈ S, z ⬝ᵥ n = 0 := by
      intro z hz
      rw [hSab] at hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact han
      · rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact hbn
        · rw [Set.mem_singleton_iff.mp hz]; exact hcn
    set w := projection v n with hwdef
    have hwn : w ⬝ᵥ n = 0 := by
      have hnn : inner ℝ n n ≠ 0 := by
        rw [inner_eq_dot]
        exact p7_dot_self_ne_zero n hn0
      rw [hwdef, projection, ← inner_eq_dot, inner_sub_left, real_inner_smul_left]
      rw [← inner_eq_dot v n]
      rw [← inner_eq_dot n n]
      rw [div_mul_cancel₀ _ hnn]
      ring
    have hwne : w ≠ 0 := by
      intro h0
      have h2le : (2:ℝ) ≤ dist u v :=
        hV.dist_ge_two (hSV hu) hv.1 (fun hh => hv.2 (by rw [← hh]; exact hu))
      have hpy := PYTHAGORAS_PROJECTION u v n (dotS u hu)
      rw [← hwdef, h0, hrad u hu, dist_comm 0 v] at hpy
      have hrad0 : 0 ≤ radV S := by rw [← hrad u hu]; exact dist_nonneg
      have hb1 := p7_sq_lt_two hrad0 hr
      have hb2 := p7_sq_lt_two dist_nonneg (lt_of_le_of_lt hdv hr)
      have hge : (4:ℝ) ≤ dist u v ^ 2 := by
        have hnn2 : (0:ℝ) ≤ dist u v := dist_nonneg
        nlinarith [h2le, hnn2]
      have hlt : dist u v ^ 2 < (2:ℝ) + 2 := by
        calc dist u v ^ 2 = radV S ^ 2 + dist v 0 ^ 2 := hpy
          _ < 2 + 2 := by linarith [hb1, hb2]
      linarith [hge, hlt]
    have hz0 : ∀ z ∈ S, z ≠ 0 := by
      intro z hz
      refine fun hzz => CIRCUMCENTER_NOT_EQ S hind (by omega) z hz ?_
      rw [hzz]
      exact hc
    have hobtuse : ∀ z ∈ S, Real.pi / 2 < EuclideanGeometry.angle z 0 w := by
      intro z hz
      have hL := XYOFCGX_lemma0 V S 0 v hV hSV hind hc.symm hr hv (by rwa [dist_comm])
        (by omega)
      have hobs := hL.1 z hz
      have hang : Real.pi / 2 < EuclideanGeometry.angle v 0 z := by
        rwa [p7_arcV_eq_angle] at hobs
      rw [EuclideanGeometry.angle_comm] at hang
      exact OBTUSE_ANGLE_PROJECTION z v n hang (dotS z hz)
    have hwnS : w ∉ S := by
      intro hws
      have h0w := hobtuse w hws
      rw [EuclideanGeometry.angle, vsub_eq_sub, sub_zero,
        InnerProductGeometry.angle_self hwne] at h0w
      linarith [Real.pi_pos]
    -- `insert w S` is a 4-point fan around the normal `n`, so the angle sum
    -- around `n` would exceed `2π` — contradiction.
    have hcardW : Nat.card ↑(insert w S) = 4 := by
      haveI : Fintype ↥S := hfin.fintype
      have h1 : Fintype.card ↥(insert w S) = Fintype.card ↥S + 1 := card_insert S hwnS
      have h3 : Fintype.card ↥S = 3 := by
        rw [← Nat.card_eq_fintype_card]
        exact hcard
      rw [Nat.card_eq_fintype_card, h1, h3]
    have hazim : ∀ x y : V3, x ∈ insert w S → y ∈ insert w S → x ≠ y →
        Real.pi / 2 < azim 0 n x y := by
      intro x y hx hy hxy
      have hx0 : x ≠ 0 := by
        rcases Set.mem_insert_iff.mp hx with rfl | hxS
        · exact hwne
        · exact hz0 x hxS
      have hy0 : y ≠ 0 := by
        rcases Set.mem_insert_iff.mp hy with rfl | hyS
        · exact hwne
        · exact hz0 y hyS
      have hxn : x ⬝ᵥ n = 0 := by
        rcases Set.mem_insert_iff.mp hx with rfl | hxS
        · exact hwn
        · exact dotS x hxS
      have hyn : y ⬝ᵥ n = 0 := by
        rcases Set.mem_insert_iff.mp hy with rfl | hyS
        · exact hwn
        · exact dotS y hyS
      have hncx : ¬ Collinear3 0 n x := by
        refine IN_PLANE_NOT_COLLINEAR x n hx0 hn0 ?_
        rw [dotProduct_comm]
        exact hxn
      have hncy : ¬ Collinear3 0 n y := by
        refine IN_PLANE_NOT_COLLINEAR y n hy0 hn0 ?_
        rw [dotProduct_comm]
        exact hyn
      have hang : Real.pi / 2 < EuclideanGeometry.angle x 0 y := by
        rcases Set.mem_insert_iff.mp hx with rfl | hxS
        · have hyS : y ∈ S := by
            rcases Set.mem_insert_iff.mp hy with h | h
            · exact absurd h.symm hxy
            · exact h
          have hyw := hobtuse y hyS
          rw [EuclideanGeometry.angle_comm w 0 y]
          exact hyw
        rcases Set.mem_insert_iff.mp hy with rfl | hyS
        · exact hobtuse x hxS
        · have hL := XYOFCGX_lemma0 V S 0 v hV hSV hind hc.symm hr hv
            (by rwa [dist_comm]) (by omega)
          have hobs := hL.2 x hxS y hyS hxy
          rwa [p7_arcV_eq_angle] at hobs
      have hdeq : EuclideanGeometry.angle x 0 y = dihV 0 n x y :=
        ANGLE_EQ_DIHV x y n hx0 hy0 hn0 (by rw [dotProduct_comm]; exact hxn)
          (by rw [dotProduct_comm]; exact hyn)
      rw [hdeq] at hang
      exact lt_of_lt_of_le hang (DIHV_LE_AZIM 0 n x y hncx hncy)
    have hWfin : (insert w S).Finite := hfin.insert w
    have hbound := ANGLE_SUM_BOUND (insert w S) n (Real.pi / 2) (by positivity) hWfin
      (by rw [hcardW]; norm_num) hazim
    rw [hcardW] at hbound
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    linarith

/-- With `v`, `x`, `y` pairwise non-collinear at the origin and all three
pairwise dot products (against `v`) negative, the dihedral angle along `0v`
between the half-planes of `x` and `y` is obtuse: `cos (dihV 0 v x y) < 0`
(the `RLXWSTK` step of the HOL `XYOFCGX_4_0`, done by direct computation). -/
private theorem p7_cos_dihV_lt_zero {x y v : V3} (hv : v ≠ 0) (hx : x ≠ 0)
    (hy : y ≠ 0) (hvv : 0 < v ⬝ᵥ v) (hxy : x ⬝ᵥ y < 0) (hβ : x ⬝ᵥ v < 0)
    (hγ : y ⬝ᵥ v < 0) (hncx : ¬ Collinear3 0 v x) (hncy : ¬ Collinear3 0 v y) :
    Real.cos (dihV 0 v x y) < 0 := by
  -- the orthogonal projections of `x`, `y` into the plane perpendicular to `v`
  have hvapne : ((v ⬝ᵥ v : ℝ) • x - (x ⬝ᵥ v) • v : V3) ≠ 0 := by
    intro h0
    have h2 : ((v ⬝ᵥ v : ℝ)) • x = (x ⬝ᵥ v) • v := eq_of_sub_eq_zero h0
    have h3 : x = ((x ⬝ᵥ v) / (v ⬝ᵥ v)) • v := by
      have h4 : ((v ⬝ᵥ v : ℝ))⁻¹ • ((x ⬝ᵥ v) • v) = ((x ⬝ᵥ v) / (v ⬝ᵥ v)) • v := by
        rw [smul_smul, inv_mul_eq_div]
      rw [← h4, ← h2, inv_smul_smul₀ (ne_of_gt hvv)]
    exact hncx
      ((collinear3_iff_smul (v := 0) (w := v) (w1 := x) hv).mpr
        ⟨(x ⬝ᵥ v) / (v ⬝ᵥ v), by rw [sub_zero, sub_zero]; exact h3⟩)
  have hvbpne : ((v ⬝ᵥ v : ℝ) • y - (y ⬝ᵥ v) • v : V3) ≠ 0 := by
    intro h0
    have h2 : ((v ⬝ᵥ v : ℝ)) • y = (y ⬝ᵥ v) • v := eq_of_sub_eq_zero h0
    have h3 : y = ((y ⬝ᵥ v) / (v ⬝ᵥ v)) • v := by
      have h4 : ((v ⬝ᵥ v : ℝ))⁻¹ • ((y ⬝ᵥ v) • v) = ((y ⬝ᵥ v) / (v ⬝ᵥ v)) • v := by
        rw [smul_smul, inv_mul_eq_div]
      rw [← h4, ← h2, inv_smul_smul₀ (ne_of_gt hvv)]
    exact hncy
      ((collinear3_iff_smul (v := 0) (w := v) (w1 := y) hv).mpr
        ⟨(y ⬝ᵥ v) / (v ⬝ᵥ v), by rw [sub_zero, sub_zero]; exact h3⟩)
  rw [dihV]
  simp only [sub_zero]
  rw [p7_cos_arcV 0 _ _ hvapne hvbpne]
  simp only [sub_zero]
  -- the numerator: ⟨αx - βv, αy - γv⟩ = α²⟨x,y⟩ - αβγ < 0 with α = v·v,
  -- β = x·v < 0, γ = y·v < 0, ⟨x,y⟩ < 0
  have hden : (0:ℝ) < dist ((v ⬝ᵥ v) • x - (x ⬝ᵥ v) • v) 0 *
      dist ((v ⬝ᵥ v) • y - (y ⬝ᵥ v) • v) 0 :=
    mul_pos (dist_pos.mpr hvapne) (dist_pos.mpr hvbpne)
  have hnum : ((v ⬝ᵥ v : ℝ) • x - (x ⬝ᵥ v) • v) ⬝ᵥ ((v ⬝ᵥ v) • y - (y ⬝ᵥ v) • v) < 0 := by
    have e2 : ((v ⬝ᵥ v : ℝ) • x - (x ⬝ᵥ v) • v) ⬝ᵥ ((v ⬝ᵥ v) • y - (y ⬝ᵥ v) • v)
        = (v ⬝ᵥ v) * ((v ⬝ᵥ v) * (x ⬝ᵥ y) - (x ⬝ᵥ v) * (y ⬝ᵥ v)) :=
      p7_dot_expand (x : Fin 3 → ℝ) (y : Fin 3 → ℝ) (v : Fin 3 → ℝ)
    rw [e2]
    have h3 : (0:ℝ) < (x ⬝ᵥ v) * (y ⬝ᵥ v) := by
      simpa using mul_pos (neg_pos.mpr hβ) (neg_pos.mpr hγ)
    have h4 : (v ⬝ᵥ v) * (x ⬝ᵥ y) < 0 := mul_neg_of_pos_of_neg hvv hxy
    nlinarith [h3, h4, hvv]
  have hzero : ((0:V3) : Fin 3 → ℝ) = 0 := rfl
  simp only [sub_zero, hzero]
  exact (div_lt_iff₀ hden).mpr (by rw [zero_mul]; exact hnum)

theorem XYOFCGX_4_0 (V S : Set V3) (hV : Packing V) (hSV : S ⊆ V)
    (hind : ¬ affineDependent S) (hc : circumcenter S = 0)
    (hr : radV S < Real.sqrt 2) (hcard : Nat.card S = 4) :
    ∀ u v, u ∈ S → v ∈ V \ S → dist v 0 > dist u 0 := by
  intro u v hu hv
  have hfin : S.Finite :=
    finite_set_of_fin_dim_affineIndependent (k := ℝ) (not_not.mp hind)
  have hrad : ∀ z ∈ S, dist z 0 = radV S := fun z hz => by
    have h := OAPVION2 S hind z hz
    rw [hc, dist_comm] at h
    exact h.symm
  by_cases hcomp : dist v (0:V3) > dist u (0:V3)
  · exact hcomp
  · exfalso
    push_neg at hcomp
    have hdv : dist v 0 ≤ radV S := hcomp.trans (hrad u hu).le
    have hSne : S ≠ ∅ := by
      intro hcon
      rw [hcon] at hu
      exact hu
    have hv0 : v ≠ 0 := by
      intro h0
      have h2le : (2:ℝ) ≤ dist u v :=
        hV.dist_ge_two (hSV hu) hv.1 (fun hh => hv.2 (by rw [← hh]; exact hu))
      rw [h0] at h2le
      rw [hrad u hu] at h2le
      have h3 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
      linarith
    have hz0 : ∀ z ∈ S, z ≠ 0 := by
      intro z hz
      refine fun hzz => CIRCUMCENTER_NOT_EQ S hind (by omega) z hz ?_
      rw [hzz]
      exact hc
    have hL := XYOFCGX_lemma0 V S 0 v hV hSV hind hc.symm hr hv
      (by rwa [dist_comm]) (by omega)
    obtain ⟨hLi, hLii⟩ := hL
    -- every `z ∈ S` has `v ⬝ᵥ z < 0`, and distinct points of `S` subtend
    -- negative dot products at the origin
    have hdoti : ∀ z ∈ S, v ⬝ᵥ z < 0 := by
      intro z hz
      have hobs := hLi z hz
      have hcos : Real.cos (arcV 0 v z) < 0 := (ARCV_GT_PI2 0 v z).mp hobs
      rw [p7_cos_arcV 0 v z hv0 (hz0 z hz)] at hcos
      have hpos : (0:ℝ) < dist v 0 * dist z 0 :=
        mul_pos (dist_pos.mpr hv0) (dist_pos.mpr (hz0 z hz))
      simpa using (div_lt_iff₀ hpos).mp hcos
    have hdotii : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ⬝ᵥ y < 0 := by
      intro x hx y hy hxy
      have hobs := hLii x hx y hy hxy
      have hcos : Real.cos (arcV 0 x y) < 0 := (ARCV_GT_PI2 0 x y).mp hobs
      rw [p7_cos_arcV 0 x y (hz0 x hx) (hz0 y hy)] at hcos
      have hpos : (0:ℝ) < dist x 0 * dist y 0 :=
        mul_pos (dist_pos.mpr (hz0 x hx)) (dist_pos.mpr (hz0 y hy))
      simpa using (div_lt_iff₀ hpos).mp hcos
    -- `{0, v, z}` is never collinear for `z ∈ S`
    have hvv : (0:ℝ) < v ⬝ᵥ v := by
      have hnsq : ‖(v:V3)‖ ^ 2 = v ⬝ᵥ v := norm_sq_eq_dot v
      rw [← hnsq]; positivity
    have hncol : ∀ x ∈ S, ¬ Collinear3 0 v x := by
      intro x hx hcol
      obtain ⟨t, htx⟩ := (collinear3_iff_smul (v := 0) (w := v) (w1 := x) hv0).mp hcol
      have htx' : x = t • v := by simpa using htx
      have hxiv : inner ℝ v x < 0 := by rw [inner_eq_dot]; exact hdoti x hx
      have hxv2 : 0 < inner ℝ v v := by rw [inner_eq_dot]; exact hvv
      rw [htx', real_inner_smul_right] at hxiv
      have htneg : t < 0 := by
        by_contra hge
        push_neg at hge
        exact absurd (mul_nonneg hge hxv2.le) (not_le.mpr hxiv)
      -- pick another point of `S` and derive opposite signs
      obtain ⟨w, hwS, hwx⟩ : ∃ z ∈ S, z ≠ x := by
        by_contra hcon
        push_neg at hcon
        have hSx : S = {x} := Set.eq_singleton_iff_unique_mem.mpr ⟨hx, fun z hz => hcon z hz⟩
        rw [hSx] at hcard
        simp at hcard
      have h2 := hdoti w hwS
      have h3 := hdotii x hx w hwS hwx.symm
      have hvw : inner ℝ v w < 0 := by rw [inner_eq_dot]; exact h2
      rw [htx', ← inner_eq_dot, real_inner_smul_left] at h3
      have hpos : (0:ℝ) < t * inner ℝ v w :=
        mul_pos_of_neg_of_neg htneg hvw
      linarith
    -- the azimuths around `0v` between points of `S` all exceed `π/2`
    have hazim : ∀ x y : V3, x ∈ S → y ∈ S → x ≠ y →
        Real.pi / 2 < azim 0 v x y := by
      intro x y hx hy hxy
      have hcx : ¬ Collinear3 0 v x := hncol x hx
      have hcy : ¬ Collinear3 0 v y := hncol y hy
      have hdi : Real.pi / 2 < dihV 0 v x y :=
        (DIHV_GT_PI2 0 v x y).mpr
          (p7_cos_dihV_lt_zero hv0 (hz0 x hx) (hz0 y hy) hvv (hdotii x hx y hy hxy)
            (by rw [dotProduct_comm]; exact hdoti x hx)
            (by rw [dotProduct_comm]; exact hdoti y hy) hcx hcy)
      exact lt_of_lt_of_le hdi (DIHV_LE_AZIM 0 v x y hcx hcy)
    -- the angle-sum bound around the edge `0v` closes the argument
    have hbound := ANGLE_SUM_BOUND S v (Real.pi / 2) (by positivity) hfin
      (by rw [hcard]; norm_num) hazim
    rw [hcard] at hbound
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    linarith

/-- The translate of an affinely independent set is affinely independent
(same proof as PA6's private `p6_not_affdep_image`; needed to transport
`XYOFCGX_3_0`/`XYOFCGX_4_0` to general circumcenters). -/
private theorem p7_not_affdep_image (s : Set V3) (a : V3) (h2 : ¬affineDependent s) :
    ¬affineDependent ((fun x : V3 => a + x) '' s) := by
  let hidx : ↥s ≃ (↥((fun x : V3 => a + x) '' s : Set V3)) :=
    { toFun := fun x => ⟨a + (x : V3), ⟨x, x.2, rfl⟩⟩
      invFun := fun y => ⟨(y : V3) - a, by
        obtain ⟨z, hz, heq⟩ := y.2
        rw [← heq]
        simpa using hz⟩
      left_inv := fun x => Subtype.ext (show a + (x : V3) - a = (x : V3) from by simp)
      right_inv := fun y =>
        Subtype.ext (show a + ((y : V3) - a) = (y : V3) from by simp) }
  have hcoe : (fun y : ↥((fun x : V3 => a + x) '' s : Set V3) => (y : V3)) ∘ hidx =
      (AffineEquiv.constVAdd ℝ V3 a) ∘ (fun x : ↥s => (x : V3)) := by
    rfl
  rw [affineDependent, not_not]
  have hA : AffineIndependent ℝ
      ((fun y : ↥((fun x : V3 => a + x) '' s : Set V3) => (y : V3)) ∘ hidx) := by
    rw [hcoe, AffineEquiv.affineIndependent_iff]
    exact not_not.mp h2
  exact (affineIndependent_equiv hidx).mp hA

/-- The packing property is translation invariant. -/
private theorem p7_packing_image (V : Set V3) (a : V3) (hV : Packing V) :
    Packing ((fun x : V3 => a + x) '' V) := by
  intro w hw z hz hlt
  obtain ⟨w', hw', rfl⟩ := hw
  obtain ⟨z', hz', rfl⟩ := hz
  have h2 : dist w' z' < 2 := by
    rwa [← dist_add_left]
  exact congrArg (fun t => a + t) (hV w' hw' z' hz' h2)

/-- HL `XYOFCGX` (Rogers.hl:6559): the general circumcenter-gap statement. -/
theorem XYOFCGX (V S : Set V3) (p : V3) (hV : Packing V) (hSV : S ⊆ V)
    (hind : ¬ affineDependent S) (hp : p = circumcenter S)
    (hr : radV S < Real.sqrt 2) :
    ∀ u v, u ∈ S → v ∈ V \ S → dist v p > dist u p := by
  intro u v hu hv
  have hfin : S.Finite :=
    finite_set_of_fin_dim_affineIndependent (k := ℝ) (not_not.mp hind)
  haveI := hfin.fintype
  have hcardle : Nat.card S ≤ 4 := by
    have h2 := (not_not.mp hind).card_le_finrank_succ (k := ℝ) (V := V3) (P := V3)
    have h3 : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range fun x : ↥S => (x : V3))) ≤ 3 := by
      trans Module.finrank ℝ V3
      · exact Submodule.finrank_le _
      · rw [finrank_euclideanSpace_fin]
    rw [Nat.card_eq_fintype_card]
    omega
  have hcardpos : 0 < Nat.card S := Nat.card_pos_iff.mpr ⟨⟨u, hu⟩, hfin⟩
  by_cases h1 : Nat.card S = 1
  · exact XYOFCGX_1 V S p hV hSV hind hp hr (by omega) u hu v hv
  by_cases h2 : Nat.card S = 2
  · exact XYOFCGX_2 V S p hV hSV hind hp hr h2 u hu v hv
  -- translation to the circumcenter-0 setting for the 3- and 4-point cases
  have hSne : S ≠ ∅ := fun hc0 => by
    rw [hc0] at hu; exact hu
  set K : Set V3 := (fun x : V3 => -p + x) '' S with hKdef
  set W : Set V3 := (fun x : V3 => -p + x) '' V with hWdef
  have hwV : Packing W := p7_packing_image V (-p) hV
  have hKV : K ⊆ W := Set.image_mono hSV
  have hindK : ¬ affineDependent K := p7_not_affdep_image S (-p) hind
  have hcK : circumcenter K = 0 := by
    rw [hKdef, CIRCUMCENTER_TRANSLATION S (-p) hSne hind, hp, neg_add_cancel]
  have hrK : radV K < Real.sqrt 2 := by
    rw [hKdef, RADV_TRANSLATION S (-p) hind]
    exact hr
  have hinj : Function.Injective (fun x : V3 => -p + x) := fun a b hab => add_left_cancel hab
  have hcardK : Nat.card K = Nat.card S := Nat.card_image_of_injective hinj S
  have huK : (-p + u) ∈ K := ⟨u, hu, rfl⟩
  have hvW : (-p + v) ∈ W \ K := by
    refine ⟨⟨v, hv.1, rfl⟩, ?_⟩
    rintro ⟨z, hzS, hzeq⟩
    refine hv.2 ?_
    have hzv : z = v := add_left_cancel hzeq
    rw [← hzv]; exact hzS
  have hzp : ∀ z : V3, dist (-p + z) (0:V3) = dist z p := by
    intro z
    rw [show (0:V3) = -p + p from (neg_add_cancel p).symm, dist_add_left]
  by_cases h3 : Nat.card S = 3
  · have key := XYOFCGX_3_0 W K hwV hKV hindK hcK hrK (by rw [hcardK]; exact h3)
      (-p + u) (-p + v) huK hvW
    rwa [hzp, hzp] at key
  by_cases h4 : Nat.card S = 4
  · have key := XYOFCGX_4_0 W K hwV hKV hindK hcK hrK (by rw [hcardK]; exact h4)
      (-p + u) (-p + v) huK hvW
    rwa [hzp, hzp] at key
  exact (by omega : False).elim

/-- HL `BARV_AFFINE_INDEPENDENT` (Rogers.hl:6650). -/
theorem BARV_AFFINE_INDEPENDENT (V : Set V3) (ul : List V3) (k : ℕ)
    (hV : Packing V) (hb : barV V k ul) : ¬ affineDependent (setOfList ul) := by
  classical
  have hlen : ul.length = k + 1 := hb.1
  have hfin : (setOfList ul).Finite := by
    refine Set.Finite.subset (Finset.finite_toSet (s := ul.toFinset)) ?_
    intro x hx
    exact List.mem_toFinset.mpr hx
  haveI := hfin.fintype
  have hcardle : Nat.card (setOfList ul) ≤ ul.length := by
    have h1 : Nat.card (setOfList ul) = hfin.toFinset.card := by
      rw [Nat.card_eq_fintype_card, Set.Finite.card_toFinset hfin]
    rw [h1]
    have h2 : hfin.toFinset = ul.toFinset := by
      ext x
      rw [hfin.mem_toFinset, List.mem_toFinset]
      exact Iff.rfl
    rw [h2]
    exact List.toFinset_card_le ul
  have hcard : (Nat.card (setOfList ul) : ℤ) ≤ affDim (setOfList ul) + 1 := by
    rw [MHFTTZN1 V ul k hV hb]
    omega
  exact p6_affdep_of_dim _ hfin hcard

/-- HL `BARV_IMP_LENGTH_EQ_CARD` (Rogers.hl:6680). -/
theorem BARV_IMP_LENGTH_EQ_CARD (V : Set V3) (ul : List V3) (k : ℕ)
    (hV : Packing V) (hb : barV V k ul) :
    ul.length = k + 1 ∧ Nat.card (setOfList ul) = k + 1 := by
  classical
  refine ⟨hb.1, ?_⟩
  have hlen : ul.length = k + 1 := hb.1
  have hulne : ul ≠ [] := by
    rintro rfl
    simp at hlen
  have hx := List.head_mem hulne
  have hfin : (setOfList ul).Finite := by
    refine Set.Finite.subset (Finset.finite_toSet (s := ul.toFinset)) ?_
    intro x hx
    exact List.mem_toFinset.mpr hx
  haveI := hfin.fintype
  have hpos : 0 < Nat.card (setOfList ul) := Nat.card_pos_iff.mpr ⟨⟨_, hx⟩, hfin⟩
  have hind := BARV_AFFINE_INDEPENDENT V ul k hV hb
  have hcardEq : Nat.card ↥(setOfList ul) = Fintype.card ↥(setOfList ul) :=
    Nat.card_eq_fintype_card
  have hcardle : Nat.card (setOfList ul) ≤ ul.length := by
    have h1 : Nat.card (setOfList ul) = hfin.toFinset.card := by
      rw [Nat.card_eq_fintype_card, Set.Finite.card_toFinset hfin]
    rw [h1]
    have h2 : hfin.toFinset = ul.toFinset := by
      ext x
      rw [hfin.mem_toFinset, List.mem_toFinset]
      exact Iff.rfl
    rw [h2]
    exact List.toFinset_card_le ul
  have haff : AffineIndependent ℝ (fun x : ↥(setOfList ul) => (x : V3)) :=
    not_not.mp hind
  have h4 : Module.finrank ℝ (vectorSpan ℝ (Set.range fun x : ↥(setOfList ul) => (x : V3)))
      = Nat.card (setOfList ul) - 1 :=
    (affineIndependent_iff_finrank_vectorSpan_eq ℝ _
      (show Fintype.card ↥(setOfList ul) = Nat.card (setOfList ul) - 1 + 1 by
        omega)).mp haff
  have hrange : Set.range (fun x : ↥(setOfList ul) => (x : V3)) = setOfList ul := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact x.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  rw [hrange] at h4
  have hne : setOfList ul ≠ ∅ := by
    intro he
    rw [he] at hpos
    simp at hpos
  have haffdim : affDim (setOfList ul) =
      (Module.finrank ℝ (vectorSpan ℝ (setOfList ul)) : ℤ) :=
    if_neg hne
  have hdimk : affDim (setOfList ul) = (k : ℤ) := MHFTTZN1 V ul k hV hb
  omega

/-- HL `AFFINE_HULL_PROJECTION_EXISTS` (Rogers.hl:6694). -/
theorem AFFINE_HULL_PROJECTION_EXISTS (S : Set V3) (p : V3) (hne : S ≠ ∅) :
    ∃ x n : V3, p = x + n ∧ x ∈ (affineSpan ℝ S : Set V3) ∧
      ∀ v ∈ S, ∀ w ∈ S, (v - w) ⬝ᵥ n = 0 := by
  classical
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hzK : (z:V3) ∈ (affineSpan ℝ S : Set V3) := mem_affineSpan ℝ hz
  obtain ⟨d, hdD, n, hnD, hdec⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := (affineSpan ℝ S).direction) (p - z)
  refine ⟨z + d, n, ?_, ?_, ?_⟩
  · rw [add_assoc, hdec.symm]
    abel
  · have hvd : (z + d : V3) = d +ᵥ z := add_comm z d
    rw [hvd]
    exact AffineSubspace.vadd_mem_of_mem_direction hdD hzK
  · intro v hv w hw
    have hvK : (v:V3) ∈ (affineSpan ℝ S : Set V3) := mem_affineSpan ℝ hv
    have hwK : (w:V3) ∈ (affineSpan ℝ S : Set V3) := mem_affineSpan ℝ hw
    have hvwD : (v - w : V3) ∈ (affineSpan ℝ S).direction :=
      AffineSubspace.vsub_mem_direction hvK hwK
    have hinner : inner ℝ n (v - w) = 0 := by
      rw [Submodule.mem_orthogonal'] at hnD
      exact hnD _ hvwD
    rw [← inner_eq_dot, real_inner_comm]
    exact hinner

/-- HL `AFFINE_HULL_PROJECTION_DIST_EQ` (Rogers.hl:6776). -/
theorem AFFINE_HULL_PROJECTION_DIST_EQ (S : Set V3) (p v w x n : V3)
    (hv : v ∈ S) (hw : w ∈ S) (hdist : dist p v = dist p w) (hpxn : p = x + n)
    (hn : ∀ u ∈ S, ∀ z ∈ S, (u - z) ⬝ᵥ n = 0) : dist x v = dist x w := by
  have hinn : inner ℝ (p - v) n = inner ℝ (p - w) n := by
    have h1 : inner ℝ (w - v) n = 0 := by
      have h0 := hn v hv w hw
      rw [← inner_eq_dot] at h0
      rw [show (w - v : V3) = -(v - w) from by abel, inner_neg_left]
      linarith
    have h3 : inner ℝ ((p - v) - (p - w)) n = 0 := by
      rw [show ((p - v) - (p - w) : V3) = w - v from by abel]
      exact h1
    rw [inner_sub_left] at h3
    linarith
  have hxv : x - v = (p - v) - n := by rw [hpxn]; abel
  have hxw : x - w = (p - w) - n := by rw [hpxn]; abel
  have s2 : ‖x - v‖ ^ 2 = ‖x - w‖ ^ 2 := by
    rw [hxv, hxw]
    rw [norm_sub_sq_real (p - v) n, norm_sub_sq_real (p - w) n]
    rw [hinn]
    rw [show ‖p - v‖ = dist p v from (dist_eq_norm p v).symm,
      show ‖p - w‖ = dist p w from (dist_eq_norm p w).symm, hdist]
  rcases (sq_eq_sq_iff_eq_or_eq_neg (a := ‖x - v‖) (b := ‖x - w‖)).mp s2 with h5 | h5
  · rw [dist_eq_norm, dist_eq_norm]; exact h5
  · rw [dist_eq_norm, dist_eq_norm]
    linarith [norm_nonneg (x - v), norm_nonneg (x - w)]

/-- HL `ORTHOGONAL_TO_AFFINE_HULL_EQ` (Rogers.hl:6799). -/
theorem ORTHOGONAL_TO_AFFINE_HULL_EQ (S : Set V3) (n : V3) :
    (∀ v ∈ S, ∀ w ∈ S, (v - w) ⬝ᵥ n = 0) ↔
      ∀ v ∈ (affineSpan ℝ S : Set V3), ∀ w ∈ (affineSpan ℝ S : Set V3),
        (v - w) ⬝ᵥ n = 0 := by
  constructor
  · intro h v hv w hw
    set U := (Submodule.span ℝ ({n} : Set V3)).orthogonal with hU
    have hgen : ∀ a ∈ S, ∀ b ∈ S, (a - b : V3) ∈ U := by
      intro a ha b hb
      rw [hU, Submodule.mem_orthogonal']
      intro y hy
      simp only [Submodule.mem_span_singleton] at hy
      obtain ⟨t, rfl⟩ := hy
      rw [inner_smul_right, real_inner_comm, inner_eq_dot, dotProduct_comm,
        h a ha b hb]
      ring
    have hsp : vectorSpan ℝ S ≤ U := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro x ⟨a, ha, b, hb, rfl⟩
      exact hgen a ha b hb
    have h2 : (v - w : V3) ∈ vectorSpan ℝ S := by
      rw [← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction hv hw
    have h3 := hsp h2
    rw [hU, Submodule.mem_orthogonal'] at h3
    have hy := h3 n (Submodule.subset_span (by simp))
    rw [← inner_eq_dot]
    exact hy
  · intro h v hv w hw
    exact h v (mem_affineSpan ℝ hv) w (mem_affineSpan ℝ hw)

/-- HL `AFFINE_HULL_PROJECTION_DIST_LE` (Rogers.hl:6863). -/
theorem AFFINE_HULL_PROJECTION_DIST_LE (S : Set V3) (p v x n : V3)
    (hv : v ∈ S) (hpxn : p = x + n) (hx : x ∈ (affineSpan ℝ S : Set V3))
    (hn : ∀ u ∈ S, ∀ z ∈ S, (u - z) ⬝ᵥ n = 0) : dist x v ≤ dist p v := by
  have horth := (ORTHOGONAL_TO_AFFINE_HULL_EQ S n).mp hn x hx v (mem_affineSpan ℝ hv)
  have hdeq : (p - v : V3) = (x - v) + n := by rw [hpxn]; abel
  have hsq : ‖x - v‖ ^ 2 ≤ ‖(x - v) + n‖ ^ 2 := by
    rw [norm_add_sq_real, inner_eq_dot, horth]
    linarith [sq_nonneg ‖x - v‖, sq_nonneg ‖n‖]
  rw [dist_eq_norm, dist_eq_norm, hdeq]
  have h0v : 0 ≤ ‖x - v‖ := norm_nonneg _
  have hle := abs_le_of_sq_le_sq hsq (norm_nonneg _)
  rw [abs_of_nonneg h0v] at hle
  exact hle

/-- HL `AFFINE_HULL_PROJECTION_DIST_LT` (Rogers.hl:6889). -/
theorem AFFINE_HULL_PROJECTION_DIST_LT (S : Set V3) (p v x n : V3)
    (hv : v ∈ S) (hp : ¬ p ∈ (affineSpan ℝ S : Set V3)) (hpxn : p = x + n)
    (hx : x ∈ (affineSpan ℝ S : Set V3))
    (hn : ∀ u ∈ S, ∀ z ∈ S, (u - z) ⬝ᵥ n = 0) : dist x v < dist p v := by
  have horth := (ORTHOGONAL_TO_AFFINE_HULL_EQ S n).mp hn x hx v (mem_affineSpan ℝ hv)
  have hn0 : n ≠ 0 := by
    intro h0
    apply hp
    rw [hpxn, h0, add_zero]
    exact hx
  have hdeq : (p - v : V3) = (x - v) + n := by rw [hpxn]; abel
  have hpos : (0:ℝ) < ‖n‖ ^ 2 := by
    have h1 : 0 < ‖n‖ := norm_pos_iff.mpr hn0
    nlinarith [sq_nonneg ‖n‖]
  have hsq : ‖x - v‖ ^ 2 < ‖(x - v) + n‖ ^ 2 := by
    rw [norm_add_sq_real, inner_eq_dot, horth]
    linarith [sq_nonneg ‖x - v‖, hpos]
  rw [dist_eq_norm, dist_eq_norm, hdeq]
  exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- A subset of an affinely independent set is affinely independent
(factored from the three circumcenter-projection theorems below). -/
private theorem p7_hind_subset (s t : Set V3) (hind : ¬ affineDependent s)
    (hts : t ⊆ s) : ¬ affineDependent t := by
  classical
  rw [affineDependent, not_not]
  rcases Set.eq_empty_or_nonempty t with hE | hne
  · rw [hE]
    have hsub : Subsingleton ↥t := by
      rw [hE]
      exact ⟨fun a b => absurd a.2 (Set.notMem_empty _)⟩
    exact affineIndependent_of_subsingleton ℝ _
  · obtain ⟨w₀, hw₀t⟩ := hne
    have hw₀s : w₀ ∈ s := hts hw₀t
    have hsi : AffineIndependent ℝ (fun y : ↥s => (y : V3)) := not_not.mp hind
    have hw₀S : w₀ ∈ Set.range (fun y : ↥s => (y : V3)) := ⟨⟨w₀, hw₀s⟩, rfl⟩
    have hw₀T : w₀ ∈ Set.range (fun i : ↥t => (i : V3)) := ⟨⟨w₀, hw₀t⟩, rfl⟩
    have hlsi : LinearIndependent ℝ
        (fun i : {y : ↥s // y ≠ (⟨w₀, hw₀s⟩ : ↥s)} => ((i : V3) - w₀)) :=
      (affineIndependent_iff_linearIndependent_vsub ℝ _ ⟨w₀, hw₀s⟩).mp hsi
    refine (affineIndependent_iff_linearIndependent_vsub ℝ _ ⟨w₀, hw₀t⟩).mpr ?_
    refine hlsi.comp (f := fun i : {x : ↥t // x ≠ (⟨w₀, hw₀t⟩ : ↥t)} =>
      (⟨⟨(i : V3), hts i.1.2⟩, ?_⟩ : {y : ↥s // y ≠ (⟨w₀, hw₀s⟩ : ↥s)})) ?_
    · intro h
      exact i.2 (Subtype.ext (Subtype.mk.inj h))
    · intro a b hab
      exact Subtype.ext (Subtype.ext (by simpa using hab))

/-- HL `AFFINE_HULL_CIRCUMCENTER_PROJECTION` (Rogers.hl:6923). -/
theorem AFFINE_HULL_CIRCUMCENTER_PROJECTION (s t : Set V3)
    (hind : ¬ affineDependent s) (hts : t ⊆ s) (hne : t ≠ ∅) :
    ∃ n : V3, circumcenter s = circumcenter t + n ∧
      ∀ v ∈ t, ∀ w ∈ t, (v - w) ⬝ᵥ n = 0 := by
  classical
  obtain ⟨x, n, hdec, hx, hn⟩ := AFFINE_HULL_PROJECTION_EXISTS t (circumcenter s) hne
  have horth' := (ORTHOGONAL_TO_AFFINE_HULL_EQ t n).mp hn
  have hsq : ∀ w ∈ t, dist x w ^ 2 = radV s ^ 2 - ‖n‖ ^ 2 := by
    intro w hw
    have hwt : w ∈ s := hts hw
    have hradw : radV s = dist (circumcenter s) w := OAPVION2 s hind w hwt
    have hdec' : (circumcenter s - w : V3) = (x - w) + n := by rw [hdec]; abel
    have h1 : dist x w ^ 2 = dist (circumcenter s) w ^ 2 - ‖n‖ ^ 2 := by
      rw [dist_eq_norm, dist_eq_norm, hdec', norm_add_sq_real, inner_eq_dot,
        horth' x hx w (mem_affineSpan ℝ hw)]
      ring
    rw [h1, hradw]
  obtain ⟨w₀, hw₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hind_t : ¬affineDependent t := p7_hind_subset s t hind hts
  have hxct : x = circumcenter t := by
    refine OAPVION3 t hind_t x hx ⟨dist x w₀, ?c⟩
    intro w hw
    have h1 := hsq w hw
    have h2 := hsq w₀ hw₀
    have h3 : 0 ≤ dist x w := dist_nonneg
    have h4 : 0 ≤ dist x w₀ := dist_nonneg
    rcases (sq_eq_sq_iff_eq_or_eq_neg (a := dist x w) (b := dist x w₀)).mp (by rw [h1, h2]) with h | h
    · exact h
    · linarith [h3, h4]
  refine ⟨n, ?_, hn⟩
  rw [hxct] at hdec
  exact hdec


/-- HL `AFFINE_HULL_CIRCUMCENTER_EQ` (Rogers.hl:6964). -/
theorem AFFINE_HULL_CIRCUMCENTER_EQ (s t : Set V3)
    (hind : ¬ affineDependent s) (hts : t ⊆ s) (hne : t ≠ ∅)
    (hmem : circumcenter s ∈ (affineSpan ℝ t : Set V3)) :
    circumcenter s = circumcenter t := by
  obtain ⟨n, hdec, hn⟩ := AFFINE_HULL_CIRCUMCENTER_PROJECTION s t hind hts hne
  have hind_t : ¬affineDependent t := p7_hind_subset s t hind hts
  have hct : circumcenter t ∈ (affineSpan ℝ t : Set V3) := OAPVION1 t hne hind_t
  have hnn : n = circumcenter s - circumcenter t := by rw [hdec]; abel
  have hself : (circumcenter s - circumcenter t) ⬝ᵥ n = 0 :=
    (ORTHOGONAL_TO_AFFINE_HULL_EQ t n).mp hn (circumcenter s) hmem (circumcenter t) hct
  rw [← hnn] at hself
  have hnsq : ‖n‖ ^ 2 = n ⬝ᵥ n := norm_sq_eq_dot n
  have hz : n = 0 := by
    have h1 : ‖n‖ ^ 2 = 0 := by rw [hnsq]; exact hself
    have h2 : ‖n‖ = 0 := sq_eq_zero_iff.mp h1
    exact norm_eq_zero.mp h2
  rw [hdec, hz, add_zero]

/-- HL `AFFINE_HULL_RADV` (Rogers.hl:6986): Pythagoras for circumradii. -/
theorem AFFINE_HULL_RADV (s t : Set V3) (hind : ¬ affineDependent s)
    (hts : t ⊆ s) (hne : t ≠ ∅) :
    radV s ^ 2 = radV t ^ 2 + dist (circumcenter t) (circumcenter s) ^ 2 ∧
      0 ≤ radV s ∧ 0 ≤ radV t := by
  classical
  obtain ⟨n, hdec, hn⟩ := AFFINE_HULL_CIRCUMCENTER_PROJECTION s t hind hts hne
  have horth' := (ORTHOGONAL_TO_AFFINE_HULL_EQ t n).mp hn
  have hind_t : ¬affineDependent t := p7_hind_subset s t hind hts
  have hct : circumcenter t ∈ (affineSpan ℝ t : Set V3) := OAPVION1 t hne hind_t
  obtain ⟨w₀, hw₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have h1 : radV s = dist (circumcenter s) w₀ := OAPVION2 s hind w₀ (hts hw₀)
  have h2 : radV t = dist (circumcenter t) w₀ := OAPVION2 t hind_t w₀ hw₀
  have hdec' : (circumcenter s - w₀ : V3) = (circumcenter t - w₀) + n := by rw [hdec]; abel
  have h3 : dist (circumcenter s) w₀ ^ 2 = dist (circumcenter t) w₀ ^ 2 + ‖n‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, hdec', norm_add_sq_real, inner_eq_dot,
      horth' (circumcenter t) hct w₀ (mem_affineSpan ℝ hw₀)]
    ring
  have h4 : ‖n‖ = dist (circumcenter t) (circumcenter s) := by
    have hsub : (circumcenter t - circumcenter s : V3) = -n := by rw [hdec]; abel
    rw [dist_eq_norm, hsub, norm_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, h2, h3, h4]
  · rw [h1]; exact dist_nonneg
  · rw [h2]; exact dist_nonneg

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

/-- Auxiliary for `XNHPWAB1` (existence half of HOL `CLOSEST_POINT_EXISTS`,
sphere.hl): for a nonempty closed convex set the `closestPoint` epsilon is a
genuine nearest point (Mathlib Hilbert projection theorem). -/
private theorem p7_closest_point_exists (K : Set V3) (x : V3)
    (hne : K.Nonempty) (hc : IsClosed K) (hcv : Convex ℝ K) :
    closestPoint K x ∈ K ∧ ∀ z ∈ K, dist x (closestPoint K x) ≤ dist x z := by
  obtain ⟨v, hvK, hnorm⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv x
  have hstep : ∀ w : {y // y ∈ K}, ‖x - v‖ ≤ ‖x - (w : V3)‖ := by
    intro w
    rw [hnorm]
    exact ciInf_le ⟨0, Set.forall_mem_range.2 fun y => norm_nonneg _⟩ w
  have hmin : ∀ z ∈ K, dist x v ≤ dist x z := by
    intro z hz
    rw [dist_eq_norm, dist_eq_norm]
    exact hstep ⟨z, hz⟩
  exact Classical.epsilon_spec (p := fun y : V3 => y ∈ K ∧ ∀ z ∈ K, dist x y ≤ dist x z)
    ⟨v, hvK, hmin⟩

/-- Auxiliary for `XNHPWAB1` (HOL `CLOSEST_POINT_UNIQUE`, sphere.hl): nearest
points on convex sets are unique (first-order condition via the real inner
product). -/
private theorem p7_closest_point_unique (K : Set V3) (x p : V3)
    (hcv : Convex ℝ K) (hpK : p ∈ K) (hp : ∀ z ∈ K, dist x p ≤ dist x z) :
    closestPoint K x = p := by
  have hbd : BddBelow (Set.range fun w : {z // z ∈ K} => ‖x - (w : V3)‖) :=
    ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
  haveI : Nonempty {z // z ∈ K} := ⟨⟨p, hpK⟩⟩
  have hspec : ∀ y : V3, y ∈ K → (∀ z ∈ K, dist x y ≤ dist x z) → y = p := by
    intro y hyK hy
    have hymin : ‖x - y‖ = ⨅ w : {z // z ∈ K}, ‖x - (w : V3)‖ :=
      le_antisymm
        (le_ciInf fun w => by simpa only [dist_eq_norm] using hy w w.2)
        (ciInf_le hbd ⟨y, hyK⟩)
    have hpmin : ‖x - p‖ = ⨅ w : {z // z ∈ K}, ‖x - (w : V3)‖ :=
      le_antisymm
        (le_ciInf fun w => by simpa only [dist_eq_norm] using hp w w.2)
        (ciInf_le hbd ⟨p, hpK⟩)
    have hch1 := (norm_eq_iInf_iff_real_inner_le_zero hcv hyK).mp hymin
    have hch2 := (norm_eq_iInf_iff_real_inner_le_zero hcv hpK).mp hpmin
    have h1 : inner ℝ (x - y) (p - y) ≤ 0 := hch1 p hpK
    have hC : 0 ≤ inner ℝ (x - p) (p - y) := by
      have h2 : inner ℝ (x - p) (y - p) ≤ 0 := hch2 y hyK
      have e2 : inner ℝ (x - p) (y - p) = -(inner ℝ (x - p) (p - y)) := by
        rw [show ((y - p : V3)) = -(p - y) from by abel, inner_neg_right]
      linarith
    have hnn : 0 ≤ inner ℝ (p - y) (p - y) := real_inner_self_nonneg
    have hkey : inner ℝ (p - y) (p - y) = 0 := by
      have hsum : inner ℝ (p - y) (p - y)
          = inner ℝ (x - y) (p - y) - inner ℝ (x - p) (p - y) := by
        rw [← inner_sub_left, show (((x - y) - (x - p) : V3)) = p - y from by abel]
      rw [hsum]
      linarith
    have hzero : (p - y : V3) = 0 := inner_self_eq_zero.mp hkey
    exact (sub_eq_zero.mp hzero).symm
  have heq : (fun y : V3 => y ∈ K ∧ ∀ z ∈ K, dist x y ≤ dist x z) = (fun y : V3 => y = p) := by
    funext y
    exact propext ⟨fun h => hspec y h.1 h.2, fun h => by subst h; exact ⟨hpK, hp⟩⟩
  show (Classical.epsilon fun y : V3 => y ∈ K ∧ ∀ z ∈ K, dist x y ≤ dist x z) = p
  rw [heq]
  exact Classical.epsilon_singleton p

/-- Auxiliary for `XNHPWAB1`: affine-hull variant of
`AFFINE_HULL_PROJECTION_DIST_LT` (the public lemma freezes `v ∈ S`; here
`v` may be any point of the affine hull, as in Rogers.hl:6889). -/
private theorem p7_proj_dist_lt_affine (S : Set V3) (p v x n : V3)
    (hv : v ∈ (affineSpan ℝ S : Set V3)) (hp : ¬ p ∈ (affineSpan ℝ S : Set V3))
    (hpxn : p = x + n) (hx : x ∈ (affineSpan ℝ S : Set V3))
    (hn : ∀ u ∈ S, ∀ z ∈ S, (u - z) ⬝ᵥ n = 0) : dist x v < dist p v := by
  have horth := (ORTHOGONAL_TO_AFFINE_HULL_EQ S n).mp hn x hx v hv
  have hn0 : n ≠ 0 := by
    intro h0
    apply hp
    rw [hpxn, h0, add_zero]
    exact hx
  have hdeq : (p - v : V3) = (x - v) + n := by rw [hpxn]; abel
  have hpos : (0 : ℝ) < ‖n‖ ^ 2 := by
    have h1 : 0 < ‖n‖ := norm_pos_iff.mpr hn0
    nlinarith [sq_nonneg ‖n‖]
  have hsq : ‖x - v‖ ^ 2 < ‖(x - v) + n‖ ^ 2 := by
    rw [norm_add_sq_real, inner_eq_dot, horth]
    linarith [sq_nonneg ‖x - v‖, hpos]
  rw [dist_eq_norm, dist_eq_norm, hdeq]
  exact (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- HL `XNHPWAB1` (Rogers.hl:7194). -/
theorem XNHPWAB1 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    omegaList V ul = circumcenter (setOfList ul) := by
  classical
  revert hb
  revert hl2
  revert ul
  induction k with
  | zero =>
    intro ul hl2 hb
    have hlen : ul.length = 1 := hb.1
    have hset : setOfList ul = {hdV ul} := by
      have h1 : ul = [hdV ul] := LENGTH_1_LEMMA ul hlen
      rw [h1, show hdV [hdV ul] = hdV ul from by simp [hdV]]
      ext x
      simp [setOfList]
    have hw : omegaList V ul = hdV ul := by
      have hzero : ul.length - 1 = 0 := by omega
      calc omegaList V ul = omegaListN V ul (ul.length - 1) := rfl
        _ = omegaListN V ul 0 := by rw [hzero]
        _ = hdV ul := rfl
    rw [hw, hset, CIRCUMCENTER_1]
  | succ k ih =>
    intro ul hl2 hb
    have hlenU : ul.length = k + 1 + 1 := hb.1
    have hvb : barV V k (truncateSimplex k ul) :=
      TRUNCATE_SIMPLEX_BARV V k (k + 1) ul hb (by omega)
    have hlm : hl (truncateSimplex k ul) ≤ hl ul :=
      HL_DECREASE V ul (k + 1) k hV hb (by omega)
    have hlt : hl (truncateSimplex k ul) < Real.sqrt 2 := lt_of_le_of_lt hlm hl2
    have hihr : omegaList V (truncateSimplex k ul)
        = circumcenter (setOfList (truncateSimplex k ul)) :=
      ih (truncateSimplex k ul) hlt hvb
    have hsubV : setOfList (truncateSimplex k ul) ⊆ setOfList ul :=
      SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET ul k (by rw [hlenU]; omega)
    have hp0 : circumcenter (setOfList (truncateSimplex k ul)) ∈
        (affineSpan ℝ (setOfList ul) : Set V3) := by
      have h1 : (affineSpan ℝ (setOfList (truncateSimplex k ul)) : AffineSubspace ℝ V3) ≤
          (affineSpan ℝ (setOfList ul) : AffineSubspace ℝ V3) := affineSpan_mono ℝ hsubV
      exact h1 (BARV_CIRCUMCENTER_EXISTS V (truncateSimplex k ul) k hV hvb)
    have hvne : (voronoiList V ul).Nonempty := Set.nonempty_iff_ne_empty.mpr
      (BARV_IMP_VORONOI_LIST_NOT_EMPTY V ul (k + 1) hb)
    have hAne : ((affineSpan ℝ (voronoiList V ul) : AffineSubspace ℝ V3) : Set V3).Nonempty :=
      ⟨hvne.some, mem_affineSpan ℝ hvne.some_mem⟩
    have hAcv : Convex ℝ ((affineSpan ℝ (voronoiList V ul) : AffineSubspace ℝ V3) : Set V3) :=
      AffineSubspace.convex _
    have hAcl : IsClosed ((affineSpan ℝ (voronoiList V ul) : AffineSubspace ℝ V3) : Set V3) :=
      AffineSubspace.closed_of_finiteDimensional _
    obtain ⟨p, hpA, hpclose⟩ :
        ∃ q : V3, q ∈ ((affineSpan ℝ (voronoiList V ul) : AffineSubspace ℝ V3) : Set V3) ∧
          ∀ z ∈ ((affineSpan ℝ (voronoiList V ul) : AffineSubspace ℝ V3) : Set V3),
            dist (circumcenter (setOfList (truncateSimplex k ul))) q ≤
              dist (circumcenter (setOfList (truncateSimplex k ul))) z :=
      ⟨closestPoint _ _, p7_closest_point_exists _ _ hAne hAcl hAcv⟩
    have hhdmem : hdV ul ∈ setOfList ul := HD_IN_SET_OF_LIST ul (by rw [hlenU]; omega)
    have hpspan : p ∈ (affineSpan ℝ (setOfList ul) : Set V3) := by
      by_contra hcontra
      obtain ⟨x, n, hpxn, hx, horth⟩ := AFFINE_HULL_PROJECTION_EXISTS (setOfList ul) p
        (Set.nonempty_iff_ne_empty.mp ⟨hdV ul, hhdmem⟩)
      have hlt2 : dist x (circumcenter (setOfList (truncateSimplex k ul))) <
          dist p (circumcenter (setOfList (truncateSimplex k ul))) :=
        p7_proj_dist_lt_affine (setOfList ul) p
          (circumcenter (setOfList (truncateSimplex k ul))) x n
          hp0 hcontra hpxn hx horth
      have hxeq : ∀ u ∈ setOfList ul, dist x u = dist x (hdV ul) := by
        intro u hu
        have hpbis : dist p (hdV ul) = dist p u :=
          (MHFTTZN2 V ul (k + 1) hV hb p).mp hpA u hu
        exact AFFINE_HULL_PROJECTION_DIST_EQ (setOfList ul) p u (hdV ul) x n hu hhdmem
          hpbis.symm hpxn horth
      have hxA : x ∈ ((affineSpan ℝ (voronoiList V ul) : AffineSubspace ℝ V3) : Set V3) :=
        (MHFTTZN2 V ul (k + 1) hV hb x).mpr (fun u hu => (hxeq u hu).symm)
      rw [dist_comm x, dist_comm p] at hlt2
      exact absurd hlt2 (not_lt.mpr (hpclose x hxA))
    have hc : p = circumcenter (setOfList ul) := by
      have h2 := MHFTTZN3 V ul (k + 1) hV hb
      have hmem : p ∈ ((affineSpan ℝ (voronoiList V ul) : AffineSubspace ℝ V3) : Set V3) ∩
          (affineSpan ℝ (setOfList ul) : Set V3) := ⟨hpA, hpspan⟩
      rw [h2] at hmem
      exact Set.mem_singleton_iff.mp hmem
    have hpvl : p ∈ voronoiList V ul := by
      rw [hc]
      show (circumcenter (setOfList ul) : V3) ∈ ⋂₀ {voronoiClosed V v | v ∈ setOfList ul}
      rw [Set.mem_sInter]
      intro T hT
      obtain ⟨v, hv, rfl⟩ := by simpa using hT
      intro w hw
      by_cases hwS : w ∈ setOfList ul
      · have h1 := HL_PROPERTIES V ul (k + 1) hV hb v hv
        have h2 := HL_PROPERTIES V ul (k + 1) hV hb w hwS
        rw [h1, h2]
      · rw [dist_comm (circumcenter (setOfList ul)) v,
          dist_comm (circumcenter (setOfList ul)) w]
        exact le_of_lt (XYOFCGX V (setOfList ul) (circumcenter (setOfList ul)) hV
          (BARV_SUBSET V (k + 1) ul hb) (BARV_AFFINE_INDEPENDENT V ul (k + 1) hV hb) rfl hl2
          v w hv ⟨hw, hwS⟩)
    have homega : omegaListN V ul k = circumcenter (setOfList (truncateSimplex k ul)) := by
      rw [← hihr]
      exact (OMEGA_LIST_LEMMA V ul k (by rw [hlenU]; omega)).symm
    have htrunc : truncateSimplex (k + 1) ul = ul :=
      ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST (k + 1) ul ul).mpr
        ⟨⟨[], by simp⟩, hb.1⟩).1
    have hfinal : omegaList V ul = p := by
      have e1 : omegaList V ul = omegaListN V ul (k + 1) := by
        show omegaListN V ul (ul.length - 1) = omegaListN V ul (k + 1)
        rw [show ul.length - 1 = k + 1 from by rw [hlenU]; omega]
      rw [e1, omegaListN, htrunc, homega]
      exact p7_closest_point_unique (voronoiList V ul) _ p (CONVEX_VORONOI_LIST V ul) hpvl
        (fun z hz => hpclose z (subset_affineSpan ℝ (voronoiList V ul) hz))
    rw [hfinal, hc]

/-! ## AFFINE_HULL_PROJECTION_SEPARATES .. AFFINE_HULL_VORONOI_LIST_SUBSET_INTERS_BIS -/

/-! ### 私件：V3 (WithLp) 点积运输 kit

`⬝ᵥ` 是 pi 型 `dotProduct`（参数自动插入 `WithLp.ofLp`），V3 上没有现成的
Finset-和交换引理（Mathlib 的 `sum_dotProduct` 是纯 pi 型）。以下私件经
coercion 搬运 add/smul/sum，采用 `Kepler/Geom/AzimLemmas.lean` 的
`WithLp.ofLp_*` 模式。 -/

/-- Dot symmetry at `V3`. -/
private theorem p7_dot_comm (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

/-- Scalar action in the left dot argument at `V3`. -/
private theorem p7_smul_dot_left (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) :=
  smul_dotProduct t (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)

/-- Distributivity in the left dot argument at `V3`. -/
private theorem p7_add_dot_left (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c := by
  simp only [WithLp.ofLp_add, add_dotProduct]

/-- Finset-sum exchange in the left dot argument at `V3` (by Finset induction,
since the `V3`-sum and the pi-sum live in different `AddCommMonoid` instances). -/
private theorem p7_sum_dot_left {ι : Type*} (s : Finset ι) (f : ι → V3) (c : V3) :
    ((∑ j ∈ s, f j : V3)) ⬝ᵥ c = ∑ j ∈ s, (f j ⬝ᵥ c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, p7_add_dot_left, ih]

-- RESOLVED (2026-10-12 PA7 r3 lane): 权重分解走 `mem_affineSpan_iff_eq_affineCombination`
-- (ι := ↥S, p := Subtype.val) + 负权重抽取用 `Finset.centerMass_mem_convexHull`
-- (凸包侧); V3 点积-和交换由上方 p7_ 私件 kit 解决 (Finset 归纳 + WithLp.ofLp 模式).
/-- HL `AFFINE_HULL_PROJECTION_SEPARATES` (Rogers.hl:7431). -/
theorem AFFINE_HULL_PROJECTION_SEPARATES (S : Set V3) (p : V3) (hfin : S.Finite)
    (hp : p ∈ (affineSpan ℝ S : Set V3)) (hnc : ¬ p ∈ convexHull ℝ S) :
    ∃ u ∈ S, ∀ x n : V3, p = x + n → x ∈ (affineSpan ℝ (S \ {u}) : Set V3) →
      (∀ v ∈ S \ {u}, ∀ w ∈ S \ {u}, (v - w) ⬝ᵥ n = 0) →
        (p - x) ⬝ᵥ (u - x) ≤ 0 := by
  classical
  have hne : S.Nonempty := by
    by_contra hcon
    push_neg at hcon
    rw [hcon, AffineSubspace.span_empty, AffineSubspace.bot_coe] at hp
    exact absurd hp (Set.notMem_empty p)
  have hrange : Set.range (Subtype.val : S → V3) = S := Subtype.range_val
  rw [← hrange] at hp
  obtain ⟨s, w, hwsum, hpw⟩ :=
    (mem_affineSpan_iff_eq_affineCombination (k := ℝ) (V := V3) (P := V3) (p1 := p)
      (p := (Subtype.val : S → V3))).mp hp
  have h1 : s.affineCombination ℝ (Subtype.val : S → V3) w = ∑ j ∈ s, w j • ((j : V3)) :=
    s.affineCombination_eq_linear_combination (Subtype.val : S → V3) w hwsum
  have hpc : ∑ j ∈ s, w j • ((j : V3)) = p := h1.symm.trans hpw.symm
  have hall : ∃ j ∈ s, w j < 0 := by
    by_contra hcon
    push_neg at hcon
    refine hnc ?_
    have hcm : s.centerMass w (fun x : S => (x : V3)) ∈ convexHull ℝ S :=
      s.centerMass_mem_convexHull hcon (by rw [hwsum]; positivity) (fun j _ => j.property)
    have hcmeq : s.centerMass w (fun x : S => (x : V3)) = p := by
      have hz : s.centerMass w (fun x : S => (x : V3))
          = ∑ j ∈ s, w j • ((j : V3)) :=
        s.centerMass_eq_of_sum_1 (fun x : S => (x : V3)) hwsum
      rw [hz, hpc]
    rwa [hcmeq] at hcm
  obtain ⟨i, his, hwi⟩ := hall
  refine ⟨(i : V3), i.property, ?_⟩
  intro x n hpxn hxspan horth
  have hsubn : n = p - x := by rw [hpxn]; abel
  have hsum : ∑ j ∈ s, w j • ((j : V3) - x) = n := by
    calc ∑ j ∈ s, w j • ((j : V3) - x)
        = ∑ j ∈ s, (w j • (j : V3) - w j • x) :=
          Finset.sum_congr rfl (fun j _ => smul_sub _ _ _)
      _ = (∑ j ∈ s, w j • (j : V3)) - (∑ j ∈ s, w j • x) :=
          Finset.sum_sub_distrib (fun j => w j • (j : V3)) (fun j => w j • x)
      _ = p - (∑ j ∈ s, w j) • x := by rw [hpc, Finset.sum_smul]
      _ = p - x := by rw [hwsum, one_smul]
      _ = n := hsubn.symm
  have hdot : n ⬝ᵥ n = ∑ j ∈ s, w j * (((j : V3) - x) ⬝ᵥ n) := by
    calc n ⬝ᵥ n = ((∑ j ∈ s, w j • ((j : V3) - x) : V3)) ⬝ᵥ n := by rw [hsum]
      _ = ∑ j ∈ s, ((w j • ((j : V3) - x)) ⬝ᵥ n) := p7_sum_dot_left _ _ _
      _ = ∑ j ∈ s, w j * (((j : V3) - x) ⬝ᵥ n) :=
          Finset.sum_congr rfl
            (fun j _ => p7_smul_dot_left (w j) ((j : V3) - x) n)
  have hzero : ∀ j ∈ s, (j : V3) ≠ (i : V3) → ((j : V3) - x) ⬝ᵥ n = 0 := by
    intro j hj hjne
    have hjS : (j : V3) ∈ S \ {(i : V3)} :=
      ⟨j.property, fun hh => hjne (Set.mem_singleton_iff.mp hh)⟩
    exact (ORTHOGONAL_TO_AFFINE_HULL_EQ (S \ {(i : V3)}) n).mp horth (j : V3)
      (mem_affineSpan ℝ hjS) x hxspan
  have hnn : 0 ≤ n ⬝ᵥ n := by rw [← norm_sq_eq_dot n]; exact sq_nonneg _
  have hkey : ((i : V3) - x) ⬝ᵥ n ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have hneg : w i * (((i : V3) - x) ⬝ᵥ n) < 0 := mul_neg_of_neg_of_pos hwi hcon
    have hsingle : ∑ j ∈ s, w j * (((j : V3) - x) ⬝ᵥ n)
        = w i * (((i : V3) - x) ⬝ᵥ n) :=
      Finset.sum_eq_single_of_mem i his
        (fun j hj hjne => by
          rw [hzero j hj (fun hh => hjne (Subtype.ext hh)), mul_zero])
    rw [hsingle] at hdot
    linarith
  rw [← hsubn, p7_dot_comm]
  exact hkey

-- RESOLVED (2026-10-12 PA7 r3 lane): 按 HOL 原证路线 (AFFINE_HULL_PROJECTION_
-- SEPARATES + AFFINE_HULL_CIRCUMCENTER_PROJECTION + OAPVION1/2 + XYOFCGX) 填证.
-- 历史侦察记录: "取 conv S 最近点 q" 替代路线不通 (法锥不等式 ⟨p-q, z-q⟩ ≤ 0
-- 不蕴含 ⊥ 差分), 未采用.
/-- HL `XNHPWAB2` (Rogers.hl:7497). -/
theorem XNHPWAB2 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    omegaList V ul ∈ convexHull ℝ (setOfList ul) := by
  classical
  by_cases hmem : omegaList V ul ∈ convexHull ℝ (setOfList ul)
  · exact hmem
  · have hc : omegaList V ul = circumcenter (setOfList ul) := XNHPWAB1 V ul k hV hb hl2
    have hind : ¬ affineDependent (setOfList ul) := BARV_AFFINE_INDEPENDENT V ul k hV hb
    have hSV : setOfList ul ⊆ V := BARV_SUBSET V k ul hb
    have hfin : (setOfList ul).Finite :=
      finite_set_of_fin_dim_affineIndependent (k := ℝ) (not_not.mp hind)
    obtain ⟨u, huS, husep⟩ := AFFINE_HULL_PROJECTION_SEPARATES (setOfList ul)
      (omegaList V ul) hfin
      (by rw [hc]; exact BARV_CIRCUMCENTER_EXISTS V ul k hV hb) hmem
    by_cases hdel : setOfList ul \ {u} = ∅
    · -- `S` is a singleton: `omegaList = u ∈ convex hull {u}`
      have hSu : setOfList ul = {u} :=
        Set.Subset.antisymm (fun x hx => by
          by_contra hne
          have hxx : x ∈ setOfList ul \ {u} := ⟨hx, hne⟩
          rw [hdel] at hxx
          exact absurd hxx (Set.notMem_empty x)) (Set.singleton_subset_iff.mpr huS)
      have hpu : omegaList V ul = u := by
        rw [hc, hSu, CIRCUMCENTER_1]
      refine absurd ?_ hmem
      rw [hpu, hSu, convexHull_singleton]
      exact Set.mem_singleton u
    · -- main case: project the circumcenter of `S \ {u}`
      have hne : setOfList ul \ {u} ≠ ∅ := hdel
      have hind_t : ¬ affineDependent (setOfList ul \ {u}) :=
        p7_hind_subset (setOfList ul) (setOfList ul \ {u}) hind (Set.diff_subset)
      obtain ⟨n0, hdec, hn0⟩ := AFFINE_HULL_CIRCUMCENTER_PROJECTION (setOfList ul)
        (setOfList ul \ {u}) hind (Set.diff_subset) hne
      obtain ⟨v, hvdel⟩ := Set.nonempty_iff_ne_empty.mpr hne
      set p0 : V3 := circumcenter (setOfList ul \ {u}) with hp0def
      have hvS : v ∈ setOfList ul := Set.diff_subset hvdel
      have hp0mem : p0 ∈ (affineSpan ℝ (setOfList ul \ {u}) : Set V3) :=
        OAPVION1 (setOfList ul \ {u}) hne hind_t
      have hvmem : v ∈ (affineSpan ℝ (setOfList ul \ {u}) : Set V3) :=
        mem_affineSpan ℝ hvdel
      have horth := (ORTHOGONAL_TO_AFFINE_HULL_EQ (setOfList ul \ {u}) n0).mp hn0
      have hpe : omegaList V ul = p0 + n0 := hc.trans hdec
      have hsubn : (p0 - omegaList V ul : V3) = -n0 := by rw [hpe]; abel
      have hnn0 : dist p0 (omegaList V ul) = ‖n0‖ := by
        rw [dist_eq_norm, hsubn, norm_neg]
      have hdec1 : ((p0 + n0) - v : V3) = (p0 - v) + n0 := by abel
      have hA : dist (omegaList V ul) v ^ 2 = dist p0 v ^ 2 + ‖n0‖ ^ 2 := by
        rw [dist_eq_norm, dist_eq_norm, hpe, hdec1, norm_add_sq_real, inner_eq_dot,
          horth p0 hp0mem v hvmem]
        ring
      have hdec2 : ((p0 + n0) - u : V3) = (p0 - u) + n0 := by abel
      have hB : dist (omegaList V ul) u ^ 2
          = dist p0 u ^ 2 + ‖n0‖ ^ 2 + 2 * ((p0 - u) ⬝ᵥ n0) := by
        rw [dist_eq_norm, dist_eq_norm, hpe, hdec2, norm_add_sq_real, inner_eq_dot]
        ring
      have hpu : dist (omegaList V ul) u = dist (omegaList V ul) v := by
        rw [hc, ← OAPVION2_concl (setOfList ul) hind u huS,
          ← OAPVION2_concl (setOfList ul) hind v hvS]
      have hsep := husep p0 n0 hpe hp0mem hn0
      have hcross : 0 ≤ (p0 - u) ⬝ᵥ n0 := by
        have h1' : (omegaList V ul - p0 : V3) = n0 := by rw [hpe]; abel
        have h0 : ((n0 : V3)) ⬝ᵥ ((u - p0 : V3))
            = ((u - p0 : V3)) ⬝ᵥ ((n0 : V3)) := p7_dot_comm n0 (u - p0)
        have hsep2 : (u - p0) ⬝ᵥ n0 ≤ 0 := by
          rw [← h0]
          have h5 : ((n0 : V3)) ⬝ᵥ ((u - p0 : V3))
              = ((omegaList V ul - p0 : V3)) ⬝ᵥ ((u - p0 : V3)) := by rw [h1']
          rw [h5]
          exact hsep
        have hcomm : (p0 - u) ⬝ᵥ n0 + (u - p0) ⬝ᵥ n0 = 0 := by
          have e1 : (p0 - u) ⬝ᵥ n0 = (p0 ⬝ᵥ n0) - (u ⬝ᵥ n0) := by
            rw [← inner_eq_dot (p0 - u) n0, ← inner_eq_dot p0 n0, ← inner_eq_dot u n0,
              inner_sub_left]
          have e3 : (u - p0) ⬝ᵥ n0 = (u ⬝ᵥ n0) - (p0 ⬝ᵥ n0) := by
            rw [← inner_eq_dot (u - p0) n0, ← inner_eq_dot u n0, ← inner_eq_dot p0 n0,
              inner_sub_left]
          rw [e1, e3]
          ring
        linarith
      have hsq : dist p0 u ^ 2 ≤ dist p0 v ^ 2 := by
        have hpu2 : dist (omegaList V ul) u ^ 2 = dist (omegaList V ul) v ^ 2 := by
          rw [hpu]
        have e2 : dist p0 u ^ 2
            = dist (omegaList V ul) u ^ 2 - ‖n0‖ ^ 2 - 2 * ((p0 - u) ⬝ᵥ n0) := by
          linarith [hB]
        linarith [hA, hpu2, hcross, e2]
      have hr2 : radV (setOfList ul \ {u}) < Real.sqrt 2 :=
        lt_of_le_of_lt (RADV_MONO (setOfList ul) (setOfList ul \ {u}) hind
          (Set.diff_subset) hne) hl2
      have hu' : u ∈ V \ (setOfList ul \ {u}) :=
        ⟨hSV huS, fun hh => hh.2 rfl⟩
      have hxy := XYOFCGX V (setOfList ul \ {u}) p0 hV
        (Set.diff_subset.trans hSV) hind_t rfl hr2 v u hvdel hu'
      rw [dist_comm u p0, dist_comm v p0] at hxy
      have hle : dist p0 u ≤ dist p0 v := by
        have g1 := dist_nonneg (x := p0) (y := u)
        have g2 := dist_nonneg (x := p0) (y := v)
        nlinarith
      linarith

/-- HL `XNHPWAB4` (Rogers.hl:7691): the truncated circumradii increase
strictly. -/
theorem XNHPWAB4 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    ∀ i j : ℕ, i < j → j ≤ k →
      hl (truncateSimplex i ul) < hl (truncateSimplex j ul) := by
  intro i j hij hjk
  have hblen : ul.length = k + 1 := hb.1
  have hbj : barV V j (truncateSimplex j ul) := TRUNCATE_SIMPLEX_BARV V j k ul hb hjk
  have hbi : barV V i (truncateSimplex i ul) :=
    TRUNCATE_SIMPLEX_BARV V i k ul hb (le_trans (le_of_lt hij) hjk)
  have hlenj : (truncateSimplex j ul).length = j + 1 := hbj.1
  have hleni : (truncateSimplex i ul).length = i + 1 := hbi.1
  have hlsj : hl (truncateSimplex j ul) < Real.sqrt 2 :=
    lt_of_le_of_lt (HL_DECREASE V ul k j hV hb hjk) hl2
  have hlsi : hl (truncateSimplex i ul) < Real.sqrt 2 :=
    lt_of_le_of_lt (HL_DECREASE V ul k i hV hb (le_trans (le_of_lt hij) hjk)) hl2
  have htr : truncateSimplex i (truncateSimplex j ul) = truncateSimplex i ul :=
    TRUNCATE_TRUNCATE_SIMPLEX ul i j (le_of_lt hij) (by omega)
  have hsub : setOfList (truncateSimplex i ul) ⊆ setOfList (truncateSimplex j ul) := by
    rw [← htr]
    exact SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET (truncateSimplex j ul) i (by rw [hlenj]; omega)
  have hyne : setOfList (truncateSimplex i ul) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp ⟨hdV (truncateSimplex i ul),
      HD_IN_SET_OF_LIST _ (by rw [hleni]; omega)⟩
  have hinx : ¬ affineDependent (setOfList (truncateSimplex j ul)) :=
    BARV_AFFINE_INDEPENDENT V (truncateSimplex j ul) j hV hbj
  have hiny : ¬ affineDependent (setOfList (truncateSimplex i ul)) :=
    BARV_AFFINE_INDEPENDENT V (truncateSimplex i ul) i hV hbi
  obtain ⟨v, hvx, hvy⟩ : ∃ v ∈ setOfList (truncateSimplex j ul),
      v ∉ setOfList (truncateSimplex i ul) := by
    by_contra hcon
    push_neg at hcon
    have heq : setOfList (truncateSimplex j ul) = setOfList (truncateSimplex i ul) :=
      Set.Subset.antisymm hcon hsub
    have h1 := MHFTTZN1 V (truncateSimplex j ul) j hV hbj
    have h2 := MHFTTZN1 V (truncateSimplex i ul) i hV hbi
    rw [heq] at h1
    have h3 : (i : ℤ) = (j : ℤ) := h2.symm.trans h1
    omega
  by_cases hd0 : dist (circumcenter (setOfList (truncateSimplex i ul)))
      (circumcenter (setOfList (truncateSimplex j ul))) = 0
  · -- same circumcenter: strict inequality from the XYOFCGX gap at the extra vertex
    have hcxy : circumcenter (setOfList (truncateSimplex i ul))
        = circumcenter (setOfList (truncateSimplex j ul)) := dist_eq_zero.mp hd0
    have hxy := XYOFCGX V (setOfList (truncateSimplex i ul))
      (circumcenter (setOfList (truncateSimplex i ul))) hV
      (BARV_SUBSET V i (truncateSimplex i ul) hbi) hiny rfl hlsi
      (hdV (truncateSimplex i ul)) v
      (HD_IN_SET_OF_LIST _ (by rw [hleni]; omega))
      ⟨BARV_SUBSET V j (truncateSimplex j ul) hbj hvx, hvy⟩
    have hdydx : hdV (truncateSimplex i ul) = hdV (truncateSimplex j ul) := by
      rw [HD_TRUNCATE_SIMPLEX ul i (by omega),
        HD_TRUNCATE_SIMPLEX ul j (by omega)]
    have hr1 : radV (setOfList (truncateSimplex i ul))
        = dist (circumcenter (setOfList (truncateSimplex i ul)))
            (hdV (truncateSimplex i ul)) :=
      OAPVION2_concl _ hiny _ (HD_IN_SET_OF_LIST _ (by rw [hleni]; omega))
    have hr2 : radV (setOfList (truncateSimplex j ul))
        = dist (circumcenter (setOfList (truncateSimplex j ul))) v :=
      OAPVION2_concl _ hinx _ hvx
    rw [hcxy, hdydx] at hxy
    show radV (setOfList (truncateSimplex i ul)) < radV (setOfList (truncateSimplex j ul))
    rw [hr1, hr2, hcxy, hdydx,
      dist_comm (circumcenter (setOfList (truncateSimplex j ul)))
        (hdV (truncateSimplex j ul)),
      dist_comm (circumcenter (setOfList (truncateSimplex j ul))) v]
    exact hxy
  · -- different centers: Pythagoras gives the strict square inequality
    have hA := AFFINE_HULL_RADV (setOfList (truncateSimplex j ul))
      (setOfList (truncateSimplex i ul)) hinx hsub hyne
    have hd : 0 < dist (circumcenter (setOfList (truncateSimplex i ul)))
        (circumcenter (setOfList (truncateSimplex j ul))) :=
      lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
    have hsq : radV (setOfList (truncateSimplex i ul)) ^ 2
        < radV (setOfList (truncateSimplex j ul)) ^ 2 := by
      rw [hA.1]
      have hdp : 0 < dist (circumcenter (setOfList (truncateSimplex i ul)))
          (circumcenter (setOfList (truncateSimplex j ul))) ^ 2 :=
        pow_pos hd 2
      linarith [hA.2.2]
    show radV (setOfList (truncateSimplex i ul)) < radV (setOfList (truncateSimplex j ul))
    exact (sq_lt_sq₀ hA.2.2 hA.2.1).mp hsq

/-- HL `OMEGA_LIST_N_IN_CONVEX_HULL` (Rogers.hl:7869). -/
theorem OMEGA_LIST_N_IN_CONVEX_HULL (V : Set V3) (ul : List V3) (k i : ℕ)
    (hV : Packing V) (hb : barV V k ul) (hik : i ≤ k)
    (hl2 : hl ul < Real.sqrt 2) :
    omegaListN V ul i ∈ convexHull ℝ (setOfList ul) := by
  have hblen : ul.length = k + 1 := hb.1
  have hbvl : barV V i (truncateSimplex i ul) := TRUNCATE_SIMPLEX_BARV V i k ul hb hik
  have heq : omegaListN V ul i = omegaList V (truncateSimplex i ul) :=
    (OMEGA_LIST_LEMMA V ul i (by rw [hblen]; omega)).symm
  rw [heq]
  have hl2i : hl (truncateSimplex i ul) < Real.sqrt 2 :=
    lt_of_le_of_lt (HL_DECREASE V ul k i hV hb hik) hl2
  have hsub : setOfList (truncateSimplex i ul) ⊆ setOfList ul :=
    SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET ul i (by rw [hblen]; omega)
  exact convexHull_mono hsub (XNHPWAB2 V (truncateSimplex i ul) i hV hbvl hl2i)

/-- Re-splice of PackingAuto6/18's private `p6/pa18_affDim_insert` (HOL
`AFF_DIM_INSERT` content): inserting a point outside the affine span raises
the affine dimension by one. -/
private theorem p7_affDim_insert (S : Set V3) (y : V3) (hne : S.Nonempty)
    (hy : y ∉ (affineSpan ℝ S : Set V3)) :
    affDim (insert y S) = affDim S + 1 := by
  obtain ⟨y0, hy0⟩ := hne
  have hy0S : y0 ∈ (affineSpan ℝ S : Set V3) := subset_affineSpan ℝ S hy0
  set D := vectorSpan ℝ S with hD
  have mD : ∀ a ∈ S, ∀ b ∈ S, (a - b) ∈ D := by
    intro a ha b hb
    rw [hD, vectorSpan_def]
    exact Submodule.subset_span (Set.mem_vsub.2 ⟨a, ha, b, hb, rfl⟩)
  have hvec : vectorSpan ℝ (insert y S) = D ⊔ Submodule.span ℝ {y - y0} := by
    have hgen : (y - y0) ∈ vectorSpan ℝ (insert y S) := by
      rw [vectorSpan_def]
      exact Submodule.subset_span (Set.mem_vsub.2 ⟨y, Set.mem_insert _ _,
        y0, Set.mem_insert_of_mem _ hy0, rfl⟩)
    have hmono : vectorSpan ℝ S ≤ vectorSpan ℝ (insert y S) :=
      vectorSpan_mono (k := ℝ) (Set.subset_insert y S)
    have hsb : ∀ r ∈ Submodule.span ℝ {y - y0}, r ∈ vectorSpan ℝ (insert y S) := by
      intro r hm
      rw [Submodule.mem_span_singleton] at hm
      obtain ⟨s, rfl⟩ := hm
      exact Submodule.smul_mem _ s hgen
    refine le_antisymm ?_ ?_
    · rw [vectorSpan_def, Submodule.span_le]
      intro g hg
      obtain ⟨x, hx, x', hx', rfl⟩ := Set.mem_vsub.1 hg
      rw [SetLike.mem_coe]
      rcases Set.mem_insert_iff.1 hx with hxe | hx
      · rcases Set.mem_insert_iff.1 hx' with hxe' | hx'
        · rw [hxe, hxe', vsub_self]
          exact Submodule.zero_mem _
        · rw [hxe, vsub_eq_sub]
          have hv : (y - x' : V3) = (y - y0) + -(x' - y0) := by abel
          have hA : (x' - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_left (mD x' hx' y0 hy0)
          have hC : (y - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_right (Submodule.subset_span
              (Set.mem_singleton (y - y0)))
          rw [hv]
          exact Submodule.add_mem (D ⊔ Submodule.span ℝ {y - y0}) hC
            (Submodule.neg_mem (D ⊔ Submodule.span ℝ {y - y0}) hA)
      · rcases Set.mem_insert_iff.1 hx' with hxe' | hx'
        · rw [hxe', vsub_eq_sub]
          have hv : (x - y : V3) = (x - y0) + -(y - y0) := by abel
          have hA : (x - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_left (mD x hx y0 hy0)
          have hC : (y - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_right (Submodule.subset_span
              (Set.mem_singleton (y - y0)))
          rw [hv]
          exact Submodule.add_mem (D ⊔ Submodule.span ℝ {y - y0}) hA
            (Submodule.neg_mem (D ⊔ Submodule.span ℝ {y - y0}) hC)
        · exact Submodule.mem_sup_left (mD x hx x' hx')
    · intro w hw
      rcases Submodule.mem_sup.1 hw with ⟨a, ha, b, hb, hab⟩
      have haD : a ∈ vectorSpan ℝ (insert y S) := hmono ha
      have hbD : b ∈ vectorSpan ℝ (insert y S) := hsb b hb
      rw [← hab]
      exact add_mem haD hbD
  have hvD : y - y0 ∉ D := by
    intro h
    apply hy
    have hmem : (y - y0) +ᵥ y0 ∈ (affineSpan ℝ S : Set V3) :=
      AffineSubspace.vadd_mem_of_mem_direction
        (by rw [direction_affineSpan]; exact h) hy0S
    have h2 : (y - y0 : V3) +ᵥ y0 = y := by rw [vadd_eq_add]; abel
    rw [h2] at hmem
    exact hmem
  have hinf : D ⊓ Submodule.span ℝ {y - y0} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwK : w ∈ D := (Submodule.mem_inf.1 hw).1
    have hwS := (Submodule.mem_inf.1 hw).2
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hwS
    have hs0 : s = 0 := by
      by_contra hs0
      have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0
      have h2 : (s⁻¹ • (s • (y - y0)) : V3) ∈ D := Submodule.smul_mem _ _ hwK
      rw [smul_smul, hinv, one_smul] at h2
      exact hvD h2
    rw [hs0, zero_smul]
  have hvyne : (y - y0 : V3) ≠ 0 := by
    intro h0
    rw [h0] at hvD
    exact hvD (Submodule.zero_mem D)
  have hfr : Module.finrank ℝ (vectorSpan ℝ (insert y S))
      = Module.finrank ℝ (vectorSpan ℝ S) + 1 := by
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq D (Submodule.span ℝ {y - y0})
    rw [hinf, finrank_bot] at h2
    have h3 : Module.finrank ℝ (Submodule.span ℝ {y - y0}) = 1 :=
      finrank_span_singleton hvyne
    rw [h3] at h2
    rw [hvec]
    omega
  have hneI : (insert y S).Nonempty := ⟨y0, Set.mem_insert_of_mem _ hy0⟩
  have hneI' : insert y S ≠ ∅ := Set.nonempty_iff_ne_empty.mp hneI
  simp only [affDim, if_neg hneI', if_neg (Set.nonempty_iff_ne_empty.mp ⟨y0, hy0⟩)]
  rw [hfr]
  omega

/-- HL `XNHPWAB3` (Rogers.hl:7926). RESOLVED (2026-10-12 PA7 r3 lane): HOL 的
k-归纳 — 归纳步将 `S_{k+1}` 拆为插入点 `omegaListN V ul (k+1)`（= circumcenter
ul，经 XNHPWAB1）与 `S_k(vl)`（vl = truncate k ul，经 OMEGA_LIST_N_LEMMA），
插入点在 `S_k(vl)` 的仿射包之外由反证：若在则经
`OMEGA_LIST_N_IN_CONVEX_HULL` + `AFFINE_HULL_CIRCUMCENTER_EQ` 得
circumcenter ul = circumcenter vl，与 `HL_PROPERTIES` + `XNHPWAB4` 的严格
递增矛盾；插入分支用 `p7_affDim_insert`（PA6/PA18 私件的重接副本）。-/
theorem XNHPWAB3 (V : Set V3) (ul : List V3) (k : ℕ) (hV : Packing V)
    (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2) :
    affDim {omegaListN V ul j | j ∈ Finset.Icc 0 k} = (k : ℤ) := by
  classical
  revert hb
  revert hl2
  revert ul
  induction k with
  | zero =>
    intro ul hl2 hb
    have hset : {omegaListN V ul j | j ∈ Finset.Icc 0 0} = {omegaListN V ul 0} := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        have h0 : j = 0 :=
          le_antisymm (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hj).1
        rw [h0]
        rfl
      · intro h
        exact ⟨0, Finset.mem_Icc.2 ⟨Nat.zero_le 0, Nat.zero_le 0⟩, h.symm⟩
    rw [hset, affDim_singleton]
    norm_num
  | succ k ih =>
    intro ul hl2 hb
    have hlenU : ul.length = k + 1 + 1 := hb.1
    set vl := truncateSimplex k ul with hvldef
    have hbvl : barV V k vl := TRUNCATE_SIMPLEX_BARV V k (k + 1) ul hb (by omega)
    have hlenV : vl.length = k + 1 := hbvl.1
    have hl2v : hl vl < Real.sqrt 2 :=
      lt_of_le_of_lt (HL_DECREASE V ul (k + 1) k hV hb (by omega)) hl2
    have ihv := ih vl hl2v hbvl
    have hstep : ∀ j ≤ k, omegaListN V vl j = omegaListN V ul j := by
      intro j hj
      have h1 := OMEGA_LIST_N_LEMMA V ul j (k - j) (by rw [hlenU]; omega)
      rw [show j + (k - j) = k from by omega] at h1
      exact h1.symm
    have hSset : {omegaListN V ul j | j ∈ Finset.Icc 0 (k + 1)}
        = insert (omegaListN V ul (k + 1))
            {omegaListN V vl j | j ∈ Finset.Icc 0 k} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨j, hj, rfl⟩
        have hjle : j ≤ k + 1 := (Finset.mem_Icc.mp hj).2
        rcases eq_or_lt_of_le hjle with hjk | hjk
        · rw [hjk]
          exact Or.inl rfl
        · have hjk1 : j ≤ k := by omega
          exact Or.inr ⟨j, Finset.mem_Icc.2 ⟨Nat.zero_le j, hjk1⟩, hstep j hjk1⟩
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨k + 1, Finset.mem_Icc.2 ⟨Nat.zero_le _, by omega⟩, rfl⟩
        · have hjk1 : j ≤ k := (Finset.mem_Icc.mp hj).2
          exact ⟨j, Finset.mem_Icc.2 ⟨Nat.zero_le j, by omega⟩, (hstep j hjk1).symm⟩
    have hcvsub : (convexHull ℝ (setOfList vl) : Set V3) ⊆
        (affineSpan ℝ (setOfList vl) : Set V3) :=
      convexHull_min (subset_affineSpan ℝ (setOfList vl)) (AffineSubspace.convex _)
    have hspanle : ∀ x ∈ {omegaListN V vl j | j ∈ Finset.Icc 0 k},
        x ∈ (affineSpan ℝ (setOfList vl) : Set V3) := by
      intro x hx
      rcases hx with ⟨j, hj, rfl⟩
      have hjk1 : j ≤ k := (Finset.mem_Icc.mp hj).2
      exact hcvsub (OMEGA_LIST_N_IN_CONVEX_HULL V vl k j hV hbvl hjk1 hl2v)
    have hind : ¬ affineDependent (setOfList ul) :=
      BARV_AFFINE_INDEPENDENT V ul (k + 1) hV hb
    have hvlne : setOfList vl ≠ ∅ :=
      Set.nonempty_iff_ne_empty.mp ⟨hdV vl, HD_IN_SET_OF_LIST vl (by rw [hlenV]; omega)⟩
    have hsub2 : setOfList vl ⊆ setOfList ul :=
      SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET ul k (by rw [hlenU]; omega)
    have hxomega : omegaListN V ul (k + 1) = omegaList V ul := by
      rw [show omegaList V ul = omegaListN V ul (ul.length - 1) from rfl,
        show ul.length - 1 = k + 1 from by rw [hlenU]; omega]
    have hx1 : omegaList V ul = circumcenter (setOfList ul) := XNHPWAB1 V ul (k + 1) hV hb hl2
    have hxnotmem : omegaListN V ul (k + 1) ∉
        (affineSpan ℝ {omegaListN V vl j | j ∈ Finset.Icc 0 k} : Set V3) := by
      intro hmem
      rw [hxomega, hx1] at hmem
      have hle : (affineSpan ℝ {omegaListN V vl j | j ∈ Finset.Icc 0 k} :
          AffineSubspace ℝ V3) ≤ (affineSpan ℝ (setOfList vl) : AffineSubspace ℝ V3) :=
        affineSpan_le.mpr (fun x hx => hspanle x hx)
      have hceq : circumcenter (setOfList ul) = circumcenter (setOfList vl) := by
        refine AFFINE_HULL_CIRCUMCENTER_EQ (setOfList ul) (setOfList vl) hind hsub2 hvlne ?_
        exact hle hmem
      have hHd : hdV vl ∈ setOfList vl := HD_IN_SET_OF_LIST vl (by rw [hlenV]; omega)
      have hdVeq : hdV vl = hdV ul := HD_TRUNCATE_SIMPLEX ul k (by omega)
      have hlU : dist (circumcenter (setOfList ul)) (hdV vl) = hl ul := by
        rw [hdVeq]
        exact HL_PROPERTIES V ul (k + 1) hV hb (hdV ul)
          (HD_IN_SET_OF_LIST ul (by rw [hlenU]; omega))
      have hlV : dist (circumcenter (setOfList vl)) (hdV vl) = hl vl :=
        HL_PROPERTIES V vl k hV hbvl (hdV vl) hHd
      have htru : truncateSimplex (k + 1) ul = ul :=
        ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST (k + 1) ul ul).mpr ⟨⟨[], by simp⟩, hlenU⟩).1
      have hstrict := XNHPWAB4 V ul (k + 1) hV hb hl2 k (k + 1) (by omega) (by omega)
      rw [htru] at hstrict
      rw [hceq] at hlU
      linarith
    rw [hSset, p7_affDim_insert {omegaListN V vl j | j ∈ Finset.Icc 0 k}
      (omegaListN V ul (k + 1))
      ⟨omegaListN V vl 0, ⟨0, Finset.mem_Icc.2 ⟨Nat.zero_le 0, by omega⟩, rfl⟩⟩
      hxnotmem, ihv]
    norm_num

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
  rw [HL_EQ_DIST0 V k ul hV hb, XNHPWAB1 V ul k hV hb hl2]

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
  have hxt : x ∈ t := by
    have h1 : x ∈ s ∩ Metric.ball x r := ⟨hx, Metric.mem_ball.mpr (by simpa using hr)⟩
    rw [heq] at h1
    exact h1.1
  obtain ⟨Ks, rfl⟩ := hs
  obtain ⟨Kt, rfl⟩ := ht
  -- the shift `p ↦ p - x` carries a carrier through `x` onto its direction
  have shift : ∀ K : AffineSubspace ℝ V3, x ∈ K →
      ∃ L : Submodule ℝ V3, (L : Set V3) = (fun p : V3 => p - x) '' (K : Set V3) := by
    intro K hxK
    refine ⟨K.direction, ?_⟩
    ext q
    constructor
    · intro hq
      exact ⟨q + x, AffineSubspace.vadd_mem_of_mem_direction hq hxK, by simp⟩
    · rintro ⟨p, hp, rfl⟩
      exact AffineSubspace.vsub_mem_direction hp hxK
  obtain ⟨Ls, hLs⟩ := shift Ks hx
  obtain ⟨Lt, hLt⟩ := shift Kt hxt
  -- the ball intersection transfers through the shift
  have key : ∀ K₁ K₂ : AffineSubspace ℝ V3,
      (K₁ : Set V3) ∩ Metric.ball x r = (K₂ : Set V3) ∩ Metric.ball x r →
      ((fun p : V3 => p - x) '' (K₁ : Set V3)) ∩ Metric.ball 0 r =
        ((fun p : V3 => p - x) '' (K₂ : Set V3)) ∩ Metric.ball 0 r := by
    intro K₁ K₂ h'
    ext q
    rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_image, Set.mem_image]
    constructor
    · rintro ⟨⟨p, hpK, rfl⟩, hqb⟩
      have hpx : dist p x < r := by
        rw [dist_eq_norm]
        simpa using hqb
      have hp2 : p ∈ (K₂ : Set V3) ∩ Metric.ball x r := by
        rw [← h']
        exact ⟨hpK, hpx⟩
      exact ⟨⟨p, hp2.1, rfl⟩, hqb⟩
    · rintro ⟨⟨p, hpK, rfl⟩, hqb⟩
      have hpx : dist p x < r := by
        rw [dist_eq_norm]
        simpa using hqb
      have hp2 : p ∈ (K₁ : Set V3) ∩ Metric.ball x r := by
        rw [h']
        exact ⟨hpK, hpx⟩
      exact ⟨⟨p, hp2.1, rfl⟩, hqb⟩
  have hshift := key Ks Kt heq
  have hsubspace := SUBSPACES_INTER_BALL_EQ_IMP_EQ
    ((fun p : V3 => p - x) '' (Ks : Set V3)) ((fun p : V3 => p - x) '' (Kt : Set V3)) r
    ⟨Ls, hLs⟩ ⟨Lt, hLt⟩ hr hshift
  -- translate back
  ext p
  constructor
  · intro hp
    have h1 : (p - x : V3) ∈ (fun p : V3 => p - x) '' (Ks : Set V3) := ⟨p, hp, rfl⟩
    have h2 : (p - x : V3) ∈ (fun p : V3 => p - x) '' (Kt : Set V3) := by
      rw [← hsubspace]
      exact h1
    obtain ⟨p', hp'Kt, hp'q⟩ := h2
    have hp'p : p' = p := by simpa using hp'q
    rw [hp'p] at hp'Kt
    exact hp'Kt
  · intro hp
    have h1 : (p - x : V3) ∈ (fun p : V3 => p - x) '' (Kt : Set V3) := ⟨p, hp, rfl⟩
    have h2 : (p - x : V3) ∈ (fun p : V3 => p - x) '' (Ks : Set V3) := by
      rw [hsubspace]
      exact h1
    obtain ⟨p', hp'Ks, hp'q⟩ := h2
    have hp'p : p' = p := by simpa using hp'q
    rw [hp'p] at hp'Ks
    exact hp'Ks

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

/-- `affDim` of an affine hull (`p6_affDim_affineSpan` pattern). -/
private theorem p7_affDim_affineSpan (s : Set V3) :
    affDim ((affineSpan ℝ s : Set V3)) = affDim s := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs, affDim_empty, AffineSubspace.span_empty, AffineSubspace.bot_coe, affDim_empty]
  · have hne : s ≠ ∅ := Set.nonempty_iff_ne_empty.mp hs
    have hne2 : (affineSpan ℝ s : Set V3) ≠ ∅ := by
      intro h0
      exact hne (Set.subset_empty_iff.1 (h0 ▸ subset_affineSpan ℝ s))
    simp only [affDim, if_neg hne, if_neg hne2]
    rw [← AffineSubspace.direction_eq_vectorSpan (affineSpan ℝ s), direction_affineSpan]

/-- The bisector family over a set is itself an affine set (the carrier of
its affine hull, by `AFFINE_HULL_INTERS_BIS`). -/
private theorem p7_inters_bis_affine (p : V3) (s : Set V3) :
    ∃ K : AffineSubspace ℝ V3, (K : Set V3) = ⋂₀ {bis p v | v ∈ s} :=
  ⟨affineSpan ℝ (⋂₀ {bis p v | v ∈ s}), AFFINE_HULL_INTERS_BIS p s⟩

/-- HL `YIFVQDV_lemma_aff_dim` (Rogers.hl:8656). -/
theorem YIFVQDV_lemma_aff_dim (V : Set V3) (vl : List V3) (hV : Packing V)
    (hsub : setOfList vl ⊆ V) (hind : ¬ affineDependent (setOfList vl))
    (hl2 : hl vl < Real.sqrt 2) :
    affDim (voronoiList V vl) =
      affDim (⋂₀ {bis (hdV vl) v | v ∈ setOfList vl}) := by
  classical
  rcases eq_or_ne (setOfList vl) (∅ : Set V3) with hE | hne
  · -- the empty list: both families are empty, both sides are `univ`
    cases vl with
    | nil =>
      have h1 : voronoiList V ([] : List V3) = (univ : Set V3) := by
        rw [voronoiList]
        ext q
        simp [voronoiSet, setOfList]
      have h2 : (⋂₀ {bis (hdV ([] : List V3)) v | v ∈ setOfList ([] : List V3)}) =
          (univ : Set V3) := by
        ext q
        simp [setOfList]
      rw [h1, h2]
    | cons a t =>
      have hmem : (a : V3) ∈ setOfList (a :: t) := by simp [setOfList]
      rw [hE] at hmem
      simp at hmem
  · -- the gap ball around the circumcenter
    have hgap : ∀ u ∈ setOfList vl, ∀ v ∈ V \ setOfList vl,
        dist v (circumcenter (setOfList vl)) > dist u (circumcenter (setOfList vl)) := by
      intro u hu v hv
      exact XYOFCGX V (setOfList vl) (circumcenter (setOfList vl)) hV hsub hind rfl hl2 u v
        hu hv
    obtain ⟨r, hrpos, hrgap⟩ := NEIGHBORHOOD_lemma V (setOfList vl)
      (circumcenter (setOfList vl)) hV hsub hgap
    have hdm : hdV vl ∈ setOfList vl := by
      cases vl with
      | nil =>
        have hE0 : setOfList ([] : List V3) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro q hq
          exact absurd (Set.mem_setOf.mp hq) List.not_mem_nil
        exact absurd hE0 hne
      | cons a t => simp [setOfList, hdV]
    have hlen1 : 1 ≤ vl.length := by
      cases vl with
      | nil =>
        exact absurd (Set.eq_empty_of_forall_notMem fun q hq => by
          simp [setOfList] at hq) hne
      | cons a t => simp
    have hpH : circumcenter (setOfList vl) ∈
        (affineSpan ℝ (voronoiList V vl) : Set V3) :=
      subset_affineSpan ℝ _ (CIRCUMCENTER_IN_VORONOI_SET V (setOfList vl) hV hsub hind hl2)
    have heq : (affineSpan ℝ (voronoiList V vl) : Set V3) ∩ Metric.ball
        (circumcenter (setOfList vl)) r =
        (⋂₀ {bis (hdV vl) v | v ∈ setOfList vl}) ∩ Metric.ball
        (circumcenter (setOfList vl)) r := by
      ext q
      rw [Set.mem_inter_iff, Set.mem_inter_iff]
      constructor
      · rintro ⟨hqa, hqb⟩
        exact ⟨AFFINE_HULL_VORONOI_LIST_SUBSET_INTERS_BIS V vl hsub hqa, hqb⟩
      · rintro ⟨hqt, hqb⟩
        have hqvc : q ∈ voronoiClosed V (hdV vl) := by
          intro w hw
          by_cases hwS : w ∈ setOfList vl
          · have h2 : dist q (hdV vl) = dist q w :=
              Set.mem_sInter.mp hqt _ (by simpa using ⟨w, hwS, rfl⟩)
            show dist q (hdV vl) ≤ dist q w
            linarith
          · have hg := hrgap q hqb (hdV vl) hdm w ⟨hw, hwS⟩
            rw [dist_comm w q, dist_comm (hdV vl) q] at hg
            exact le_of_lt hg
        have hqvl : q ∈ voronoiList V vl := by
          rw [VORONOI_LIST_EQ_INTERS_BIS V vl hsub hlen1]
          exact ⟨hqvc, hqt⟩
        exact ⟨subset_affineSpan ℝ _ hqvl, hqb⟩
    have hspaneq := AFFINES_INTER_BALL_EQ_IMP_EQ
      (affineSpan ℝ (voronoiList V vl) : Set V3)
      (⋂₀ {bis (hdV vl) v | v ∈ setOfList vl})
      (circumcenter (setOfList vl)) r
      ⟨affineSpan ℝ (voronoiList V vl), rfl⟩
      (p7_inters_bis_affine (hdV vl) (setOfList vl)) hrpos heq hpH
    calc affDim (voronoiList V vl)
        = affDim ((affineSpan ℝ (voronoiList V vl) : Set V3)) :=
          (p7_affDim_affineSpan (voronoiList V vl)).symm
      _ = affDim (⋂₀ {bis (hdV vl) v | v ∈ setOfList vl}) := by rw [hspaneq]

/-! ## YIFVQDV_1 (permutation invariance) .. WQPRRDY (capstone) -/

/-! ### YIFVQDV_1 support kit (bisector dimensions and prefix dimensions) -/

/-- Four pairwise-distinct points give a 4-element set. -/
private theorem p7_card4_of_distinct {a b c d : V3} (h1 : a ≠ b) (h2 : a ≠ c)
    (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) :
    Nat.card ({a, b, c, d} : Set V3) = 4 := by
  have e1 : ({a, b, c, d} : Set V3).ncard = ({b, c, d} : Set V3).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp; tauto)
  have e2 : ({b, c, d} : Set V3).ncard = ({c, d} : Set V3).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp; tauto)
  have e3 : ({c, d} : Set V3).ncard = ({d} : Set V3).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp; tauto)
  have e4 : ({d} : Set V3).ncard = 1 := Set.ncard_singleton d
  have he : Nat.card ({a, b, c, d} : Set V3) = ({a, b, c, d} : Set V3).ncard := rfl
  omega

/-- Three pairwise-distinct points give a 3-element set. -/
private theorem p7_card3_of_distinct {a b c : V3} (h1 : a ≠ b) (h2 : a ≠ c)
    (h3 : b ≠ c) : Nat.card ({a, b, c} : Set V3) = 3 := by
  have e1 : ({a, b, c} : Set V3).ncard = ({b, c} : Set V3).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp; tauto)
  have e2 : ({b, c} : Set V3).ncard = ({c} : Set V3).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp; tauto)
  have e3 : ({c} : Set V3).ncard = 1 := Set.ncard_singleton c
  have he : Nat.card ({a, b, c} : Set V3) = ({a, b, c} : Set V3).ncard := rfl
  omega

/-- Two distinct points give a 2-element set. -/
private theorem p7_card2_of_distinct {a b : V3} (h : a ≠ b) :
    Nat.card ({a, b} : Set V3) = 2 := by
  have e1 : ({a, b} : Set V3).ncard = ({b} : Set V3).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp [h])
  have e2 : ({b} : Set V3).ncard = 1 := Set.ncard_singleton b
  have he : Nat.card ({a, b} : Set V3) = ({a, b} : Set V3).ncard := rfl
  omega

/-- Affine dependence passes to supersets (contrapositive form used for
subsets of an affinely independent point set). -/
private theorem p7_not_affineDependent_subset {s t : Set V3} (hsub : s ⊆ t)
    (ht : ¬ affineDependent t) : ¬ affineDependent s := by
  intro hs
  exact ht (fun hti => hs (AffineIndependent.mono hti hsub))

/-- `voronoiNondg` only depends on the point set and the list length. -/
private theorem p7_voronoiNondg_congr {V : Set V3} {a b : List V3}
    (hset : setOfList a = setOfList b) (hlen : a.length = b.length) :
    voronoiNondg V a ↔ voronoiNondg V b := by
  simp only [voronoiNondg, voronoiList, hset, hlen]

/-- A list's point set is contained in the point set of any extension. -/
private theorem p7_setOfList_append {l1 l2 : List V3} :
    setOfList l1 ⊆ setOfList (l1 ++ l2) := by
  intro t ht
  exact List.mem_append.mpr (Or.inl ht)

/-- Initial sublists of a four-point list. -/
private theorem p7_initSublist_four {a b c d : V3} {zl : List V3}
    (hini : initialSublist zl [a, b, c, d]) (hz : 0 < zl.length) :
    zl = [a, b, c, d] ∨ zl = [a, b, c] ∨ zl = [a, b] ∨ zl = [a] := by
  obtain ⟨yl, hyl0⟩ := hini
  have h4 : ([a, b, c, d] : List V3).length = 4 := by simp
  have hlen0 : ([a, b, c, d] : List V3).length = zl.length + yl.length := by
    rw [hyl0, List.length_append]
  cases zl with
  | nil => exact absurd hz (by simp)
  | cons x t =>
    simp only [List.cons_append, List.nil_append] at hyl0
    cases t with
    | nil =>
      injection hyl0 with e1 _
      exact Or.inr (Or.inr (Or.inr (by rw [e1])))
    | cons y t2 =>
      cases t2 with
      | nil =>
        injection hyl0 with e1 e2
        injection e2 with e3 _
        exact Or.inr (Or.inr (Or.inl (by rw [e1, e3])))
      | cons z t3 =>
        cases t3 with
        | nil =>
          injection hyl0 with e1 e2
          injection e2 with e3 e4
          injection e4 with e5 _
          exact Or.inr (Or.inl (by rw [e1, e3, e5]))
        | cons w t4 =>
          cases t4 with
          | nil =>
            injection hyl0 with e1 e2
            injection e2 with e3 e4
            injection e4 with e5 e6
            injection e6 with e7 _
            exact Or.inl (by rw [e1, e3, e5, e7])
          | cons v t5 =>
            exfalso
            have h5 : 5 ≤ (x :: y :: z :: w :: v :: t5).length := by simp
            omega

/-- Initial sublists of a three-point list. -/
private theorem p7_initSublist_three {a b c : V3} {zl : List V3}
    (hini : initialSublist zl [a, b, c]) (hz : 0 < zl.length) :
    zl = [a, b, c] ∨ zl = [a, b] ∨ zl = [a] := by
  obtain ⟨yl, hyl0⟩ := hini
  have hlen0 : ([a, b, c] : List V3).length = zl.length + yl.length := by
    rw [hyl0, List.length_append]
  simp at hlen0
  cases zl with
  | nil => exact absurd hz (by simp)
  | cons x t =>
    simp only [List.cons_append, List.nil_append] at hyl0
    cases t with
    | nil =>
      injection hyl0 with e1 _
      exact Or.inr (Or.inr (by rw [e1]))
    | cons y t2 =>
      cases t2 with
      | nil =>
        injection hyl0 with e1 e2
        injection e2 with e3 _
        exact Or.inr (Or.inl (by rw [e1, e3]))
      | cons z t3 =>
        cases t3 with
        | nil =>
          injection hyl0 with e1 e2
          injection e2 with e3 e4
          injection e4 with e5 _
          exact Or.inl (by rw [e1, e3, e5])
        | cons w t4 =>
          exfalso
          have h5 : 4 ≤ (x :: y :: z :: w :: t4).length := by simp
          omega

/-- Initial sublists of a two-point list. -/
private theorem p7_initSublist_two {a b : V3} {zl : List V3}
    (hini : initialSublist zl [a, b]) (hz : 0 < zl.length) :
    zl = [a, b] ∨ zl = [a] := by
  obtain ⟨yl, hyl0⟩ := hini
  have hlen0 : ([a, b] : List V3).length = zl.length + yl.length := by
    rw [hyl0, List.length_append]
  simp at hlen0
  cases zl with
  | nil => exact absurd hz (by simp)
  | cons x t =>
    simp only [List.cons_append, List.nil_append] at hyl0
    cases t with
    | nil =>
      injection hyl0 with e1 _
      exact Or.inr (by rw [e1])
    | cons y t2 =>
      cases t2 with
      | nil =>
        injection hyl0 with e1 e2
        injection e2 with e3 _
        exact Or.inl (by rw [e1, e3])
      | cons z t3 =>
        exfalso
        have h4 : 3 ≤ (x :: y :: z :: t3).length := by simp
        omega

/-- Explicit shape of a length-one list. -/
private theorem p7_list1_eq (ul : List V3) (h : ul.length = 1) :
    ∃ u0, ul = [u0] := by
  cases ul with
  | nil => simp at h
  | cons u0 t =>
    cases t with
    | nil => exact ⟨u0, rfl⟩
    | cons u1 t => simp at h

/-- Explicit shape of a length-two list. -/
private theorem p7_list2_eq (ul : List V3) (h : ul.length = 2) :
    ∃ u0 u1, ul = [u0, u1] := by
  cases ul with
  | nil => simp at h
  | cons u0 t =>
    cases t with
    | nil => simp at h
    | cons u1 t =>
      cases t with
      | nil => exact ⟨u0, u1, rfl⟩
      | cons u2 t => simp at h

/-- Explicit shape of a length-three list. -/
private theorem p7_list3_eq (ul : List V3) (h : ul.length = 3) :
    ∃ u0 u1 u2, ul = [u0, u1, u2] := by
  cases ul with
  | nil => simp at h
  | cons u0 t =>
    cases t with
    | nil => simp at h
    | cons u1 t =>
      cases t with
      | nil => simp at h
      | cons u2 t =>
        cases t with
        | nil => exact ⟨u0, u1, u2, rfl⟩
        | cons u3 t => simp at h

/-- Explicit shape of a length-four list. -/
private theorem p7_list4_eq (ul : List V3) (h : ul.length = 4) :
    ∃ u0 u1 u2 u3, ul = [u0, u1, u2, u3] := by
  cases ul with
  | nil => simp at h
  | cons u0 t =>
    cases t with
    | nil => simp at h
    | cons u1 t =>
      cases t with
      | nil => simp at h
      | cons u2 t =>
        cases t with
        | nil => simp at h
        | cons u3 t =>
          cases t with
          | nil => exact ⟨u0, u1, u2, u3, rfl⟩
          | cons u4 t => simp at h

/-- The inner-product functional on `V3` (the `p15_dotR` pattern). -/
private noncomputable def p7_dotR (a : V3) : V3 →ₗ[ℝ] ℝ where
  toFun x := inner ℝ a x
  map_add' x y := inner_add_right a x y
  map_smul' r x := real_inner_smul_right a x r

/-- The coe family on a set has the set as its range. -/
private theorem p7_range_coe {S : Set V3} :
    Set.range (fun x : ↥S => (x : V3)) = S := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro hy; exact ⟨⟨y, hy⟩, rfl⟩

/-- For `a ≠ 0` the kernel of the inner-product functional has finrank `2`. -/
private theorem p7_finrank_ker_dot {a : V3} (ha : a ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (p7_dotR a)) = 2 := by
  have hDpos : (0:ℝ) < p7_dotR a a := by
    show 0 < inner ℝ a a
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr ha) 2
  have hrange_ne : LinearMap.range (p7_dotR a) ≠ ⊥ := by
    intro hbot
    have hx : p7_dotR a a ∈ LinearMap.range (p7_dotR a) := ⟨a, rfl⟩
    rw [hbot] at hx
    exact hDpos.ne' (Submodule.mem_bot (R := ℝ) |>.mp hx)
  have hnk := LinearMap.finrank_range_add_finrank_ker (p7_dotR a)
  have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
  rw [h3] at hnk
  have hfrle : Module.finrank ℝ (LinearMap.range (p7_dotR a)) ≤ 1 := by
    refine le_trans (Submodule.finrank_mono (le_top : LinearMap.range (p7_dotR a) ≤ _)) ?_
    simp
  have hfrne : Module.finrank ℝ (LinearMap.range (p7_dotR a)) ≠ 0 := by
    intro h
    apply hrange_ne
    exact (Submodule.finrank_eq_zero).mp h
  omega

/-- A bisector is the carrier of the affine subspace through the midpoint
with direction the kernel of the inner-product functional. -/
private theorem p7_bis_mk' (a b : V3) :
    (AffineSubspace.mk' ((2⁻¹ : ℝ) • (a + b))
        (LinearMap.ker (p7_dotR (b - a))) : Set V3) = bis a b := by
  ext x
  rw [SetLike.mem_coe, AffineSubspace.mem_mk', LinearMap.mem_ker]
  show inner ℝ (b - a) (x - (2⁻¹ : ℝ) • (a + b)) = 0 ↔ dist x a = dist x b
  have hsqinj : ‖x - a‖ = ‖x - b‖ ↔ ‖x - a‖ ^ 2 = ‖x - b‖ ^ 2 := by
    constructor
    · intro hh; rw [hh]
    · intro hh
      have hA : 0 ≤ ‖x - a‖ := norm_nonneg _
      have hB : 0 ≤ ‖x - b‖ := norm_nonneg _
      have hmul : (‖x - a‖ + ‖x - b‖) * (‖x - a‖ - ‖x - b‖) = 0 := by
        have key : ‖x - a‖ * ‖x - a‖ - ‖x - b‖ * ‖x - b‖ = 0 := by
          rw [← pow_two, ← pow_two, hh, sub_self]
        nlinarith [key]
      rcases mul_eq_zero.1 hmul with h | h
      · linarith
      · linarith
  rw [inner_sub_right, real_inner_smul_right, dist_eq_norm, dist_eq_norm, hsqinj,
    norm_sub_sq_real x a, norm_sub_sq_real x b]
  have hL : inner ℝ (b - a) x = inner ℝ b x - inner ℝ a x := inner_sub_left b a x
  have hE : inner ℝ (b - a) (a + b) = ‖b‖ ^ 2 - ‖a‖ ^ 2 := by
    rw [inner_add_right, inner_sub_left, inner_sub_left, real_inner_comm b a,
      real_inner_self_eq_norm_sq a, real_inner_self_eq_norm_sq b]
    ring
  rw [hL, hE]
  constructor <;> intro h
  · linarith [real_inner_comm x a, real_inner_comm x b]
  · linarith [real_inner_comm x a, real_inner_comm x b]

/-- The vector span of a three-point set is the span of the two differences
off the first point. -/
private theorem p7_vectorSpan_triple (x y z : V3) :
    vectorSpan ℝ ({x, y, z} : Set V3) = Submodule.span ℝ ({y - x, z - x} : Set V3) := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ (show x ∈ ({x, y, z} : Set V3) from by simp)]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro q ⟨p, hp, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · simp
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · rw [Submodule.span_le]
    rintro q (rfl | rfl)
    · exact Submodule.subset_span ⟨y, by simp, rfl⟩
    · exact Submodule.subset_span ⟨z, by simp, rfl⟩

/-- `affDim` of a nondegenerate bisector is `2`. -/
private theorem p7_affDim_bis_pair {u0 u1 : V3} (hne : u0 ≠ u1) :
    affDim (bis u0 u1) = 2 := by
  have hsub : u1 - u0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [BIS_EQ_HYPERPLANE]
  have heq : {x : V3 | 2 * ((u1 - u0) ⬝ᵥ x) = u1 ⬝ᵥ u1 - u0 ⬝ᵥ u0} =
      {x : V3 | (u1 - u0) ⬝ᵥ x = (u1 ⬝ᵥ u1 - u0 ⬝ᵥ u0) / 2} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [heq]
  exact affDim_hyperplane hsub _

/-- The bisector family over a pair collapses to the one nontrivial
bisector (`bis u u = univ`). -/
private theorem p7_inters_bis_pair (u v : V3) :
    ⋂₀ {bis u w | w ∈ ({u, v} : Set V3)} = bis u v := by
  ext q
  rw [Set.mem_sInter]
  constructor
  · intro h
    exact h (bis u v) ⟨v, by simp, rfl⟩
  · intro h T hT
    rw [Set.mem_setOf_eq] at hT
    obtain ⟨w, hw, rfl⟩ := hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hwu | hwv
    · rw [hwu]
      show dist q u = dist q u
      rfl
    · rw [hwv]
      exact h

/-- The bisector family over a triple collapses to the pair of nontrivial
bisectors. -/
private theorem p7_inters_bis_triple (u v w : V3) :
    ⋂₀ {bis u z | z ∈ ({u, v, w} : Set V3)} = bis u v ∩ bis u w := by
  ext q
  rw [Set.mem_sInter, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨h (bis u v) (by simpa using ⟨v, by simp, rfl⟩),
      h (bis u w) (by simpa using ⟨w, by simp, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ T hT
    rw [Set.mem_setOf_eq] at hT
    obtain ⟨z, hz, rfl⟩ := hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hzu | hzv | hzw
    · rw [hzu]
      show dist q u = dist q u
      rfl
    · rw [hzv]
      exact h1
    · rw [hzw]
      exact h2

/-- Three pairwise distinct, non-collinear points: the two bisectors `bis u v`
and `bis u w` meet in a line, `affDim = 1`. -/
private theorem p7_affDim_bis2 {u v w : V3} (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) (hnc : Module.finrank ℝ (vectorSpan ℝ ({u, v, w} : Set V3)) = 2) :
    affDim (bis u v ∩ bis u w) = 1 := by
  classical
  have hcard3 : Nat.card ({u, v, w} : Set V3) = 3 :=
    p7_card3_of_distinct huv huw hvw
  have hind3 : ¬ affineDependent ({u, v, w} : Set V3) := by
    rw [affineDependent, not_not]
    have hfin : ({u, v, w} : Set V3).Finite :=
      Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton w))
    haveI : Fintype ↥({u, v, w} : Set V3) := hfin.fintype
    have hcf : Fintype.card ↥({u, v, w} : Set V3) = 1 + 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard3
    rw [affineIndependent_iff_not_finrank_vectorSpan_le ℝ
      (fun x : ↥({u, v, w} : Set V3) => (x : V3)) hcf, p7_range_coe, hnc]
    norm_num
  -- nonempty: the triple circumcenter is equidistant from all three points
  have d0 := OAPVION2_concl ({u, v, w} : Set V3) hind3 u (by simp)
  have d1 := OAPVION2_concl ({u, v, w} : Set V3) hind3 v (by simp)
  have d2 := OAPVION2_concl ({u, v, w} : Set V3) hind3 w (by simp)
  have hc0 : circumcenter ({u, v, w} : Set V3) ∈ bis u v ∩ bis u w := by
    constructor
    · show dist (circumcenter ({u, v, w} : Set V3)) u =
        dist (circumcenter ({u, v, w} : Set V3)) v
      linarith
    · show dist (circumcenter ({u, v, w} : Set V3)) u =
        dist (circumcenter ({u, v, w} : Set V3)) w
      linarith
  have hne2 : (bis u v ∩ bis u w : Set V3).Nonempty := ⟨_, hc0⟩
  have hK1 : (AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + v))
      (LinearMap.ker (p7_dotR (v - u))) : Set V3) = bis u v := p7_bis_mk' u v
  have hK2 : (AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + w))
      (LinearMap.ker (p7_dotR (w - u))) : Set V3) = bis u w := p7_bis_mk' u w
  have hdir1 : (AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + v))
      (LinearMap.ker (p7_dotR (v - u)))).direction =
      LinearMap.ker (p7_dotR (v - u)) := AffineSubspace.direction_mk' _ _
  have hdir2 : (AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + w))
      (LinearMap.ker (p7_dotR (w - u)))).direction =
      LinearMap.ker (p7_dotR (w - u)) := AffineSubspace.direction_mk' _ _
  have hc0mem : circumcenter ({u, v, w} : Set V3) ∈
      ↑(AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + v)) (LinearMap.ker (p7_dotR (v - u))) ⊓
        AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + w)) (LinearMap.ker (p7_dotR (w - u)))) := by
    rw [AffineSubspace.mem_inf_iff]
    refine ⟨?_, ?_⟩
    · have h' : circumcenter ({u, v, w} : Set V3) ∈ bis u v := hc0.1
      rwa [← hK1] at h'
    · have h' : circumcenter ({u, v, w} : Set V3) ∈ bis u w := hc0.2
      rwa [← hK2] at h'
  have hcarrier : (bis u v ∩ bis u w : Set V3) =
      ↑(AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + v)) (LinearMap.ker (p7_dotR (v - u))) ⊓
        AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + w)) (LinearMap.ker (p7_dotR (w - u)))) := by
    rw [← hK1, ← hK2, ← AffineSubspace.coe_inf]
    rfl
  have hdirEq : (AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + v))
      (LinearMap.ker (p7_dotR (v - u))) ⊓
      AffineSubspace.mk' ((2⁻¹ : ℝ) • (u + w))
      (LinearMap.ker (p7_dotR (w - u)))).direction =
      LinearMap.ker (p7_dotR (v - u)) ⊓ LinearMap.ker (p7_dotR (w - u)) := by
    rw [AffineSubspace.direction_inf_of_mem_inf hc0mem, hdir1, hdir2]
  rw [affDim, if_neg (Set.nonempty_iff_ne_empty.mp hne2), hcarrier,
    ← AffineSubspace.direction_eq_vectorSpan, hdirEq]
  have h2K : Module.finrank ℝ (LinearMap.ker (p7_dotR (v - u))) = 2 :=
    p7_finrank_ker_dot (a := v - u) (sub_ne_zero.mpr (Ne.symm huv))
  have h2K' : Module.finrank ℝ (LinearMap.ker (p7_dotR (w - u))) = 2 :=
    p7_finrank_ker_dot (a := w - u) (sub_ne_zero.mpr (Ne.symm huw))
  have hspanspan : Submodule.span ℝ ({v - u, w - u} : Set V3) =
      vectorSpan ℝ ({u, v, w} : Set V3) := (p7_vectorSpan_triple u v w).symm
  -- upper bound: the kernel intersection sits in the orthogonal complement
  have hle : LinearMap.ker (p7_dotR (v - u)) ⊓
      LinearMap.ker (p7_dotR (w - u)) ≤
      (Submodule.span ℝ ({v - u, w - u} : Set V3))ᗮ := by
    intro q hq
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [Submodule.mem_span_pair] at hy
    obtain ⟨a, b, hb⟩ := hy
    have hq1 : inner ℝ (v - u) q = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hq).1
    have hq2 : inner ℝ (w - u) q = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hq).2
    rw [← hb, inner_add_left, real_inner_smul_left, real_inner_smul_left, hq1, hq2]
    ring
  have hleFr : Module.finrank ℝ ↥(LinearMap.ker (p7_dotR (v - u)) ⊓
      LinearMap.ker (p7_dotR (w - u))) ≤
      Module.finrank ℝ ↥((Submodule.span ℝ ({v - u, w - u} : Set V3))ᗮ) :=
    Submodule.finrank_mono hle
  have horthrank : Module.finrank ℝ
      ((Submodule.span ℝ ({v - u, w - u} : Set V3))ᗮ) = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal
      (Submodule.span ℝ ({v - u, w - u} : Set V3))
    have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    rw [hspanspan, hnc] at h
    rw [hspanspan]
    omega
  -- lower bound: submodularity of finrank
  have hsubmod := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (p7_dotR (v - u))) (LinearMap.ker (p7_dotR (w - u)))
  have htop : Module.finrank ℝ ↥(LinearMap.ker (p7_dotR (v - u)) ⊔
      LinearMap.ker (p7_dotR (w - u))) ≤ 3 := by
    refine le_trans (Submodule.finrank_mono (le_top : _ ≤ ⊤)) ?_
    rw [finrank_top]
    exact (finrank_euclideanSpace_fin).le
  rw [h2K, h2K'] at hsubmod
  rw [horthrank] at hleFr
  omega

/-- A three-element subset of an affinely independent four-point set is
affinely independent. -/
private theorem p7_affInd_three_of_affInd4 {x0 x1 x2 x3 : V3}
    (hind : ¬ affineDependent ({x0, x1, x2, x3} : Set V3)) :
    ¬ affineDependent (setOfList [x0, x1, x2]) := by
  rw [show setOfList [x0, x1, x2] = ({x0, x1, x2} : Set V3) from by
    ext t; simp [setOfList]]
  exact p7_not_affineDependent_subset (by intro t ht; simp at ht ⊢; tauto) hind

/-- A non-collinear affinely independent triple spans a two-dimensional
vector space. -/
private theorem p7_finrank_vectorSpan_three {x0 x1 x2 : V3}
    (hd : x0 ≠ x1 ∧ x0 ≠ x2 ∧ x1 ≠ x2)
    (hind : ¬ affineDependent ({x0, x1, x2} : Set V3)) :
    Module.finrank ℝ (vectorSpan ℝ ({x0, x1, x2} : Set V3)) = 2 := by
  have hcard := p7_card3_of_distinct hd.1 hd.2.1 hd.2.2
  have hfin : ({x0, x1, x2} : Set V3).Finite :=
    Set.Finite.insert _ (Set.Finite.insert _ (Set.finite_singleton x2))
  haveI : Fintype ↥({x0, x1, x2} : Set V3) := hfin.fintype
  have hcf : Fintype.card ↥({x0, x1, x2} : Set V3) = 1 + 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have haff : AffineIndependent ℝ (fun x : ↥({x0, x1, x2} : Set V3) => (x : V3)) :=
    not_not.mp hind
  have hfr := (affineIndependent_iff_finrank_vectorSpan_eq ℝ
    (fun x : ↥({x0, x1, x2} : Set V3) => (x : V3)) hcf).mp haff
  rwa [p7_range_coe] at hfr

/-- `affDim (voronoiList V [a, b]) = 2` for a distinct pair below the
`sqrt 2` margin. -/
private theorem p7_affDim_voronoiList_pair (V : Set V3) (a b : V3)
    (hp : Packing V) (ha : a ∈ V) (hb : b ∈ V) (hne : a ≠ b)
    (hhl : hl [a, b] < Real.sqrt 2) :
    affDim (voronoiList V [a, b]) = 2 := by
  have hsub : setOfList [a, b] ⊆ V := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb
    exact absurd hx (by simp)
  have hpair : setOfList [a, b] = ({a, b} : Set V3) := by
    ext x; simp [setOfList]
  have hind : ¬ affineDependent (setOfList [a, b]) := by
    rw [affineDependent, not_not, hpair]
    have hfin : ({a, b} : Set V3).Finite := Set.Finite.insert _ (Set.finite_singleton b)
    haveI : Fintype ↥({a, b} : Set V3) := hfin.fintype
    have hcard : Fintype.card ↥({a, b} : Set V3) = 0 + 2 := by
      have hn : Nat.card ({a, b} : Set V3) = 2 := p7_card2_of_distinct hne
      rw [Nat.card_eq_fintype_card] at hn
      omega
    rw [affineIndependent_iff_not_finrank_vectorSpan_le ℝ
      (fun x : ↥({a, b} : Set V3) => (x : V3)) hcard, p7_range_coe,
      vectorSpan_pair, finrank_span_singleton
        (show (a -ᵥ b : V3) ≠ 0 from sub_ne_zero.mpr hne)]
    norm_num
  have hdim := YIFVQDV_lemma_aff_dim V [a, b] hp hsub hind hhl
  rw [hdim]
  have hhd : hdV [a, b] = a := rfl
  have hinter : (⋂₀ {bis (hdV [a, b]) v | v ∈ setOfList [a, b]}) = bis a b := by
    rw [hhd, hpair]
    exact p7_inters_bis_pair a b
  rw [hinter]
  exact p7_affDim_bis_pair hne

/-- The `k = 3` slice of `YIFVQDV_1`: `barV V 3` of a four-point list depends
only on its point set (full prefix by set congruence, singletons by
`AFF_DIM_VORONOI_CLOSED`, pairs and triples by `YIFVQDV_lemma_aff_dim` plus
the bisector dimension arithmetic). -/
private theorem p7_barV3_of_set (V : Set V3) (w0 w1 w2 w3 : V3) (hp : Packing V)
    (hsub : setOfList [w0, w1, w2, w3] ⊆ V)
    (hd : w0 ≠ w1 ∧ w0 ≠ w2 ∧ w0 ≠ w3 ∧ w1 ≠ w2 ∧ w1 ≠ w3 ∧ w2 ≠ w3)
    (hind : ¬ affineDependent (setOfList [w0, w1, w2, w3]))
    (hhl : hl [w0, w1, w2, w3] < Real.sqrt 2)
    (hfull : voronoiNondg V [w0, w1, w2, w3])
    (x0 x1 x2 x3 : V3) (hset : setOfList [x0, x1, x2, x3] = setOfList [w0, w1, w2, w3])
    (hdistx : x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x3 ∧ x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3) :
    barV V 3 [x0, x1, x2, x3] := by
  classical
  rw [hl] at hhl
  have hsab : setOfList [w0, w1, w2, w3] = ({w0, w1, w2, w3} : Set V3) := by
    ext t; simp [setOfList]
  have hcardw : Nat.card ({w0, w1, w2, w3} : Set V3) = 4 :=
    p7_card4_of_distinct hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2
  have hs4 : ({x0, x1, x2, x3} : Set V3) = setOfList [x0, x1, x2, x3] := by
    ext t; simp [setOfList]
  have hcardx : Nat.card ({x0, x1, x2, x3} : Set V3) = 4 := by
    rw [hs4, hset, hsab, hcardw]
  have hindx : ¬ affineDependent ({x0, x1, x2, x3} : Set V3) := by
    rw [hs4, hset]
    exact hind
  have hsubmem : ∀ t ∈ ({x0, x1, x2, x3} : Set V3), t ∈ setOfList [w0, w1, w2, w3] := by
    intro t ht
    rw [hs4] at ht
    rw [hset] at ht
    exact ht
  refine ⟨rfl, fun vl hv => ?_⟩
  obtain ⟨hini, hpos⟩ := hv
  rcases p7_initSublist_four hini hpos with heq | heq | heq | heq
  · -- the full prefix: the same point set as the original list
    rw [heq]
    exact (p7_voronoiNondg_congr hset rfl).2 hfull
  · -- the triple prefix
    rw [heq]
    refine ⟨by norm_num, ?_, ?_⟩
    · intro t ht
      have ht' : t ∈ setOfList [x0, x1, x2, x3] := p7_setOfList_append ht
      rw [hset] at ht'
      exact hsub ht'
    · have hs3 : setOfList [x0, x1, x2] = ({x0, x1, x2} : Set V3) := by
        ext t; simp [setOfList]
      have hind3 : ¬ affineDependent (setOfList [x0, x1, x2]) :=
        p7_affInd_three_of_affInd4 hindx
      have hfr3 : Module.finrank ℝ (vectorSpan ℝ ({x0, x1, x2} : Set V3)) = 2 :=
        p7_finrank_vectorSpan_three
          ⟨hdistx.1, hdistx.2.1, hdistx.2.2.2.1⟩ (by rwa [← hs3])
      have hsub3 : setOfList [x0, x1, x2] ⊆ V := fun t ht => by
        have ht' : t ∈ setOfList [x0, x1, x2, x3] := p7_setOfList_append ht
        rw [hset] at ht'
        exact hsub ht'
      have hhl3 : hl [x0, x1, x2] < Real.sqrt 2 := by
        rw [hl, hs3]
        have hh : ∀ t ∈ ({x0, x1, x2} : Set V3), t ∈ setOfList [w0, w1, w2, w3] := by
          intro t ht
          rw [← hs3] at ht
          have ht' : t ∈ setOfList [x0, x1, x2, x3] := p7_setOfList_append ht
          rw [hset] at ht'
          exact ht'
        have hle := RADV_MONO (setOfList [w0, w1, w2, w3]) ({x0, x1, x2} : Set V3)
          hind hh (Set.nonempty_iff_ne_empty.mp ⟨x0, by simp⟩)
        linarith
      have hdim3 := YIFVQDV_lemma_aff_dim V [x0, x1, x2] hp hsub3 hind3 hhl3
      show affDim (voronoiList V [x0, x1, x2]) + ((3 : ℕ) : ℤ) = 4
      rw [hdim3, hs3]
      show affDim (⋂₀ {bis x0 v | v ∈ ({x0, x1, x2} : Set V3)}) + ((3 : ℕ) : ℤ) = 4
      rw [p7_inters_bis_triple,
        p7_affDim_bis2 hdistx.1 hdistx.2.1 hdistx.2.2.2.1 hfr3]
      norm_num
  · -- the pair prefix
    rw [heq]
    refine ⟨by norm_num, ?_, ?_⟩
    · intro t ht
      have ht' : t ∈ setOfList [x0, x1, x2, x3] := p7_setOfList_append ht
      rw [hset] at ht'
      exact hsub ht'
    · have hs2 : setOfList [x0, x1] = ({x0, x1} : Set V3) := by
        ext t; simp [setOfList]
      have hsub2 : setOfList [x0, x1] ⊆ V := fun t ht => by
        have ht' : t ∈ setOfList [x0, x1, x2, x3] := p7_setOfList_append ht
        rw [hset] at ht'
        exact hsub ht'
      have hx0V : x0 ∈ V := hsub2 (by simp [setOfList])
      have hx1V : x1 ∈ V := hsub2 (by simp [setOfList])
      have hhl2 : hl [x0, x1] < Real.sqrt 2 := by
        rw [hl, hs2]
        have hh : ∀ t ∈ ({x0, x1} : Set V3), t ∈ setOfList [w0, w1, w2, w3] := by
          intro t ht
          rw [← hs2] at ht
          have ht' : t ∈ setOfList [x0, x1, x2, x3] := p7_setOfList_append ht
          rw [hset] at ht'
          exact ht'
        have hle := RADV_MONO (setOfList [w0, w1, w2, w3]) ({x0, x1} : Set V3)
          hind hh (Set.nonempty_iff_ne_empty.mp ⟨x0, by simp⟩)
        linarith
      have hdim2 := p7_affDim_voronoiList_pair V x0 x1 hp hx0V hx1V hdistx.1 hhl2
      show affDim (voronoiList V [x0, x1]) + ((2 : ℕ) : ℤ) = 4
      rw [hdim2]
      norm_num
  · -- the singleton prefix
    rw [heq]
    refine ⟨by norm_num, ?_, ?_⟩
    · intro t ht
      have ht' : t ∈ setOfList [x0, x1, x2, x3] := p7_setOfList_append ht
      rw [hset] at ht'
      exact hsub ht'
    · show affDim (voronoiList V [x0]) + ((1 : ℕ) : ℤ) = 4
      rw [VORONOI_LIST_SING V x0, AFF_DIM_VORONOI_CLOSED V x0 hp]
      norm_num

/-- HL `YIFVQDV_1` (Rogers.hl:8777). -/
theorem YIFVQDV_1 (V : Set V3) (ul : List V3) (k : ℕ) (p : Equiv.Perm ℕ)
    (hV : Packing V) (hb : barV V k ul) (hl2 : hl ul < Real.sqrt 2)
    (hperm : permutes p (Set.Icc 0 k)) :
    barV V k (leftActionList p ul) := by
  classical
  have hlenu : ul.length = k + 1 := hb.1
  have hk3 : k ≤ 3 := BARV_IMP_K_LE_3 V ul k hb
  have hcardu : Nat.card (setOfList ul) = k + 1 :=
    (BARV_IMP_LENGTH_EQ_CARD V ul k hV hb).2
  have hpermL : permutes p {i : ℕ | i < ul.length} := by
    intro x
    have hx := hperm x
    simp only [Set.mem_Icc, Set.mem_setOf_eq] at hx ⊢
    rw [hlenu]
    omega
  have hset : setOfList (leftActionList p ul) = setOfList ul :=
    SET_OF_LIST_LEFT_ACTION_LIST ul p hpermL
  have hsubu : setOfList ul ⊆ V := BARV_SUBSET V k ul hb
  have hindu : ¬ affineDependent (setOfList ul) := BARV_AFFINE_INDEPENDENT V ul k hV hb
  have hfullu : voronoiNondg V ul :=
    hb.2 ul ⟨INITIAL_SUBLIST_REFL ul, by rw [hlenu]; omega⟩
  have hdistu : ∀ i j : ℕ, i < ul.length → j < ul.length → i ≠ j →
      elV ul i ≠ elV ul j := fun i j hi hj hij =>
    CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT ul (by rw [hcardu, hlenu]) i j hi hj hij
  refine ⟨?_, ?_⟩
  · rw [LENGTH_LEFT_ACTION_LIST, hlenu]
  · intro vl' ⟨hinit, hpos⟩
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    · -- k = 0
      obtain ⟨u0, rfl⟩ := p7_list1_eq ul (by rw [hlenu])
      have hp0 : p 0 = 0 := by
        have h0 : (0:ℕ) ∈ Set.Icc 0 0 := Set.mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩
        have h := (hperm 0).mp h0
        simpa [Set.mem_Icc] using h
      have hsymm0 : p.symm 0 = 0 := by
        have h1 : p.symm (p 0) = 0 := Equiv.symm_apply_apply p 0
        rwa [hp0] at h1
      have hvl : leftActionList p [u0] = [u0] := by
        simp [leftActionList, hsymm0]
      have hlen1 : (leftActionList p [u0]).length = 1 := by
        rw [LENGTH_LEFT_ACTION_LIST]; rfl
      have hlenvl' : vl'.length = 1 := by
        have hle := INITIAL_SUBLIST_LENGTH_LE hinit
        rw [hlen1] at hle
        omega
      have heq : vl' = leftActionList p [u0] :=
        INITIAL_SUBLIST_UNIQUE hinit (INITIAL_SUBLIST_REFL _) hlenvl' hlen1
      rw [heq, hvl]
      exact hfullu
    · -- k = 1
      obtain ⟨u0, u1, rfl⟩ := p7_list2_eq ul (by rw [hlenu])
      have hvl2 : (leftActionList p [u0, u1]).length = 2 := by
        rw [LENGTH_LEFT_ACTION_LIST]; rfl
      obtain ⟨a, b, hvl⟩ := p7_list2_eq (leftActionList p [u0, u1]) hvl2
      rw [hvl] at hset hinit
      have hsetab : setOfList [a, b] = setOfList [u0, u1] := hset
      have hcardab : Nat.card (setOfList [a, b]) = 2 := by
        rw [hsetab,
          show setOfList [u0, u1] = ({u0, u1} : Set V3) from by ext t; simp [setOfList]]
        exact p7_card2_of_distinct (hdistu 0 1 (by simp) (by simp) (by norm_num))
      have hneab : a ≠ b := by
        intro he
        have h1 := CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT [a, b]
          (by rw [hcardab]; rfl) 0 1 (by norm_num) (by norm_num) (by norm_num)
        exact h1 he
      rcases p7_initSublist_two hinit hpos with heq | heq
      · -- full prefix
        rw [heq]
        exact (p7_voronoiNondg_congr hsetab rfl).2 hfullu
      · -- singleton
        rw [heq]
        refine ⟨by norm_num, ?_, ?_⟩
        · intro t ht
          have ht' : t = a := by simpa [setOfList] using ht
          rw [ht']
          exact hsubu (by rw [← hsetab]; simp [setOfList])
        · show affDim (voronoiList V [a]) + ((1 : ℕ) : ℤ) = 4
          rw [VORONOI_LIST_SING V a, AFF_DIM_VORONOI_CLOSED V a hV]
          norm_num
    · -- k = 2
      obtain ⟨u0, u1, u2, rfl⟩ := p7_list3_eq ul (by rw [hlenu])
      have hvl3 : (leftActionList p [u0, u1, u2]).length = 3 := by
        rw [LENGTH_LEFT_ACTION_LIST]; rfl
      obtain ⟨a, b, c, hvl⟩ := p7_list3_eq (leftActionList p [u0, u1, u2]) hvl3
      rw [hvl] at hset hinit
      have hsetabc : setOfList [a, b, c] = setOfList [u0, u1, u2] := hset
      have hcardabc : Nat.card (setOfList [a, b, c]) = 3 := by
        rw [hsetabc,
          show setOfList [u0, u1, u2] = ({u0, u1, u2} : Set V3) from by ext t; simp [setOfList]]
        exact p7_card3_of_distinct
          (hdistu 0 1 (by simp) (by simp) (by norm_num))
          (hdistu 0 2 (by simp) (by simp) (by norm_num))
          (hdistu 1 2 (by simp) (by simp) (by norm_num))
      have hdistabc := CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT [a, b, c]
        (by rw [hcardabc]; rfl)
      have hab : a ≠ b := hdistabc 0 1 (by norm_num) (by norm_num) (by norm_num)
      have hac : a ≠ c := hdistabc 0 2 (by norm_num) (by norm_num) (by norm_num)
      have hbc : b ≠ c := hdistabc 1 2 (by norm_num) (by norm_num) (by norm_num)
      rcases p7_initSublist_three hinit hpos with heq | heq | heq
      · -- full prefix
        rw [heq]
        exact (p7_voronoiNondg_congr hsetabc rfl).2 hfullu
      · -- pair prefix
        rw [heq]
        refine ⟨by norm_num, ?_, ?_⟩
        · intro t ht
          have ht' : t ∈ setOfList [a, b, c] := p7_setOfList_append ht
          rw [hsetabc] at ht'
          exact hsubu ht'
        · have hsubp : setOfList [a, b] ⊆ setOfList [u0, u1, u2] := by
            rw [← hsetabc]
            exact p7_setOfList_append
          have hhla : hl [a, b] < Real.sqrt 2 := by
            have hle : radV (setOfList [a, b]) ≤ radV (setOfList [u0, u1, u2]) :=
              RADV_MONO (setOfList [u0, u1, u2]) (setOfList [a, b])
                hindu hsubp (Set.nonempty_iff_ne_empty.mp ⟨a, by simp [setOfList]⟩)
            have hhlu : radV (setOfList [u0, u1, u2]) < Real.sqrt 2 := by
              simpa [hl] using hl2
            rw [hl]
            linarith
          have haV : a ∈ V := hsubu (by rw [← hsetabc]; simp [setOfList])
          have hbV : b ∈ V := hsubu (by rw [← hsetabc]; simp [setOfList])
          have hdim2 := p7_affDim_voronoiList_pair V a b hV haV hbV hab hhla
          show affDim (voronoiList V [a, b]) + ((2 : ℕ) : ℤ) = 4
          rw [hdim2]
          norm_num
      · -- singleton prefix
        rw [heq]
        refine ⟨by norm_num, ?_, ?_⟩
        · intro t ht
          have ht' : t ∈ setOfList [a, b, c] := p7_setOfList_append ht
          rw [hsetabc] at ht'
          exact hsubu ht'
        · show affDim (voronoiList V [a]) + ((1 : ℕ) : ℤ) = 4
          rw [VORONOI_LIST_SING V a, AFF_DIM_VORONOI_CLOSED V a hV]
          norm_num
    · -- k = 3
      obtain ⟨u0, u1, u2, u3, rfl⟩ := p7_list4_eq ul (by rw [hlenu])
      have hvl4 : (leftActionList p [u0, u1, u2, u3]).length = 4 := by
        rw [LENGTH_LEFT_ACTION_LIST]; rfl
      obtain ⟨x0, x1, x2, x3, hvl⟩ := p7_list4_eq (leftActionList p [u0, u1, u2, u3]) hvl4
      rw [hvl] at hset hinit
      have hsetx : setOfList [x0, x1, x2, x3] = setOfList [u0, u1, u2, u3] := hset
      have hcardx4 : Nat.card (setOfList [x0, x1, x2, x3]) = 4 := by
        have hcardu4 : Nat.card (setOfList [u0, u1, u2, u3]) = 4 := by
          simpa using hcardu
        rw [hsetx, hcardu4]
      have hdistx4 := CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT [x0, x1, x2, x3]
        (by rw [hcardx4]; rfl)
      have hdx : x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x3 ∧ x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 :=
        ⟨hdistx4 0 1 (by norm_num) (by norm_num) (by norm_num),
         hdistx4 0 2 (by norm_num) (by norm_num) (by norm_num),
         hdistx4 0 3 (by norm_num) (by norm_num) (by norm_num),
         hdistx4 1 2 (by norm_num) (by norm_num) (by norm_num),
         hdistx4 1 3 (by norm_num) (by norm_num) (by norm_num),
         hdistx4 2 3 (by norm_num) (by norm_num) (by norm_num)⟩
      have hdu : u0 ≠ u1 ∧ u0 ≠ u2 ∧ u0 ≠ u3 ∧ u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 :=
        ⟨hdistu 0 1 (by simp) (by simp) (by norm_num),
         hdistu 0 2 (by simp) (by simp) (by norm_num),
         hdistu 0 3 (by simp) (by simp) (by norm_num),
         hdistu 1 2 (by simp) (by simp) (by norm_num),
         hdistu 1 3 (by simp) (by simp) (by norm_num),
         hdistu 2 3 (by simp) (by simp) (by norm_num)⟩
      have hfullu4 : voronoiNondg V [u0, u1, u2, u3] := by simpa using hfullu
      have hindu4 : ¬ affineDependent (setOfList [u0, u1, u2, u3]) := by simpa using hindu
      have hhlu4 : hl [u0, u1, u2, u3] < Real.sqrt 2 := by simpa using hl2
      have hsubu4 : setOfList [u0, u1, u2, u3] ⊆ V := by simpa using hsubu
      have hbar3 : barV V 3 [x0, x1, x2, x3] :=
        p7_barV3_of_set V u0 u1 u2 u3 hV hsubu4 hdu hindu4 hhlu4 hfullu4
          x0 x1 x2 x3 hsetx hdx
      exact hbar3.2 vl' ⟨hinit, hpos⟩

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
P1-P3). With `hfix` the statement matches the HOL original.
RESOLVED (2026-10-12 PA7 r3 lane): a moved point `j` exists (`hpid` + `hfix`),
and `ul = leftActionList p ul` forces `elV ul j = elV ul (p j)` via
`EL_LEFT_ACTION_LIST`, contradicting the all-distinct property from
`CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT` (both PA5 public kit). -/
theorem NOT_ID_IMP_LISTS_NOT_EQ (ul : List V3) (p : Equiv.Perm ℕ) (k : ℕ)
    (hlen : ul.length = k + 1) (hcard : Nat.card (setOfList ul) = k + 1)
    (hperm : permutes p (Set.Icc 0 k))
    (hfix : ∀ j : ℕ, k < j → p j = j) (hpid : ¬ (p = Equiv.refl ℕ)) :
    ¬ (ul = leftActionList p ul) := by
  intro heq
  obtain ⟨j, hjlt, hjne⟩ : ∃ j : ℕ, j < k + 1 ∧ p j ≠ j := by
    by_contra hcon
    push_neg at hcon
    refine hpid (Equiv.ext (fun j => ?_))
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact hcon j h
    · exact hfix j (by omega)
  have hp' : permutes p {i : ℕ | i < ul.length} := by
    intro x
    have hx := hperm x
    simp only [Set.mem_setOf_eq, Set.mem_Icc] at hx ⊢
    constructor
    · intro h0
      rw [hlen] at h0
      have hxI : x ∈ Set.Icc 0 k := ⟨Nat.zero_le x, by omega⟩
      have hpx := hx.1 hxI
      rw [hlen]
      omega
    · intro h0
      rw [hlen] at h0
      have hxI : p x ∈ Set.Icc 0 k := ⟨Nat.zero_le (p x), by omega⟩
      have hpx := hx.2 hxI
      rw [hlen]
      omega
  have hj : j < ul.length := by rw [hlen]; omega
  have hpj : p j < ul.length := by
    have h1 := (hperm j).1 ⟨Nat.zero_le j, by omega⟩
    simp only [Set.mem_Icc] at h1
    rw [hlen]
    omega
  have hdist := CARD_SET_OF_LIST_EQ_LENGTH_IMP_ALL_DISTINCT ul
    (by rw [hlen]; exact hcard) j (p j) hj hpj (Ne.symm hjne)
  have hEL := EL_LEFT_ACTION_LIST ul p hp' j hj
  rw [← heq] at hEL
  exact hdist hEL

/-- HL `NOT_ID_IMP_EXISTS_MAX_EQ_TRUNCATE_SIMPLEX` (Rogers.hl:9490).
ENCODING-FIX (SF item 24, 2026-09-30, user-approved batch A): same shape as
`NOT_ID_IMP_LISTS_NOT_EQ` — complement-fixing `hfix` added (sweep report
docs/encoding-risk-sweep.md §2.1 C2-2, same probe P1-P3 counterexample
engine); with `hfix` the statement matches the HOL original.
RESOLVED (2026-10-12 PA7 r3 lane): heads-equal case runs the maximal-truncation
argument of HOL — `K = {j ≤ k | trunc j ul = trunc j vl}` contains 0
(`TRUNCATE_0_EQ_HEAD`), its maximum `i` is `< k` (else `ul = vl = leftActionList`
contradicts `NOT_ID_IMP_LISTS_NOT_EQ`), and `EL (i+1)` equality would push
`i+1 ∈ K` past the maximum via `TRUNCATE_SIMPLEX_ADD1_ALT`. -/
theorem NOT_ID_IMP_EXISTS_MAX_EQ_TRUNCATE_SIMPLEX (ul : List V3)
    (p : Equiv.Perm ℕ) (k : ℕ) (hlen : ul.length = k + 1)
    (hcard : Nat.card (setOfList ul) = k + 1)
    (hperm : permutes p (Set.Icc 0 k))
    (hfix : ∀ j : ℕ, k < j → p j = j) (hpid : ¬ (p = Equiv.refl ℕ)) :
    ¬ (hdV ul = hdV (leftActionList p ul)) ∨
      ∃ j : ℕ, j < k ∧
        truncateSimplex j ul = truncateSimplex j (leftActionList p ul) ∧
        ¬ ((ul.getD (j + 1) default) = ((leftActionList p ul).getD (j + 1) default)) := by
  classical
  have hvlen : (leftActionList p ul).length = k + 1 := by
    rw [LENGTH_LEFT_ACTION_LIST ul p]
    exact hlen
  by_cases hhd : hdV ul = hdV (leftActionList p ul)
  · set vl := leftActionList p ul with hvl
    set K : Set ℕ := {j : ℕ | j ≤ k ∧ truncateSimplex j ul = truncateSimplex j vl} with hK
    have hK0 : (0:ℕ) ∈ K := by
      have h1 : truncateSimplex 0 ul = [hdV ul] := TRUNCATE_0_EQ_HEAD ul (by rw [hlen]; omega)
      have h2 : truncateSimplex 0 vl = [hdV vl] :=
        TRUNCATE_0_EQ_HEAD vl (by rw [hvlen]; omega)
      refine ⟨Nat.zero_le _, ?_⟩
      rw [h1, h2, hhd]
    have hKfin : K.Finite :=
      Set.Finite.subset (Finset.finite_toSet (Finset.Icc 0 k))
        (fun j hj => Finset.mem_coe.2 (Finset.mem_Icc.mpr ⟨Nat.zero_le j, hj.1⟩))
    have hKne : K ≠ ∅ := by
      intro h0
      have h5 : K.Nonempty := ⟨0, hK0⟩
      rw [h0] at h5
      obtain ⟨x, hx⟩ := h5
      exact absurd hx (Set.notMem_empty x)
    obtain ⟨i, hiK, himax⟩ := NUM_FINITE_IMP_MAX_EXISTS K hKfin hKne
    have hik : i < k := by
      by_contra hcon
      have hik1 : i ≤ k := hiK.1
      have hik' : i = k := by omega
      have he1 : truncateSimplex k ul = ul :=
        ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST k ul ul).mpr ⟨⟨[], by simp⟩, hlen⟩).1
      have he2 : truncateSimplex k vl = vl :=
        ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST k vl vl).mpr ⟨⟨[], by simp⟩, hvlen⟩).1
      rw [hik'] at hiK
      have huv : ul = vl := by rw [← he1, ← he2]; exact hiK.2
      have hne2 := NOT_ID_IMP_LISTS_NOT_EQ ul p k hlen hcard hperm hfix hpid
      exact absurd (by rw [← hvl]; exact huv) hne2
    refine Or.inr ⟨i, hik, hiK.2, ?_⟩
    intro hel
    have hdef : (default : V3) = 0 := rfl
    rw [hdef] at hel
    have hel' : elV ul (i + 1) = elV vl (i + 1) := hel
    have hi1K : (i + 1) ∈ K := by
      refine ⟨by omega, ?_⟩
      rw [TRUNCATE_SIMPLEX_ADD1_ALT ul i (by rw [hlen]; omega),
        TRUNCATE_SIMPLEX_ADD1_ALT vl i (by rw [hvlen]; omega),
        hiK.2, hel']
    have hmax := himax (i + 1) hi1K
    omega
  · exact Or.inl hhd

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
