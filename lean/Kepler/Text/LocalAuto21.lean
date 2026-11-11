/-
LocalAuto21 — Local Fan appendix lane, `scripts/local/CUXVZOZ.hl` (4348 ln,
0 defs + 62 thms; T. Hales 2013, check_completeness chapter).  The file
carries the deformation-existence kit for the 684-pent/planar strata
(`mk_simplex1`-driven edge and two-vertex deformations), the ε-interleaving
and continuity small-print, the `SKOLEM_PERIODIC` uniform-ε reduction over
the `periodic`/`periodic2` scs symmetries, the `BBs_inj`/`interior_angle1`
fan transport, the a/b/azim assumption reductions, the `dih_x`/`dihV`
obtuse-monotonicity kit, and the terminal chain `general_482_deformation`,
`CUXVZOZ`, `CJBDXXN` (all under the `main_nonlinear_terminal_v11` seal).

FILE MAP (all 62 HOL theorems, source order; `_p21` suffix throughout)
  Section A (simplex completion kit): `PQCSXWG1_SYM_p21` (sorry), `homog_2x2_p21`
    (proved), `simplex_unique_p21` (proved), `re_eqvl_pos_pos_p21` (proved),
    `mk_simplex_uniq_p21` (proved).
  Section B (ε/continuity small-print): `continuous_nbd_pos_p21`,
    `epsilon_pair_p21`, `epsilon_triple_p21`, `epsilon_quad_p21` (all proved).
  Section C (deformation existence): `deform_simplex_decrease_edge23_p21`
    (sorry giant), `deform_simplex_edge_exists_p21` (from the decrease thm),
    `deform_simplex_684_pent_p21` (sorry giant), `deform_684_pent_exists_p21`,
    `mk_planar_unique_p21` (sorry), `mk_planar2_continuous_p21` (sorry),
    `collinear_expand_p21` (sorry), `deform_planar_p21` (sorry giant),
    `deform_planar_exists_p21`, `deform_planar_second_version_p21` (sorry
    giant), `deform_planar_exists_second_version_p21`,
    `deformation_restrict_p21` (proved).
  Section D (periodic/mod kit): `SKOLEM_PERIODIC_p21`,
    `SKOLEM_PERIODIC2_p21` (proved), `scs_k_bounds_p21` (proved),
    `periodic2_MOD_p21`, `MOD_periodic2_p21`, `MOD_SHIFT_p21` (proved),
    `I_IMP_p21` (proved), `psort_inj_p21`, `psort_mod_p21`,
    `solve_mod_k_p21` (proved), `sin_azim_pos_p21` (proved).
  Section E (BBs/fan transport): `VV_SUC_EQ_IVS_RHO_NODE_PRIME_p21` (proved),
    `vv_azim_le_alt_p21`, `vv_split_azim_alt_p21` (proved),
    `interior_angle1_azim_p21`, `LOFA_IMP_INANGLE_EQ_AZIM_IVS_p21`
    (proved, definitional), `BBs_inj_p21` (proved), `IMAGE_FF_p21` (proved),
    `interior_angle1_azim_scs_p21` (proved), `deformation_BBs_p21`,
    `deformation_BBs_ALT_p21` (proved; §E1 `w4clamp` kit).
  Section F (assumption reductions): `a_assumption_reduction_p21`,
    `b_assumption_reduction_p21`, `azim_assumption_reduction_p21`,
    `WNWSHJT_ALT_p21` (sorry giants).
  Section G (obtuse-monotonicity kit): `dih_x5_mono_p21` (sorry),
    `delta_x5_delta_x6_p21` (proved), `dih_obtuse_mono_p21` (sorry),
    `dih_obtuse_mono_b_p21` (sorry), `square_add_neg_lemma_p21` (proved),
    `dihV_obtuse_mono_a_p21`, `dihV_obtuse_mono_b_p21` (sorry),
    `dihV_obtuse_mono_p21` (from a+b), `real_continuous_abs_p21` (proved).
  Section H (terminal chain): `deformation_restrict` lives above; here
    `MMs_minimize_tau_fun_p21` (sorry), `solve_mod_k_p21` (Section D),
    `tau3_taum_nonplanar_p21`, `tau3_azim_p21` (proved),
    `general_482_deformation_p21` (sorry giant), `CUXVZOZ_p21` and
    `CJBDXXN_p21` (each from `general_482_deformation_p21` by instantiating
    `p0`/`p2` — the HOL proofs are exactly these substitutions).

ENCODING NOTES
  - Import discipline: this file sits on the LocalAuto1/`PackingAuto18` side
    of the fatal `atn2` duplication. LocalAuto2/PackingAuto20 and everything
    importing them (LocalAuto9/LocalAuto11, hence `mkSimplex1_p11`,
    `taum_p11` and the PQCSXWG/`delta_x_sym` kit) must NOT be imported; the
    LocalAuto1-side twins `mkSimplex1`, `mkPlanar2`, `deltaX4`, `deltaX5`
    (LocalAuto1 — its `deltaX5` carries the corrected 6-term body since
    DEDUP 2026-09-17) and `upsX`/`deltaX` (canonical, SphereKit) are used
    instead.  Same-wave lanes LocalAuto19/20/22-27 are NOT imported.
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `0`; `a cross b` ↔
    `cross3 a b` (PackingAuto18:86); `dot` ↔ `⬝ᵥ`; `%` ↔ `•`; `dist (a,b)`
    ↔ `dist a b`; `norm` ↔ `‖·‖`; `pow 2` ↔ `^ 2`; `collinear {a,b,c}` ↔
    `Collinear ℝ {a,b,c}`; `coplanar s` ↔ `Coplanar s` (Geom.Coplanar,
    "⊂ affineSpan of three points").
  - DEDUP 2026-09-17: `dih_x` ↔ `dihXf`, `dih_y` ↔ `dihY`, `taum` ↔ `taum`
    — the LocalAuto16 `_p16` sphere-kit copies are deleted; these names are
    canonical `Kepler.Text.SphereKit` definitions now (the `taum` stub was
    upgraded to the real body).  `delta_x` ↔ `deltaX` (canonical,
    SphereKit).  `delta_x5` matched the canonical corrected `deltaX5`
    verbatim and its `_p21` copy is deleted (DEDUP 2026-09-17);
    `delta_x6` (sphere.hl:114) is NOT yet hosted by SphereKit, so the
    `deltaX6_p21` copy stays until that wave.
  - `deformation f V (a,b)` ↔ `Deformation f V a b` (LocalAuto1:128);
    `real_continuous_on (real_interval (--e,e))` ↔ `ContinuousOn _ (Ioo (-e) e)`;
    `real_continuous atreal t` / `continuous atreal t` ↔ `ContinuousAt`.
  - `periodic P k` ↔ `Periodic P k`, `periodic2` ↔ `Periodic2` (LocalAuto1);
    `IMAGE v (:num)` ↔ `Set.range v`; `IMAGE (\i. (v i, v (SUC i))) (:num)` ↔
    `Set.range fun i => (v i, v (i + 1))`; `interior_angle1 (vec 0) FF v` ↔
    `interiorAngle1 0 FF v` — definitionally `azim 0 v (rhoNode1 FF v)
    (ivsRhoNode1 FF v)`, which makes `interior_angle1_azim_p21` and its
    HOL duplicate `LOFA_IMP_INANGLE_EQ_AZIM_IVS` `rfl`.
  - scs accessors: `scs_k_v39 s` ↔ `s.k`, `scs_a_v39`/`scs_b_v39` ↔
    `s.a`/`s.b`, `is_scs_v39` ↔ `isScsV39`, `BBs_v39` ↔ `BBsV39`,
    `MMs_v39 s v` ↔ `v ∈ MMsV39 s`, `scs_basic_v39` ↔ `scsBasicV39`,
    `scs_generic` ↔ `scsGeneric`, `scs_diag` ↔ `scsDiag`, `psort` ↔ `psort`
    (LocalAuto1). `BBprime_v39 s v` ↔ `v ∈ BBprimeV39 s`.
  - `main_nonlinear_terminal_v11` (terminal.hl:37, bare Prop) ↔
    `mainNonlinearTerminalV11_p21 := main_nonlinear_terminal_v11` (alias of the
    `LocalAuto1` 109-entry registry conjunction; twin of LocalAuto18's `_p18`;
    DEF-FIX charter `docs/def-fix-charters/p21-anchor/`).
  - The HOL source's `let assumptions = ...` (CUXVZOZ.hl:2391) is a term
    abbreviation, not a theorem — not ported. The `//`-commented azim
    assumption inside `deformation_BBs` is dropped as in the source.
  - No `native_decide` anywhere; `sorry` bodies carry `-- DISCHARGES:`
    markers naming the missing HOL inputs.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto11
import Kepler.Text.LocalAuto14
import Kepler.Text.LocalAuto16
import Kepler.Text.LocalAuto21Kit
import Kepler.Text.LocalAuto37
import Kepler.Text.LocalAuto38
import Kepler.Text.SphereKit
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p21` copies and anchors

-- DEDUP 2026-09-17: the verbatim `delta_x5` copy that used to sit here
-- (`deltaX5`, nonlin_def.hl:435) is deleted against the canonical
-- corrected `Kepler.Text.SphereKit.deltaX5` — the bodies were identical
-- (both carry the full 6-term formula; LocalAuto1's old mis-port was
-- fixed 2026-09-17).  `deltaX6_p21` stays: SphereKit defers `delta_x6`. -/

/-- HOL `delta_x6` (sphere.hl:114): partial derivative of `delta_x` at
`x6`; not previously ported, and not yet hosted by `Kepler.Text.SphereKit`
(deferred wave). KEEP: local copy. -/
noncomputable def deltaX6_p21 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x2 - x3 * x6 + x1 * x4 + x2 * x5 - x4 * x5 +
    x3 * (-x3 + x1 + x2 - x6 + x4 + x5)

/-- EXTERNAL-ANCHOR: the `MainNonlinearTerminalV11` box (LocalAnchors:49;
terminal.hl:2240-2249/2496-2505, appendix.hl:1514-1532 `CUXVZOZ`):
`2 ≤ y1..y3 ≤ 2*h0`, `cstab ≤ y4 ≤ 3.915`, `y5 = y6 = 2`. Verbatim copy —
LocalAnchors cannot be imported next to LocalAuto1 (duplicate
`scsBasicV39`). NEEDS: merge. -/
def MainNonlinearTerminalV11_p21 (y : Fin 6 → ℝ) : Prop :=
  2 ≤ y 0 ∧ y 0 ≤ 2 * h0 ∧
    2 ≤ y 1 ∧ y 1 ≤ 2 * h0 ∧
    2 ≤ y 2 ∧ y 2 ≤ 2 * h0 ∧
    cstab ≤ y 3 ∧ y 3 ≤ 3.915 ∧
    y 4 = 2 ∧ y 5 = 2

/-- HOL `main_nonlinear_terminal_v11` (terminal.hl:37, bare Prop): **alias of
`LocalAuto1.main_nonlinear_terminal_v11`** (the closed conjunction of the 109
registry entries), per DEF-FIX charter `docs/def-fix-charters/p21-anchor/`.
The box predicate `MainNonlinearTerminalV11_p21` above stays a plain predicate
(it is no longer the anchor); twin of LocalAuto18's `mainNonlinearTerminalV11_p18`. -/
def mainNonlinearTerminalV11_p21 : Prop := main_nonlinear_terminal_v11

/-! ## Section A: PQCSXWG simplex completion kit -/

/-- HOL `PQCSXWG1_SYM` (CUXVZOZ.hl:61): the `Pqcsxwg.PQCSXWG1` signature with
`v1`/`v2` swapped. -/
theorem PQCSXWG1_SYM_p21 (v0 v1 v2 v3 : V3) (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4) (h5 : 0 < x5)
    (h6 : 0 < x6) (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (hx1 : x1 = dist v1 v0 ^ 2) (hx2 : x2 = dist v2 v0 ^ 2)
    (hx6 : x6 = dist v1 v2 ^ 2) (hΔ : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hv3 : v3 = mkSimplex1 v0 v2 v1 x2 x1 x3 x5 x4 x6) :
    x3 = dist v3 v0 ^ 2 ∧ x5 = dist v3 v1 ^ 2 ∧ x4 = dist v3 v2 ^ 2 ∧
      (v2 - v0) ⬝ᵥ cross3 (v1 - v0) (v3 - v0) > 0 := by
  -- PROVED from `LocalAuto11.PQCSXWG1_p11` applied to the swapped triple
  -- `(v0, v2, v1)` (`mkSimplex1 = mkSimplex1_p11` definitionally):
  -- `deltaX` is invariant under `x1 <-> x2`, `x4 <-> x5`, the collinearity
  -- set is permuted, and the swapped conclusion's positivity is exactly the
  -- `cross3 (v1 - v0) (v3 - v0)` triple product below.
  have hnc' : ¬ Collinear ℝ ({v0, v2, v1} : Set V3) := by
    intro hc
    apply hnc
    rwa [show ({v0, v2, v1} : Set V3) = {v0, v1, v2} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hc
  have hx6' : x6 = dist v2 v1 ^ 2 := by simpa only [dist_comm] using hx6
  have hΔ' : 0 < deltaX x2 x1 x3 x5 x4 x6 := by
    have hsym : deltaX x2 x1 x3 x5 x4 x6 = deltaX x1 x2 x3 x4 x5 x6 := by
      simp only [deltaX]; ring
    rw [hsym]; exact hΔ
  have hv3' : v3 = mkSimplex1_p11 v0 v2 v1 x2 x1 x3 x5 x4 x6 := by
    rw [hv3]; rfl
  have hp := PQCSXWG1_p11 v0 v2 v1 v3 x2 x1 x3 x5 x4 x6
    ⟨h2, h1, h3, h5, h4, h6, hnc', hx2, hx1, hx6', hΔ', hv3'⟩
  exact ⟨hp.1, hp.2.2.1, hp.2.1, hp.2.2.2⟩

/-- HOL `homog_2x2` (CUXVZOZ.hl:99): invertible 2×2 homogeneous linear
system has only the trivial solution. -/
theorem homog_2x2_p21 (a b c d x y : ℝ) (hdet : a * d - b * c ≠ 0)
    (h1 : a * x + b * y = 0) (h2 : c * x + d * y = 0) : x = 0 ∧ y = 0 := by
  have e1 : (a * d - b * c) * x = d * (a * x + b * y) - b * (c * x + d * y) := by ring
  have e2 : (a * d - b * c) * y = a * (c * x + d * y) - c * (a * x + b * y) := by ring
  rw [h1, h2] at e1 e2
  simp only [mul_zero, sub_zero] at e1 e2
  rcases mul_eq_zero.mp e1 with hx | hx
  · simp [hdet] at hx
  · refine ⟨hx, ?_⟩
    rcases mul_eq_zero.mp e2 with hy | hy
    · simp [hdet] at hy
    · exact hy

/-- HOL `simplex_unique` (CUXVZOZ.hl:113): a tetrahedron completion is
uniquely determined by the three distances and the orientation class. -/
theorem simplex_unique_p21 (v0 v1 v2 v3 v3' : V3)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (d0 : dist v0 v3 = dist v0 v3') (d1 : dist v1 v3 = dist v1 v3')
    (d2 : dist v2 v3 = dist v2 v3')
    (hre : reEqvl ((v3 - v0) ⬝ᵥ cross3 (v1 - v0) (v2 - v0))
      ((v3' - v0) ⬝ᵥ cross3 (v1 - v0) (v2 - v0))) : v3 = v3' := by
  -- PROVED: HOL `NONCOPLANAR_3_BASIS` basis-expansion ported verbatim (same
  -- statement) in `LocalAuto21Kit.simplex_unique_w2`.
  exact simplex_unique_w2 v0 v1 v2 v3 v3' hnc d0 d1 d2 hre

/-- HOL `re_eqvl_pos_pos` (CUXVZOZ.hl:218). -/
theorem re_eqvl_pos_pos_p21 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : reEqvl a b := by
  refine ⟨a / b, div_pos ha hb, ?_⟩
  field_simp

/-- HOL `mk_simplex_uniq` (CUXVZOZ.hl:232): `mk_simplex1` returns its
non-coplanar completion target. -/
theorem mk_simplex_uniq_p21 (v0 v1 v2 v3 : V3)
    (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3))
    (hpos : (v1 - v0) ⬝ᵥ cross3 (v2 - v0) (v3 - v0) > 0) :
    mkSimplex1 v0 v1 v2 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) = v3 := by
  -- PROVED: HOL proof ported verbatim (same statement) in
  -- `LocalAuto21Kit.mk_simplex_uniq_w2` (the `coplanar_delta_y` step is
  -- replaced there by the `Coplanar` hypothesis).
  exact mk_simplex_uniq_w2 v0 v1 v2 v3 hnc hpos

/-! ## Section B: ε and continuity small-print -/

/-- HOL `continuous_nbd_pos` (CUXVZOZ.hl:268): a positive point value of a
real-continuous map persists on a neighbourhood. -/
theorem continuous_nbd_pos_p21 {f : ℝ → ℝ} {t : ℝ} (hf : ContinuousAt f t)
    (hft : 0 < f t) : ∃ e, 0 < e ∧ ∀ t', |t' - t| < e → 0 < f t' := by
  have ev : Filter.Eventually (fun t' => 0 < f t') (nhds t) :=
    hf.eventually (Ioi_mem_nhds hft)
  rw [Metric.eventually_nhds_iff] at ev
  obtain ⟨e, he, hall⟩ := ev
  exact ⟨e, he, fun t' ht' => @hall t' (by rwa [Real.dist_eq])⟩

/-- HOL `epsilon_pair` (CUXVZOZ.hl:286). -/
theorem epsilon_pair_p21 (e e' : ℝ) (he : 0 < e) (he' : 0 < e') :
    ∃ e'', 0 < e'' ∧ (∀ t, |t| < e'' → |t| < e) ∧ (∀ t, |t| < e'' → |t| < e') := by
  refine ⟨min e e', lt_min he he', ?_, ?_⟩
  · intro t ht; exact (lt_min_iff.mp ht).1
  · intro t ht; exact (lt_min_iff.mp ht).2

/-- HOL `epsilon_triple` (CUXVZOZ.hl:298). -/
theorem epsilon_triple_p21 (e e' e'' : ℝ) (he : 0 < e) (he' : 0 < e') (he'' : 0 < e'') :
    ∃ e''', 0 < e''' ∧ (∀ t, |t| < e''' → |t| < e) ∧ (∀ t, |t| < e''' → |t| < e') ∧
      (∀ t, |t| < e''' → |t| < e'') := by
  obtain ⟨a, ha, h1, h2⟩ := epsilon_pair_p21 e e' he he'
  obtain ⟨b, hb, h3, h4⟩ := epsilon_pair_p21 e'' a he'' ha
  exact ⟨b, hb, fun t ht => h1 t (h4 t ht), fun t ht => h2 t (h4 t ht), h3⟩

/-- HOL `epsilon_quad` (CUXVZOZ.hl:310). -/
theorem epsilon_quad_p21 (e e' e'' e''' : ℝ) (he : 0 < e) (he' : 0 < e')
    (he'' : 0 < e'') (he''' : 0 < e''') :
    ∃ e'''', 0 < e'''' ∧ (∀ t, |t| < e'''' → |t| < e) ∧ (∀ t, |t| < e'''' → |t| < e') ∧
      (∀ t, |t| < e'''' → |t| < e'') ∧ (∀ t, |t| < e'''' → |t| < e''') := by
  obtain ⟨a, ha, h1, h2, h3⟩ := epsilon_triple_p21 e e' e'' he he' he''
  obtain ⟨b, hb, h4, h5⟩ := epsilon_pair_p21 e''' a he''' ha
  exact ⟨b, hb, fun t ht => h1 t (h5 t ht), fun t ht => h2 t (h5 t ht),
    fun t ht => h3 t (h5 t ht), h4⟩

/-! ## Section C: deformation existence kit
The HOL `let`-bound deformation maps are ported as explicit `_p21` defs so
that the statements stay readable; each is the verbatim lambda from the
source. -/

/-- HOL let `f` (CUXVZOZ.hl:325): the one-vertex `mk_simplex1` deformation
moving only `v1`, edge-23-prescribed. -/
private noncomputable def edge23F_p21 (v0 v1 v2 : V3) (g01 g12 : ℝ → ℝ) :
    V3 → ℝ → V3 :=
  fun w t => if w = v1 then
    mkSimplex1 0 v2 v0 (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
      ((dist v0 v1 + g01 t) ^ 2) ((dist v2 v1 + g12 t) ^ 2) (dist v0 v2 ^ 2)
  else w


/-! ### W2b helpers for HOL `deform_simplex_decrease_edge23` (CUXVZOZ.hl:322) -/

/-- Cyclic invariance of the scalar triple product `a·(b×c) = c·(a×b)`. -/
private theorem w2b_triple_cyclic (a b c : V3) :
    a ⬝ᵥ cross3 b c = c ⬝ᵥ cross3 a b := by
  simp only [cross3, dotProduct, cross_apply, Fin.sum_univ_three,
    Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- `deltaX` is invariant under `x1 <-> x2`, `x4 <-> x5` (HOL
`Merge_ineq.delta_x_sym`). -/
private theorem w2b_deltaX_sym (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x2 x1 x3 x5 x4 x6 = deltaX x1 x2 x3 x4 x5 x6 := by
  simp only [deltaX]
  ring

/-- Collinear points are coplanar with any fourth point. -/
private theorem w2b_collinear_coplanar {z w w1 w2 : V3}
    (hc : Collinear3 z w w1) : Coplanar ({z, w, w1, w2} : Set V3) := by
  by_cases hzw : z = w
  · have hset : ({z, w, w1, w2} : Set V3) = ({z, w1, w2} : Set V3) := by
      rw [hzw]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact coplanar_triple z w1 w2
  · refine ⟨z, w, w2, fun p hp => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · have hmem : p ∈ line[ℝ, z, w] :=
        hc.mem_affineSpan_of_mem_of_ne (p₁ := z) (p₂ := w)
          (by simp) (by simp) (by simp) hzw
      exact affineSpan_mono ℝ (by
        intro q hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
        tauto) hmem
    · exact mem_affineSpan ℝ (by simp)

/-- `¬ Coplanar {x,y,z,w}` gives all six pairwise distinctness facts. -/
private theorem w2b_ncop_ne_all {x y z w : V3}
    (h : ¬ Coplanar ({x, y, z, w} : Set V3)) :
    x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w := by
  have hxy : x ≠ y := by
    intro he
    apply h
    have hset : ({x, y, z, w} : Set V3) = ({y, z, w} : Set V3) := by
      rw [he]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact coplanar_triple y z w
  have hxz : x ≠ z := by
    intro he
    apply h
    have hset : ({x, y, z, w} : Set V3) = ({y, z, w} : Set V3) := by
      rw [he]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact coplanar_triple y z w
  have hxw : x ≠ w := by
    intro he
    apply h
    have hset : ({x, y, z, w} : Set V3) = ({y, z, w} : Set V3) := by
      rw [he]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact coplanar_triple y z w
  have hyz : y ≠ z := by
    intro he
    apply h
    have hset : ({x, y, z, w} : Set V3) = ({x, z, w} : Set V3) := by
      rw [he]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact coplanar_triple x z w
  have hyw : y ≠ w := by
    intro he
    apply h
    have hset : ({x, y, z, w} : Set V3) = ({x, z, w} : Set V3) := by
      rw [he]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact coplanar_triple x z w
  have hzw' : z ≠ w := by
    intro he
    apply h
    have hset : ({x, y, z, w} : Set V3) = ({x, y, w} : Set V3) := by
      rw [he]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact coplanar_triple x y w
  exact ⟨hxy, hxz, hxw, hyz, hyw, hzw'⟩

/-- Cayley–Menger positivity off non-coplanarity, in the argument order used
by the `PQCSXWG1_SYM`/`PQCSXWG2_ATREAL` consumption site. -/
private theorem w2b_deltaX_pos_of_ncop {v0 v1 v2 : V3}
    (hnc : ¬ Coplanar ({0, v2, v0, v1} : Set V3)) :
    0 < deltaX (dist v2 0 ^ 2) (dist v0 0 ^ 2) (dist v1 0 ^ 2)
      (dist v0 v1 ^ 2) (dist v2 v1 ^ 2) (dist v0 v2 ^ 2) := by
  rw [← delta_delta_x]
  rw [dist_comm v2 0, dist_comm v0 0, dist_comm v1 0, dist_comm v0 v2]
  exact (POS_EQ_NOT_COPLANANR 0 v2 v0 v1).2
    (fun hc => hnc (coplanar_eq_coplanar_alt.mpr hc))

/-- Cancel squares with nonnegative sides. -/
private theorem w2b_sq_eq_of_nonneg {x y : ℝ} (h : x ^ 2 = y ^ 2)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : x = y := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
  · exact h1
  · linarith

/-- HOL `deform_simplex_decrease_edge23` (CUXVZOZ.hl:322): moving `v1`
continuously along both adjacent edges keeps the simplex rigid on the
sphere and non-coplanar near `t = 0`. -/
theorem deform_simplex_decrease_edge23_p21 (V : Set V3) (g01 g12 : ℝ → ℝ)
    (v0 v1 v2 : V3) (e : ℝ)
    (hnc : ¬ Coplanar ({0, v0, v1, v2} : Set V3)) (hcr : v1 ⬝ᵥ cross3 v2 v0 > 0)
    (he : 0 < e) (hc01 : ContinuousOn g01 (Ioo (-e) e))
    (hc12 : ContinuousOn g12 (Ioo (-e) e)) (h01 : g01 0 = 0) (h12 : g12 0 = 0) :
    ∃ e', 0 < e' ∧ Deformation (edge23F_p21 v0 v1 v2 g01 g12) V (-e') e' ∧
      (∀ v t, v ≠ v1 → edge23F_p21 v0 v1 v2 g01 g12 v t = v) ∧
      (∀ t, |t| < e' → dist v0 (edge23F_p21 v0 v1 v2 g01 g12 v1 t) = dist v0 v1 + g01 t ∧
        dist v2 (edge23F_p21 v0 v1 v2 g01 g12 v1 t) = dist v2 v1 + g12 t ∧
        ‖edge23F_p21 v0 v1 v2 g01 g12 v1 t‖ = ‖v1‖) := by
  have hnc' : ¬ Coplanar ({0, v2, v0, v1} : Set V3) := by
    intro hc
    apply hnc
    rwa [show ({0, v2, v0, v1} : Set V3) = ({0, v0, v1, v2} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hc
  have hncol : ¬ Collinear3 (0 : V3) v2 v0 := fun hcol =>
    hnc' (w2b_collinear_coplanar (z := 0) (w := v2) (w1 := v0) (w2 := v1) hcol)
  have hncol' : ¬ Collinear3 (0 : V3) v0 v2 := by
    show ¬ Collinear ℝ ({0, v0, v2} : Set V3)
    rw [show ({0, v0, v2} : Set V3) = ({0, v2, v0} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact hncol
  obtain ⟨h0v0, h0v1, h0v2, hv01, hv02, hv12⟩ := w2b_ncop_ne_all hnc
  have hval : ∀ (w : V3) (t : ℝ),
      edge23F_p21 v0 v1 v2 g01 g12 w t =
        if w = v1 then
          mkSimplex1 0 v2 v0 (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
            ((dist v0 v1 + g01 t) ^ 2) ((dist v2 v1 + g12 t) ^ 2) (dist v0 v2 ^ 2)
        else w := fun w t => rfl
  -- the moving vertex starts at `v1`
  have hpos1 : (v2 - (0 : V3)) ⬝ᵥ cross3 (v0 - (0 : V3)) (v1 - (0 : V3)) > 0 := by
    rw [sub_zero, sub_zero, sub_zero, w2b_triple_cyclic v2 v0 v1]
    exact hcr
  have hf0 : edge23F_p21 v0 v1 v2 g01 g12 v1 0 = v1 := by
    rw [hval v1 0, if_pos rfl, h01, h12, add_zero, add_zero]
    rw [show ‖v2‖ ^ 2 = dist (0 : V3) v2 ^ 2 from by
          rw [dist_eq_norm, zero_sub, norm_neg],
        show ‖v0‖ ^ 2 = dist (0 : V3) v0 ^ 2 from by
          rw [dist_eq_norm, zero_sub, norm_neg],
        show ‖v1‖ ^ 2 = dist (0 : V3) v1 ^ 2 from by
          rw [dist_eq_norm, zero_sub, norm_neg],
        show dist v0 v2 ^ 2 = dist v2 v0 ^ 2 from by rw [dist_comm v0 v2]]
    exact mk_simplex_uniq_w2 0 v2 v0 v1 hnc' hpos1
  -- `deltaX` positivity at `0` and near `0`
  have hd0 : 0 < deltaX (dist v2 0 ^ 2) (dist v0 0 ^ 2) (dist v1 0 ^ 2)
      (dist v0 v1 ^ 2) (dist v2 v1 ^ 2) (dist v0 v2 ^ 2) :=
    w2b_deltaX_pos_of_ncop hnc'
  have hd_at0 : 0 < deltaX (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
      ((dist v0 v1 + g01 0) ^ 2) ((dist v2 v1 + g12 0) ^ 2) (dist v0 v2 ^ 2) := by
    rw [h01, h12, add_zero, add_zero]
    rw [show ‖v2‖ ^ 2 = dist v2 0 ^ 2 from by rw [dist_eq_norm, sub_zero],
        show ‖v0‖ ^ 2 = dist v0 0 ^ 2 from by rw [dist_eq_norm, sub_zero],
        show ‖v1‖ ^ 2 = dist v1 0 ^ 2 from by rw [dist_eq_norm, sub_zero]]
    exact hd0
  have hg01 : ContinuousAt g01 0 := hc01.continuousAt (Ioo_mem_nhds (by linarith) he)
  have hg12 : ContinuousAt g12 0 := hc12.continuousAt (Ioo_mem_nhds (by linarith) he)
  have hdcont : ContinuousAt (fun t => deltaX (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
      ((dist v0 v1 + g01 t) ^ 2) ((dist v2 v1 + g12 t) ^ 2) (dist v0 v2 ^ 2)) 0 := by
    have h4 : ContinuousAt (fun t : ℝ => (dist v0 v1 + g01 t) ^ 2) 0 :=
      (continuousAt_const.add hg01).pow 2
    have h5 : ContinuousAt (fun t : ℝ => (dist v2 v1 + g12 t) ^ 2) 0 :=
      (continuousAt_const.add hg12).pow 2
    simp only [deltaX]
    fun_prop
  obtain ⟨e1, he1, hδ⟩ := continuous_nbd_pos_p21 hdcont hd_at0
  -- positivity of the two moving edge lengths near `0`
  have hd01pos : 0 < dist v0 v1 + g01 0 := by rw [h01, add_zero]; exact dist_pos.mpr hv01
  have hd21pos : 0 < dist v2 v1 + g12 0 := by
    rw [h12, add_zero]; exact dist_pos.mpr (fun h => hv12 h.symm)
  obtain ⟨ea, hea, hpa⟩ := continuous_nbd_pos_p21 (continuousAt_const.add hg01) hd01pos
  obtain ⟨eb, heb, hpb⟩ := continuous_nbd_pos_p21 (continuousAt_const.add hg12) hd21pos
  obtain ⟨e2, he2, h2a, h2b⟩ := epsilon_pair_p21 ea eb hea heb
  -- a working radius for everything except the pointwise clauses
  set E : ℝ := min e (min e1 e2) with hEdef
  have hEpos : 0 < E := lt_min he (lt_min he1 he2)
  have hEe : E ≤ e := min_le_left e (min e1 e2)
  have hEe1 : E ≤ e1 := le_trans (min_le_right e (min e1 e2)) (min_le_left e1 e2)
  have hEe2 : E ≤ e2 := le_trans (min_le_right e (min e1 e2)) (min_le_right e1 e2)
  -- continuity of the moving vertex on the whole working interval
  have hcont_at : ∀ r ∈ Ioo (-E) E,
      ContinuousAt (fun t => edge23F_p21 v0 v1 v2 g01 g12 v1 t) r := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have habs : |r| < e1 := by
      rw [abs_lt]; constructor <;> linarith
    have hre : r ∈ Ioo (-e) e := ⟨by linarith, by linarith⟩
    have hgr1 : ContinuousAt g01 r := hc01.continuousAt (Ioo_mem_nhds hre.1 hre.2)
    have hgr2 : ContinuousAt g12 r := hc12.continuousAt (Ioo_mem_nhds hre.1 hre.2)
    have hff : (fun t => edge23F_p21 v0 v1 v2 g01 g12 v1 t)
        = fun t => mkSimplex1_p11 0 v2 v0 (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
            ((dist v0 v1 + g01 t) ^ 2) ((dist v2 v1 + g12 t) ^ 2) (dist v0 v2 ^ 2) := by
      funext t
      rw [hval v1 t, if_pos rfl]
      rfl
    rw [hff]
    refine PQCSXWG2_ATREAL_p11 (v0 := fun _ => (0 : V3)) (v1 := fun _ => v2)
      (v2 := fun _ => v0)
      (x1 := fun _ => ‖v2‖ ^ 2) (x2 := fun _ => ‖v0‖ ^ 2)
      (x3 := fun _ => ‖v1‖ ^ 2)
      (x4 := fun t => (dist v0 v1 + g01 t) ^ 2)
      (x5 := fun t => (dist v2 v1 + g12 t) ^ 2)
      (x6 := fun _ => dist v0 v2 ^ 2) (a := r)
      hncol ?hx1 ?hx2 ?hx6 ?hd ?hv0 ?hv1 ?hv2 ?hx1c ?hx2c ?hx3c ?hx4c ?hx5c ?hx6c
    · -- x1 a = dist (v1 a) (v0 a)^2
      show ‖v2‖ ^ 2 = dist v2 (0 : V3) ^ 2
      rw [dist_eq_norm, sub_zero]
    · show ‖v0‖ ^ 2 = dist v0 (0 : V3) ^ 2
      rw [dist_eq_norm, sub_zero]
    · show dist v0 v2 ^ 2 = dist v2 v0 ^ 2
      rw [dist_comm v0 v2]
    · -- deltaX positivity at `r`
      have hδr := hδ r (by simpa using habs)
      exact hδr
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact (continuousAt_const.add hgr1).pow 2
    · exact (continuousAt_const.add hgr2).pow 2
    · exact continuousAt_const
  -- final radius: the continuity part runs on `E`
  refine ⟨E, hEpos, ?_, ?_, ?_⟩
  · -- `Deformation`
    refine ⟨?_, ?_, ?_⟩
    · constructor <;> linarith
    · intro v _ r hr
      by_cases hvv : v = v1
      · subst hvv
        exact hcont_at r hr
      · have hconst : edge23F_p21 v0 v1 v2 g01 g12 v = fun _ => v := by
          funext t
          rw [hval v t, if_neg hvv]
        rw [hconst]
        exact continuousAt_const
    · intro v _
      by_cases hvv : v = v1
      · subst hvv
        exact hf0
      · rw [hval v 0, if_neg hvv]
  · intro v t hvv
    rw [hval v t, if_neg hvv]
  · -- the three stellar facts
    intro t ht
    have htE : |t| < E := ht
    have ht1 : |t| < e1 := lt_of_lt_of_le htE hEe1
    have ht2 : |t| < e2 := lt_of_lt_of_le htE hEe2
    have hposa : 0 < dist v0 v1 + g01 t :=
      hpa t (by simpa using h2a t ht2)
    have hposb : 0 < dist v2 v1 + g12 t :=
      hpb t (by simpa using h2b t ht2)
    have hΔ : 0 < deltaX (‖v0‖ ^ 2) (‖v2‖ ^ 2) (‖v1‖ ^ 2)
        ((dist v2 v1 + g12 t) ^ 2) ((dist v0 v1 + g01 t) ^ 2) (dist v0 v2 ^ 2) := by
      rw [w2b_deltaX_sym]
      exact hδ t (by simpa using ht1)
    have hv3 : edge23F_p21 v0 v1 v2 g01 g12 v1 t
        = mkSimplex1 0 v2 v0 (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
            ((dist v0 v1 + g01 t) ^ 2) ((dist v2 v1 + g12 t) ^ 2) (dist v0 v2 ^ 2) := by
      rw [hval v1 t, if_pos rfl]
    obtain ⟨h1, h2, h3, -⟩ := PQCSXWG1_SYM_p21 0 v0 v2
      (edge23F_p21 v0 v1 v2 g01 g12 v1 t)
      (‖v0‖ ^ 2) (‖v2‖ ^ 2) (‖v1‖ ^ 2)
      ((dist v2 v1 + g12 t) ^ 2) ((dist v0 v1 + g01 t) ^ 2) (dist v0 v2 ^ 2)
      (pow_pos (norm_pos_iff.mpr h0v0.symm) 2)
      (pow_pos (norm_pos_iff.mpr h0v2.symm) 2)
      (pow_pos (norm_pos_iff.mpr h0v1.symm) 2)
      (pow_pos hposb 2) (pow_pos hposa 2)
      (pow_pos (dist_pos.mpr hv02) 2)
      hncol'
      (by show ‖v0‖ ^ 2 = dist v0 (0 : V3) ^ 2
          rw [dist_eq_norm, sub_zero])
      (by show ‖v2‖ ^ 2 = dist v2 (0 : V3) ^ 2
          rw [dist_eq_norm, sub_zero])
      (by show (dist v0 v2) ^ 2 = dist v0 v2 ^ 2
          rfl) hΔ hv3
    refine ⟨?_, ?_, ?_⟩
    · -- dist v0 (f v1 t) = dist v0 v1 + g01 t
      have h2' : dist v0 (edge23F_p21 v0 v1 v2 g01 g12 v1 t) ^ 2
          = (dist v0 v1 + g01 t) ^ 2 := by
        rw [dist_comm v0 (edge23F_p21 v0 v1 v2 g01 g12 v1 t)]
        exact h2.symm
      exact w2b_sq_eq_of_nonneg h2' dist_nonneg (le_of_lt hposa)
    · -- dist v2 (f v1 t) = dist v2 v1 + g12 t
      have h3' : dist v2 (edge23F_p21 v0 v1 v2 g01 g12 v1 t) ^ 2
          = (dist v2 v1 + g12 t) ^ 2 := by
        rw [dist_comm v2 (edge23F_p21 v0 v1 v2 g01 g12 v1 t)]
        exact h3.symm
      exact w2b_sq_eq_of_nonneg h3' dist_nonneg (le_of_lt hposb)
    · -- ‖f v1 t‖ = ‖v1‖
      have h1' : ‖v1‖ ^ 2 = ‖edge23F_p21 v0 v1 v2 g01 g12 v1 t‖ ^ 2 := by
        rw [h1, dist_eq_norm, sub_zero]
      exact (w2b_sq_eq_of_nonneg h1' (norm_nonneg _) (norm_nonneg _)).symm

/-- HOL `deform_simplex_edge_exists` (CUXVZOZ.hl:508): existential-witness
form of the preceding theorem. -/
theorem deform_simplex_edge_exists_p21 (V : Set V3) (g01 g12 : ℝ → ℝ)
    (v0 v1 v2 : V3) (e : ℝ) :
    ∃ f : V3 → ℝ → V3,
      (¬ Coplanar ({0, v0, v1, v2} : Set V3) → v1 ⬝ᵥ cross3 v2 v0 > 0 → 0 < e →
        ContinuousOn g01 (Ioo (-e) e) → ContinuousOn g12 (Ioo (-e) e) →
        g01 0 = 0 → g12 0 = 0 →
        ∃ e', 0 < e' ∧ Deformation f V (-e') e' ∧
          (∀ v t, v ≠ v1 → f v t = v) ∧
          (∀ t, |t| < e' → dist v0 (f v1 t) = dist v0 v1 + g01 t ∧
            dist v2 (f v1 t) = dist v2 v1 + g12 t ∧ ‖f v1 t‖ = ‖v1‖)) :=
  ⟨edge23F_p21 v0 v1 v2 g01 g12, fun hnc hcr he hc01 hc12 h01 h12 =>
    deform_simplex_decrease_edge23_p21 V g01 g12 v0 v1 v2 e hnc hcr he hc01 hc12 h01 h12⟩

/-- HOL let `f1` (CUXVZOZ.hl:536): the `mk_simplex1` deformation moving
`v2` within the 684 face. -/
private noncomputable def pent684F1_p21 (v0 v2 v3 : V3) (g23 : ℝ → ℝ) :
    V3 → ℝ → V3 :=
  fun w t => if w = v2 then
    mkSimplex1 0 v3 v0 (‖v3‖ ^ 2) (‖v0‖ ^ 2) (‖v2‖ ^ 2)
      (dist v0 v2 ^ 2) ((dist v3 v2 + g23 t) ^ 2) (dist v0 v3 ^ 2)
  else w

/-- HOL let `f` (CUXVZOZ.hl:539): the two-vertex 684-pent deformation
moving `v2` by `f1` and then `v1` onto the moved triangle. -/
private noncomputable def pent684F_p21 (v0 v1 v2 v3 : V3) (g23 : ℝ → ℝ) :
    V3 → ℝ → V3 :=
  fun w t => if w = v2 then pent684F1_p21 v0 v2 v3 g23 v2 t
    else if w = v1 then
      mkSimplex1 0 (pent684F1_p21 v0 v2 v3 g23 v2 t) v0
        (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
        (dist v0 v1 ^ 2) (dist v2 v1 ^ 2) (dist v0 v2 ^ 2)
    else w

/-- HOL `deform_simplex_684_pent` (CUXVZOZ.hl:533): the 684-pent
deformation is a deformation and preserves the pentagon data near `0`. -/
theorem deform_simplex_684_pent_p21 (V : Set V3) (g23 : ℝ → ℝ) (v0 v1 v2 v3 : V3) (e : ℝ)
    (h1 : ¬ Coplanar ({0, v0, v2, v3} : Set V3))
    (h2 : ¬ Coplanar ({0, v0, v1, v2} : Set V3))
    (hc1 : v2 ⬝ᵥ cross3 v3 v0 > 0) (hc2 : v1 ⬝ᵥ cross3 v2 v0 > 0) (he : 0 < e)
    (h23 : ContinuousOn g23 (Ioo (-e) e)) (h23z : g23 0 = 0) :
    ∃ e', 0 < e' ∧ Deformation (pent684F_p21 v0 v1 v2 v3 g23) V (-e') e' ∧
      (∀ v t, v ≠ v1 ∧ v ≠ v2 → pent684F_p21 v0 v1 v2 v3 g23 v t = v) ∧
      (∀ t, |t| < e' →
        dist v0 (pent684F_p21 v0 v1 v2 v3 g23 v1 t) = dist v0 v1 ∧
        dist (pent684F_p21 v0 v1 v2 v3 g23 v2 t) (pent684F_p21 v0 v1 v2 v3 g23 v1 t) =
          dist v2 v1 ∧
        ‖pent684F_p21 v0 v1 v2 v3 g23 v1 t‖ = ‖v1‖ ∧
        dist (pent684F_p21 v0 v1 v2 v3 g23 v2 t) v0 = dist v2 v0 ∧
        dist (pent684F_p21 v0 v1 v2 v3 g23 v2 t) v3 = dist v2 v3 + g23 t ∧
        ‖pent684F_p21 v0 v1 v2 v3 g23 v2 t‖ = ‖v2‖) := by
  -- PROVED: HOL `deform_simplex_684_pent` (CUXVZOZ.hl:533) ported.  Stage 1
  -- (the `f1`/`v2` move) reads `PQCSXWG1_SYM` on `(0, v0, v3)` with the
  -- `g23`-dependent `deltaX` kept positive by `continuous_nbd_pos`, and
  -- `PQCSXWG2_ATREAL` for continuity; `NONPLANAR_OPEN` propagates
  -- `¬coplanar {0,v0,f1 v2 t,v3}` near `0`.  Stage 2 (the `f`/`v1` move)
  -- reads `PQCSXWG1_SYM` on `(0, v0, f1 v2 t)` with the constant `deltaX`
  -- of `h2`.  `mk_simplex_uniq` (twice) pins both `t = 0` values.
  obtain ⟨h0v0, h0v2, h0v3, hv0v2, hv0v3, hv2v3⟩ :=
    w2b_ncop_ne_all (x := (0 : V3)) (y := v0) (z := v2) (w := v3) h1
  obtain ⟨-, h0v1, -, hv0v1, -, hv1v2⟩ :=
    w2b_ncop_ne_all (x := (0 : V3)) (y := v0) (z := v1) (w := v2) h2
  -- the two `let`-bound maps unfold definitionally
  have hval1 : ∀ (w : V3) (t : ℝ), pent684F1_p21 v0 v2 v3 g23 w t =
      if w = v2 then mkSimplex1 0 v3 v0 (‖v3‖ ^ 2) (‖v0‖ ^ 2) (‖v2‖ ^ 2)
        (dist v0 v2 ^ 2) ((dist v3 v2 + g23 t) ^ 2) (dist v0 v3 ^ 2) else w :=
    fun w t => rfl
  have hval : ∀ (w : V3) (t : ℝ), pent684F_p21 v0 v1 v2 v3 g23 w t =
      if w = v2 then pent684F1_p21 v0 v2 v3 g23 v2 t
      else if w = v1 then
        mkSimplex1 0 (pent684F1_p21 v0 v2 v3 g23 v2 t) v0
          (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
          (dist v0 v1 ^ 2) (dist v2 v1 ^ 2) (dist v0 v2 ^ 2)
      else w := fun w t => rfl
  -- set permutations of the two non-coplanarity hypotheses
  have hnc023 : ¬ Collinear ℝ ({0, v0, v3} : Set V3) := by
    intro hcol
    apply h1
    have hcop := w2b_collinear_coplanar (z := (0 : V3)) (w := v0) (w1 := v3)
      (w2 := v2) hcol
    rwa [show ({0, v0, v3, v2} : Set V3) = ({0, v0, v2, v3} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hcop
  have hnc023' : ¬ Collinear ℝ ({0, v3, v0} : Set V3) := by
    have h := hnc023
    rwa [show ({0, v0, v3} : Set V3) = ({0, v3, v0} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
  have hnc_s1 : ¬ Coplanar ({0, v3, v0, v2} : Set V3) := by
    intro hc
    apply h1
    rwa [show ({0, v3, v0, v2} : Set V3) = ({0, v0, v2, v3} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hc
  have hnc_d1 : ¬ Coplanar ({0, v0, v3, v2} : Set V3) := by
    intro hc
    apply h1
    rwa [show ({0, v0, v3, v2} : Set V3) = ({0, v0, v2, v3} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hc
  have hnc_s2 : ¬ Coplanar ({0, v2, v0, v1} : Set V3) := by
    intro hc
    apply h2
    rwa [show ({0, v2, v0, v1} : Set V3) = ({0, v0, v1, v2} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hc
  have hnc_d2 : ¬ Coplanar ({0, v0, v2, v1} : Set V3) := by
    intro hc
    apply h2
    rwa [show ({0, v0, v2, v1} : Set V3) = ({0, v0, v1, v2} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hc
  -- `deltaX` positivity at `t = 0` (stage 1: triangle `0,v0,v3`)
  have hd0_1 : 0 < deltaX (‖v0‖ ^ 2) (‖v3‖ ^ 2) (‖v2‖ ^ 2)
      (dist v3 v2 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) := by
    have hraw := w2b_deltaX_pos_of_ncop (v0 := v3) (v1 := v2) (v2 := v0) hnc_d1
    rw [show ‖v0‖ ^ 2 = dist v0 0 ^ 2 from by rw [dist_eq_norm, sub_zero],
        show ‖v3‖ ^ 2 = dist v3 0 ^ 2 from by rw [dist_eq_norm, sub_zero],
        show ‖v2‖ ^ 2 = dist v2 0 ^ 2 from by rw [dist_eq_norm, sub_zero],
        show dist v0 v3 ^ 2 = dist v3 v0 ^ 2 from by rw [dist_comm v0 v3]]
    exact hraw
  -- `deltaX` positivity for the stage-2 triangle `0,v0,v1` (constant in `t`)
  have hd0_2 : 0 < deltaX (‖v0‖ ^ 2) (‖v2‖ ^ 2) (‖v1‖ ^ 2)
      (dist v2 v1 ^ 2) (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) := by
    have hraw := w2b_deltaX_pos_of_ncop (v0 := v2) (v1 := v1) (v2 := v0) hnc_d2
    rw [show ‖v0‖ ^ 2 = dist v0 0 ^ 2 from by rw [dist_eq_norm, sub_zero],
        show ‖v2‖ ^ 2 = dist v2 0 ^ 2 from by rw [dist_eq_norm, sub_zero],
        show ‖v1‖ ^ 2 = dist v1 0 ^ 2 from by rw [dist_eq_norm, sub_zero],
        show dist v0 v2 ^ 2 = dist v2 v0 ^ 2 from by rw [dist_comm v0 v2]]
    exact hraw
  -- stage-1 `deltaX` positivity is open near `0`
  have hg23_0 : ContinuousAt g23 0 := h23.continuousAt (Ioo_mem_nhds (by linarith) he)
  have hdcont1 : ContinuousAt (fun t => deltaX (‖v0‖ ^ 2) (‖v3‖ ^ 2) (‖v2‖ ^ 2)
      ((dist v3 v2 + g23 t) ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)) 0 := by
    have h5 : ContinuousAt (fun t : ℝ => (dist v3 v2 + g23 t) ^ 2) 0 :=
      (continuousAt_const.add hg23_0).pow 2
    simp only [deltaX]
    fun_prop
  obtain ⟨e1, he1, hδ1⟩ := continuous_nbd_pos_p21 hdcont1 (by
    simpa [h23z] using hd0_1)
  -- positivity of the moving edge length `dist v3 v2 + g23 t` near `0`
  have hpos0 : 0 < dist v3 v2 + g23 0 := by
    rw [h23z, add_zero]
    exact dist_pos.mpr (fun h => hv2v3 h.symm)
  obtain ⟨e2, he2, hpos2⟩ := continuous_nbd_pos_p21 (continuousAt_const.add hg23_0) hpos0
  -- `f1` fixes `v2` at `t = 0`
  have hf1_0 : pent684F1_p21 v0 v2 v3 g23 v2 0 = v2 := by
    rw [hval1 v2 0, if_pos rfl, h23z, add_zero]
    rw [show ‖v3‖ ^ 2 = dist 0 v3 ^ 2 from by rw [dist_eq_norm, zero_sub, norm_neg],
        show ‖v0‖ ^ 2 = dist 0 v0 ^ 2 from by rw [dist_eq_norm, zero_sub, norm_neg],
        show ‖v2‖ ^ 2 = dist 0 v2 ^ 2 from by rw [dist_eq_norm, zero_sub, norm_neg],
        show dist v0 v3 ^ 2 = dist v3 v0 ^ 2 from by rw [dist_comm v0 v3]]
    exact mk_simplex_uniq_p21 0 v3 v0 v2 hnc_s1 (by
      rw [sub_zero, sub_zero, sub_zero, w2b_triple_cyclic v3 v0 v2]
      exact hc1)
  -- working radius: `e` (g23 continuity) ∧ `e1` (`deltaX`) ∧ `e2` (edge sign)
  set E : ℝ := min e (min e1 e2) with hEdef
  have hEpos : 0 < E := lt_min he (lt_min he1 he2)
  have hEe : E ≤ e := min_le_left e (min e1 e2)
  have hEe1 : E ≤ e1 := le_trans (min_le_right e (min e1 e2)) (min_le_left e1 e2)
  have hEe2 : E ≤ e2 := le_trans (min_le_right e (min e1 e2)) (min_le_right e1 e2)
  -- continuity of the stage-1 moving vertex on `Ioo (-E) E`
  have hcont1_at : ∀ r ∈ Ioo (-E) E,
      ContinuousAt (fun t => pent684F1_p21 v0 v2 v3 g23 v2 t) r := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have habs : |r| < e1 := by
      rw [abs_lt]; constructor <;> linarith
    have hre : r ∈ Ioo (-e) e := ⟨by linarith, by linarith⟩
    have hgr : ContinuousAt g23 r := h23.continuousAt (Ioo_mem_nhds hre.1 hre.2)
    have hff : (fun t => pent684F1_p21 v0 v2 v3 g23 v2 t)
        = fun t => mkSimplex1_p11 0 v3 v0 (‖v3‖ ^ 2) (‖v0‖ ^ 2) (‖v2‖ ^ 2)
            (dist v0 v2 ^ 2) ((dist v3 v2 + g23 t) ^ 2) (dist v0 v3 ^ 2) := by
      funext t
      rw [hval1 v2 t, if_pos rfl]
      rfl
    rw [hff]
    refine PQCSXWG2_ATREAL_p11 (v0 := fun _ => (0 : V3)) (v1 := fun _ => v3)
      (v2 := fun _ => v0)
      (x1 := fun _ => ‖v3‖ ^ 2) (x2 := fun _ => ‖v0‖ ^ 2)
      (x3 := fun _ => ‖v2‖ ^ 2) (x4 := fun _ => dist v0 v2 ^ 2)
      (x5 := fun t => (dist v3 v2 + g23 t) ^ 2) (x6 := fun _ => dist v0 v3 ^ 2)
      (a := r)
      hnc023' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · show ‖v3‖ ^ 2 = dist v3 (0 : V3) ^ 2
      rw [dist_eq_norm, sub_zero]
    · show ‖v0‖ ^ 2 = dist v0 (0 : V3) ^ 2
      rw [dist_eq_norm, sub_zero]
    · show dist v0 v3 ^ 2 = dist v3 v0 ^ 2
      rw [dist_comm v0 v3]
    · -- `deltaX` at `r` (positional `x4`, `x5` order)
      rw [w2b_deltaX_sym (‖v0‖ ^ 2) (‖v3‖ ^ 2) (‖v2‖ ^ 2)
        ((dist v3 v2 + g23 r) ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)]
      exact hδ1 r (by simpa using habs)
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact (continuousAt_const.add hgr).pow 2
    · exact continuousAt_const
  -- stage-1 pointwise facts (on `|t| < E`)
  have hstage1 : ∀ t, |t| < E →
      ‖pent684F1_p21 v0 v2 v3 g23 v2 t‖ = ‖v2‖ ∧
      dist (pent684F1_p21 v0 v2 v3 g23 v2 t) v0 = dist v2 v0 ∧
      dist (pent684F1_p21 v0 v2 v3 g23 v2 t) v3 = dist v3 v2 + g23 t ∧
      v3 ⬝ᵥ cross3 v0 (pent684F1_p21 v0 v2 v3 g23 v2 t) > 0 := by
    intro t htE
    have ht1 : |t| < e1 := lt_of_lt_of_le htE hEe1
    have ht2 : |t| < e2 := lt_of_lt_of_le htE hEe2
    have hposb : 0 < dist v3 v2 + g23 t := hpos2 t (by simpa using ht2)
    have hΔ : 0 < deltaX (‖v0‖ ^ 2) (‖v3‖ ^ 2) (‖v2‖ ^ 2)
        ((dist v3 v2 + g23 t) ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) :=
      hδ1 t (by simpa using ht1)
    have hv3 : pent684F1_p21 v0 v2 v3 g23 v2 t
        = mkSimplex1 0 v3 v0 (‖v3‖ ^ 2) (‖v0‖ ^ 2) (‖v2‖ ^ 2)
            (dist v0 v2 ^ 2) ((dist v3 v2 + g23 t) ^ 2) (dist v0 v3 ^ 2) := by
      rw [hval1 v2 t, if_pos rfl]
    obtain ⟨hA, hB, hC, hD⟩ := PQCSXWG1_SYM_p21 0 v0 v3
      (pent684F1_p21 v0 v2 v3 g23 v2 t)
      (‖v0‖ ^ 2) (‖v3‖ ^ 2) (‖v2‖ ^ 2)
      ((dist v3 v2 + g23 t) ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (pow_pos (norm_pos_iff.mpr h0v0.symm) 2)
      (pow_pos (norm_pos_iff.mpr h0v3.symm) 2)
      (pow_pos (norm_pos_iff.mpr h0v2.symm) 2)
      (pow_pos hposb 2) (pow_pos (dist_pos.mpr hv0v2) 2)
      (pow_pos (dist_pos.mpr hv0v3) 2)
      hnc023
      (by show ‖v0‖ ^ 2 = dist v0 (0 : V3) ^ 2
          rw [dist_eq_norm, sub_zero])
      (by show ‖v3‖ ^ 2 = dist v3 (0 : V3) ^ 2
          rw [dist_eq_norm, sub_zero])
      rfl
      hΔ hv3
    have hD' : v3 ⬝ᵥ cross3 v0 (pent684F1_p21 v0 v2 v3 g23 v2 t) > 0 := by
      simpa only [sub_zero] using hD
    refine ⟨?_, ?_, ?_, hD'⟩
    · have hsq : ‖pent684F1_p21 v0 v2 v3 g23 v2 t‖ ^ 2 = ‖v2‖ ^ 2 := by
        rw [hA, dist_eq_norm, sub_zero]
      exact w2b_sq_eq_of_nonneg hsq (norm_nonneg _) (norm_nonneg _)
    · have hsq : dist (pent684F1_p21 v0 v2 v3 g23 v2 t) v0 ^ 2
          = dist v2 v0 ^ 2 := by
        rw [← hB, dist_comm v0 v2]
      exact w2b_sq_eq_of_nonneg hsq dist_nonneg dist_nonneg
    · have hsq : dist (pent684F1_p21 v0 v2 v3 g23 v2 t) v3 ^ 2
          = (dist v3 v2 + g23 t) ^ 2 := hC.symm
      exact w2b_sq_eq_of_nonneg hsq dist_nonneg (le_of_lt hposb)
  -- `f` fixes `v1` at `t = 0`
  have hf_0 : pent684F_p21 v0 v1 v2 v3 g23 v1 0 = v1 := by
    rw [hval v1 0, if_neg hv1v2, if_pos rfl, hf1_0]
    rw [show ‖v2‖ ^ 2 = dist 0 v2 ^ 2 from by rw [dist_eq_norm, zero_sub, norm_neg],
        show ‖v0‖ ^ 2 = dist 0 v0 ^ 2 from by rw [dist_eq_norm, zero_sub, norm_neg],
        show ‖v1‖ ^ 2 = dist 0 v1 ^ 2 from by rw [dist_eq_norm, zero_sub, norm_neg],
        show dist v0 v2 ^ 2 = dist v2 v0 ^ 2 from by rw [dist_comm v0 v2]]
    exact mk_simplex_uniq_p21 0 v2 v0 v1 hnc_s2 (by
      rw [sub_zero, sub_zero, sub_zero, w2b_triple_cyclic v2 v0 v1]
      exact hc2)
  -- `f` fixes `v2` at `t = 0`
  have hf2_0 : pent684F_p21 v0 v1 v2 v3 g23 v2 0 = v2 := by
    rw [hval v2 0, if_pos rfl, hf1_0]
  -- non-coplanarity of `{0, v0, f1 v2 t, v3}` persists near `0`
  obtain ⟨e3, he3, hnc3⟩ :=
    NONPLANAR_OPEN_p14 (v1 := fun _ => (0 : V3)) (v2 := fun _ => v0)
      (v3 := fun _ => v3) (v4 := fun t => pent684F1_p21 v0 v2 v3 g23 v2 t) 0
      (by simpa [hf1_0] using hnc_d1)
      continuousAt_const continuousAt_const continuousAt_const
      (hcont1_at 0 ⟨by linarith, hEpos⟩)
  set E2 : ℝ := min E e3 with hE2def
  have hE2pos : 0 < E2 := lt_min hEpos he3
  have hE2E : E2 ≤ E := min_le_left E e3
  have hE2e3 : E2 ≤ e3 := min_le_right E e3
  have hnc3' : ∀ t, |t| < e3 →
      ¬ Coplanar ({0, v0, v3, pent684F1_p21 v0 v2 v3 g23 v2 t} : Set V3) :=
    fun t ht => hnc3 t (by simpa using ht)
  have hncol2 : ∀ t, |t| < E2 →
      ¬ Collinear ℝ ({0, pent684F1_p21 v0 v2 v3 g23 v2 t, v0} : Set V3) := by
    intro t ht hcol
    have ht3 : |t| < e3 := lt_of_lt_of_le ht hE2e3
    apply hnc3' t ht3
    rw [show ({0, v0, v3, pent684F1_p21 v0 v2 v3 g23 v2 t} : Set V3) =
        ({0, pent684F1_p21 v0 v2 v3 g23 v2 t, v0, v3} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact w2b_collinear_coplanar (z := (0 : V3))
      (w := pent684F1_p21 v0 v2 v3 g23 v2 t) (w1 := v0) (w2 := v3) hcol
  -- continuity of the stage-2 moving vertex on `Ioo (-E2) E2`
  have hcont2_at : ∀ r ∈ Ioo (-E2) E2,
      ContinuousAt (fun t => pent684F_p21 v0 v1 v2 v3 g23 v1 t) r := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have habs2 : |r| < E2 := by rw [abs_lt]; exact ⟨hr1, hr2⟩
    have habsE : |r| < E := lt_of_lt_of_le habs2 hE2E
    have hre : r ∈ Ioo (-e) e := ⟨by linarith, by linarith⟩
    have hgr : ContinuousAt g23 r := h23.continuousAt (Ioo_mem_nhds hre.1 hre.2)
    have hff : (fun t => pent684F_p21 v0 v1 v2 v3 g23 v1 t)
        = fun t => mkSimplex1_p11 0 (pent684F1_p21 v0 v2 v3 g23 v2 t) v0
            (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
            (dist v0 v1 ^ 2) (dist v2 v1 ^ 2) (dist v0 v2 ^ 2) := by
      funext t
      rw [hval v1 t, if_neg hv1v2, if_pos rfl]
      rfl
    rw [hff]
    have hd2 : 0 < deltaX (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
        (dist v0 v1 ^ 2) (dist v2 v1 ^ 2) (dist v0 v2 ^ 2) := by
      rw [w2b_deltaX_sym (‖v0‖ ^ 2) (‖v2‖ ^ 2) (‖v1‖ ^ 2)
        (dist v2 v1 ^ 2) (dist v0 v1 ^ 2) (dist v0 v2 ^ 2)]
      exact hd0_2
    refine PQCSXWG2_ATREAL_p11 (v0 := fun _ => (0 : V3))
      (v1 := fun t => pent684F1_p21 v0 v2 v3 g23 v2 t) (v2 := fun _ => v0)
      (x1 := fun _ => ‖v2‖ ^ 2) (x2 := fun _ => ‖v0‖ ^ 2)
      (x3 := fun _ => ‖v1‖ ^ 2) (x4 := fun _ => dist v0 v1 ^ 2)
      (x5 := fun _ => dist v2 v1 ^ 2) (x6 := fun _ => dist v0 v2 ^ 2) (a := r)
      (hncol2 r habs2) ?_ ?_ ?_ hd2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · have hnorm := (hstage1 r habsE).1
      show ‖v2‖ ^ 2 = dist (pent684F1_p21 v0 v2 v3 g23 v2 r) (0 : V3) ^ 2
      rw [dist_eq_norm, sub_zero, ← hnorm]
    · show ‖v0‖ ^ 2 = dist v0 (0 : V3) ^ 2
      rw [dist_eq_norm, sub_zero]
    · have hd0 := (hstage1 r habsE).2.1
      show dist v0 v2 ^ 2 = dist (pent684F1_p21 v0 v2 v3 g23 v2 r) v0 ^ 2
      rw [hd0, dist_comm v0 v2]
    · exact continuousAt_const
    · exact hcont1_at r ⟨by linarith, by linarith⟩
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
  -- final radius
  refine ⟨E2, hE2pos, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · constructor <;> linarith
    · intro v _ r hr
      by_cases hvv : v = v1
      · rw [hvv]
        exact hcont2_at r hr
      · by_cases hvv2 : v = v2
        · rw [hvv2]
          obtain ⟨hr1, hr2⟩ := hr
          have hconst : pent684F_p21 v0 v1 v2 v3 g23 v2
              = fun t => pent684F1_p21 v0 v2 v3 g23 v2 t := by
            funext t
            rw [hval v2 t, if_pos rfl]
          rw [hconst]
          exact hcont1_at r ⟨by linarith, by linarith⟩
        · have hconst : pent684F_p21 v0 v1 v2 v3 g23 v = fun _ => v := by
            funext t
            rw [hval v t, if_neg hvv2, if_neg hvv]
          rw [hconst]
          exact continuousAt_const
    · intro v _
      by_cases hvv : v = v1
      · rw [hvv]
        exact hf_0
      · by_cases hvv2 : v = v2
        · rw [hvv2]
          exact hf2_0
        · rw [hval v 0, if_neg hvv2, if_neg hvv]
  · intro v t hvv
    rw [hval v t, if_neg hvv.2, if_neg hvv.1]
  · intro t ht
    have htE : |t| < E := lt_of_lt_of_le ht hE2E
    obtain ⟨hnorm2, hd20, hd23, -⟩ := hstage1 t htE
    obtain ⟨hA, hB, hC, -⟩ := PQCSXWG1_SYM_p21 0 v0
      (pent684F1_p21 v0 v2 v3 g23 v2 t)
      (pent684F_p21 v0 v1 v2 v3 g23 v1 t)
      (‖v0‖ ^ 2) (‖v2‖ ^ 2) (‖v1‖ ^ 2)
      (dist v2 v1 ^ 2) (dist v0 v1 ^ 2) (dist v0 v2 ^ 2)
      (pow_pos (norm_pos_iff.mpr h0v0.symm) 2)
      (pow_pos (norm_pos_iff.mpr h0v2.symm) 2)
      (pow_pos (norm_pos_iff.mpr h0v1.symm) 2)
      (pow_pos (dist_pos.mpr (fun h => hv1v2 h.symm)) 2)
      (pow_pos (dist_pos.mpr hv0v1) 2)
      (pow_pos (dist_pos.mpr hv0v2) 2)
      (by
        intro hcol
        apply hncol2 t ht
        rwa [show ({0, v0, pent684F1_p21 v0 v2 v3 g23 v2 t} : Set V3) =
            ({0, pent684F1_p21 v0 v2 v3 g23 v2 t, v0} : Set V3) from by
          ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hcol)
      (by show ‖v0‖ ^ 2 = dist v0 (0 : V3) ^ 2
          rw [dist_eq_norm, sub_zero])
      (by show ‖v2‖ ^ 2 = dist (pent684F1_p21 v0 v2 v3 g23 v2 t) (0 : V3) ^ 2
          rw [dist_eq_norm, sub_zero, ← hnorm2])
      (by show dist v0 v2 ^ 2 = dist v0 (pent684F1_p21 v0 v2 v3 g23 v2 t) ^ 2
          rw [dist_comm v0 (pent684F1_p21 v0 v2 v3 g23 v2 t), hd20, dist_comm v0 v2])
      hd0_2
      (by rw [hval v1 t, if_neg hv1v2, if_pos rfl])
    refine ⟨?_, ?_, ?_, by rw [hval v2 t, if_pos rfl]; exact hd20, ?_, ?_⟩
    · have hsq : dist v0 (pent684F_p21 v0 v1 v2 v3 g23 v1 t) ^ 2 = dist v0 v1 ^ 2 := by
        rw [dist_comm v0 (pent684F_p21 v0 v1 v2 v3 g23 v1 t)]
        exact hB.symm
      exact w2b_sq_eq_of_nonneg hsq dist_nonneg dist_nonneg
    · have hsq : dist (pent684F_p21 v0 v1 v2 v3 g23 v2 t)
          (pent684F_p21 v0 v1 v2 v3 g23 v1 t) ^ 2 = dist v2 v1 ^ 2 := by
        rw [show pent684F_p21 v0 v1 v2 v3 g23 v2 t
            = pent684F1_p21 v0 v2 v3 g23 v2 t from by rw [hval v2 t, if_pos rfl]]
        rw [dist_comm (pent684F1_p21 v0 v2 v3 g23 v2 t)
          (pent684F_p21 v0 v1 v2 v3 g23 v1 t)]
        exact hC.symm
      exact w2b_sq_eq_of_nonneg hsq dist_nonneg dist_nonneg
    · have hsq : ‖pent684F_p21 v0 v1 v2 v3 g23 v1 t‖ ^ 2 = ‖v1‖ ^ 2 := by
        rw [hA, dist_eq_norm, sub_zero]
      exact w2b_sq_eq_of_nonneg hsq (norm_nonneg _) (norm_nonneg _)
    · rw [hval v2 t, if_pos rfl, hd23, dist_comm v2 v3]
    · rw [hval v2 t, if_pos rfl]
      exact hnorm2

/-- HOL `deform_684_pent_exists` (CUXVZOZ.hl:805): existential-witness form
of the preceding theorem. -/
theorem deform_684_pent_exists_p21 (V : Set V3) (g23 : ℝ → ℝ) (v0 v1 v2 v3 : V3) (e : ℝ) :
    ∃ f : V3 → ℝ → V3,
      (¬ Coplanar ({0, v0, v2, v3} : Set V3) → ¬ Coplanar ({0, v0, v1, v2} : Set V3) →
        v2 ⬝ᵥ cross3 v3 v0 > 0 → v1 ⬝ᵥ cross3 v2 v0 > 0 → 0 < e →
        ContinuousOn g23 (Ioo (-e) e) → g23 0 = 0 →
        ∃ e', 0 < e' ∧ Deformation f V (-e') e' ∧
          (∀ v t, v ≠ v1 ∧ v ≠ v2 → f v t = v) ∧
          (∀ t, |t| < e' → dist v0 (f v1 t) = dist v0 v1 ∧
            dist (f v2 t) (f v1 t) = dist v2 v1 ∧ ‖f v1 t‖ = ‖v1‖ ∧
            dist (f v2 t) v0 = dist v2 v0 ∧
            dist (f v2 t) v3 = dist v2 v3 + g23 t ∧ ‖f v2 t‖ = ‖v2‖)) :=
  ⟨pent684F_p21 v0 v1 v2 v3 g23, fun h1 h2 hc1 hc2 he h23 h23z =>
    deform_simplex_684_pent_p21 V g23 v0 v1 v2 v3 e h1 h2 hc1 hc2 he h23 h23z⟩

private theorem g482_finrank_pair_le (a b : V3) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  haveI : Fintype ↥({a, b} : Set V3) := (Set.toFinite _).fintype
  have h := finrank_span_le_card (R := ℝ) (M := V3) (s := ({a, b} : Set V3))
  have hcard : ({a, b} : Set V3).toFinset.card ≤ 2 := by
    rw [show ({a, b} : Set V3).toFinset = ({a, b} : Finset V3) from by
      ext x
      simp]
    have hc := Finset.card_insert_le (a := a) (s := ({b} : Finset V3))
    simpa using hc
  omega

private theorem g482_image_vsub3 (p u v : V3) :
    ((fun x : V3 => x -ᵥ p) '' ({p, u, v} : Set V3))
      = ({0, u -ᵥ p, v -ᵥ p} : Set V3) := by
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl | rfl
    · exact Or.inl (vsub_self y)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, vsub_self _⟩
    · exact ⟨u, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨v, Or.inr (Or.inr rfl), rfl⟩

private theorem g482_span_zero_insert (a b : V3) :
    Submodule.span ℝ ({0, a, b} : Set V3) = Submodule.span ℝ ({a, b} : Set V3) := by
  refine le_antisymm ?_ (Submodule.span_mono (fun x hx => ?_))
  · rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto

private theorem g482_mem_span_of_coplanar {v0 v1 v2 v3 : V3}
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (hc : Coplanar ({v0, v1, v2, v3} : Set V3)) :
    v3 -ᵥ v0 ∈ Submodule.span ℝ ({v1 -ᵥ v0, v2 -ᵥ v0} : Set V3) := by
  obtain ⟨u, v, w, hsub⟩ := hc
  have h0 : v0 ∈ affineSpan ℝ ({u, v, w} : Set V3) := hsub (by simp)
  have h1 : v1 ∈ affineSpan ℝ ({u, v, w} : Set V3) := hsub (by simp)
  have h2 : v2 ∈ affineSpan ℝ ({u, v, w} : Set V3) := hsub (by simp)
  have h3 : v3 ∈ affineSpan ℝ ({u, v, w} : Set V3) := hsub (by simp)
  have he1 : v1 -ᵥ v0 ∈ vectorSpan ℝ ({u, v, w} : Set V3) := by
    have hm : v1 -ᵥ v0 ∈ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
      vsub_mem_vectorSpan (k := ℝ) (p₁ := v1) (p₂ := v0) h1 h0
    rwa [direction_affineSpan] at hm
  have he2 : v2 -ᵥ v0 ∈ vectorSpan ℝ ({u, v, w} : Set V3) := by
    have hm : v2 -ᵥ v0 ∈ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
      vsub_mem_vectorSpan (k := ℝ) (p₁ := v2) (p₂ := v0) h2 h0
    rwa [direction_affineSpan] at hm
  have hx : v3 -ᵥ v0 ∈ vectorSpan ℝ ({u, v, w} : Set V3) := by
    have hm : v3 -ᵥ v0 ∈ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
      vsub_mem_vectorSpan (k := ℝ) (p₁ := v3) (p₂ := v0) h3 h0
    rwa [direction_affineSpan] at hm
  have hle : Submodule.span ℝ ({v1 -ᵥ v0, v2 -ᵥ v0} : Set V3)
      ≤ vectorSpan ℝ ({u, v, w} : Set V3) := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact he1
    · exact he2
  have hS2 : Module.finrank ℝ (vectorSpan ℝ ({u, v, w} : Set V3)) ≤ 2 := by
    rw [vectorSpan_eq_span_vsub_set_right (k := ℝ) (p := u) (by simp)]
    rw [g482_image_vsub3 u v w]
    rw [g482_span_zero_insert (v -ᵥ u) (w -ᵥ u)]
    exact g482_finrank_pair_le (v -ᵥ u) (w -ᵥ u)
  have hvec : vectorSpan ℝ ({v0, v1, v2} : Set V3)
      = Submodule.span ℝ ({v1 -ᵥ v0, v2 -ᵥ v0} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right (k := ℝ) (p := v0) (by simp)]
    rw [show ((fun x : V3 => x -ᵥ v0) '' ({v0, v1, v2} : Set V3))
        = ({0, v1 -ᵥ v0, v2 -ᵥ v0} : Set V3) from by
      simpa using g482_image_vsub3 v0 v1 v2]
    rw [g482_span_zero_insert]
  have hpair_ge : 2 ≤ Module.finrank ℝ
      (Submodule.span ℝ ({v1 -ᵥ v0, v2 -ᵥ v0} : Set V3)) := by
    have h := collinear_iff_finrank_le_one (k := ℝ) (s := ({v0, v1, v2} : Set V3))
    have h' : ¬ Module.finrank ℝ (vectorSpan ℝ ({v0, v1, v2} : Set V3)) ≤ 1 := by
      intro hle1
      exact hnc (h.mpr hle1)
    rw [hvec] at h'
    omega
  have hpair_dim : Module.finrank ℝ
      (Submodule.span ℝ ({v1 -ᵥ v0, v2 -ᵥ v0} : Set V3)) = 2 :=
    le_antisymm (g482_finrank_pair_le _ _) hpair_ge
  have hSdim : Module.finrank ℝ (vectorSpan ℝ ({u, v, w} : Set V3)) = 2 := by
    have hmono : Module.finrank ℝ (Submodule.span ℝ ({v1 -ᵥ v0, v2 -ᵥ v0} : Set V3))
        ≤ Module.finrank ℝ (vectorSpan ℝ ({u, v, w} : Set V3)) := Submodule.finrank_mono hle
    omega
  have hEq : Submodule.span ℝ ({v1 -ᵥ v0, v2 -ᵥ v0} : Set V3)
      = vectorSpan ℝ ({u, v, w} : Set V3) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hpair_dim, hSdim])
  rw [← hEq] at hx
  exact hx

private theorem g482_norm_decomp (a b : ℝ) (e1 n : V3) (hn : inner ℝ e1 n = 0) :
    ‖a • e1 + b • n‖ ^ 2 = a ^ 2 * ‖e1‖ ^ 2 + b ^ 2 * ‖n‖ ^ 2 := by
  rw [norm_add_sq_real]
  have hinner : inner ℝ (a • e1) (b • n) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hn]; ring
  rw [hinner, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs]
  ring

private theorem g482_cross_add_smul (a b : ℝ) (e1 n z : V3) :
    cross3 (a • e1 + b • n) z = a • cross3 e1 z + b • cross3 n z := by
  ext i
  fin_cases i <;> simp [cross3, crossProduct, WithLp.ofLp_smul, WithLp.ofLp_add]

private theorem g482_cross_self (e1 : V3) : cross3 e1 e1 = 0 := by
  ext i
  fin_cases i <;> simp [cross3, crossProduct] <;> ring

private theorem g482_n_formula (e1 e2 : V3) :
    cross3 e1 (cross3 e1 e2) = (e1 ⬝ᵥ e2) • e1 - (e1 ⬝ᵥ e1) • e2 := by
  ext i
  fin_cases i <;> simp [cross3, crossProduct, dotProduct, Fin.sum_univ_three] <;> ring

private theorem g482_n_perp (e1 e2 : V3) : inner ℝ e1 (cross3 e1 (cross3 e1 e2)) = 0 := by
  rw [g482_n_formula]
  simp only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    inner_eq_dot, norm_sq_eq_dot]
  ring

private theorem g482_pair_li (v0 v1 v2 : V3)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3)) :
    LinearIndependent ℝ (![v1 - v0, v2 - v0] : Fin 2 → V3) := by
  have hne : v1 ≠ v0 := by
    intro h
    apply hnc
    rw [h]
    simpa using collinear_pair ℝ v0 v2
  have hcol := collinear3_iff_smul (v := v0) (w := v1) (w1 := v2) hne
  have hnot : ¬ ∃ c : ℝ, v2 - v0 = c • (v1 - v0) := fun ⟨c, hc⟩ => hnc (hcol.mpr ⟨c, hc⟩)
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra htne
    apply hnot
    refine ⟨-(t⁻¹ * s), ?_⟩
    have h1 : t • (v2 - v0) = -(s • (v1 - v0)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hst
    have h2 := congrArg (fun z : V3 => (1 / t) • z) h1
    simpa [smul_smul, inv_mul_cancel₀ htne] using h2
  subst ht
  have hs : s = 0 := by
    have h1 : s • (v1 - v0) = 0 := by simpa using hst
    exact (smul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)
  exact ⟨hs, rfl⟩

private theorem g482_pair_li_fin (v0 v1 v2 : V3)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3)) :
    LinearIndependent ℝ (![((v1 - v0 : V3) : Fin 3 → ℝ), ((v2 - v0 : V3) : Fin 3 → ℝ)] :
      Fin 2 → (Fin 3 → ℝ)) := by
  have hind := g482_pair_li v0 v1 v2 hnc
  rw [LinearIndependent.pair_iff] at hind ⊢
  intro s t hst
  have hV : s • (v1 - v0) + t • (v2 - v0) = 0 := by
    apply WithLp.ofLp_injective 2
    simpa [WithLp.ofLp_add, WithLp.ofLp_smul] using hst
  exact hind s t hV

private theorem g482_cross_ne (v0 v1 v2 : V3)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3)) :
    cross3 (v1 - v0) (v2 - v0) ≠ 0 := by
  have hLI := g482_pair_li_fin v0 v1 v2 hnc
  have hne := (crossProduct_ne_zero_iff_linearIndependent (F := ℝ)
    (v := ((v1 - v0 : V3) : Fin 3 → ℝ)) (w := ((v2 - v0 : V3) : Fin 3 → ℝ))).mpr hLI
  intro hz
  apply hne
  have := congrArg (fun z : V3 => (z : Fin 3 → ℝ)) hz
  simpa [cross3] using this

private theorem g482_n_cross_ne (e1 e2 : V3) (he1 : e1 ≠ 0) (hne : cross3 e1 e2 ≠ 0) :
    cross3 (cross3 e1 (cross3 e1 e2)) e1 ≠ 0 := by
  have hform : cross3 (cross3 e1 (cross3 e1 e2)) e1 = (e1 ⬝ᵥ e1) • cross3 e1 e2 := by
    ext i
    fin_cases i <;> simp [cross3, crossProduct, dotProduct, Fin.sum_univ_three] <;> ring
  rw [hform]
  refine smul_ne_zero ?_ hne
  rw [← norm_sq_eq_dot]
  exact ne_of_gt (pow_pos (norm_pos_iff.mpr he1) 2)


/-- HOL `mk_planar_unique` (CUXVZOZ.hl:839): a planar completion is
uniquely determined by distances and the cross-product ray. -/

theorem mk_planar_unique_p21 (v0 v1 v2 v3 v3' : V3)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (d0 : dist v0 v3 = dist v0 v3') (d1 : dist v1 v3 = dist v1 v3')
    (cp : Coplanar ({v0, v1, v2, v3} : Set V3))
    (cp' : Coplanar ({v0, v1, v2, v3'} : Set V3))
    (hcr : ∃ t : ℝ, 0 < t ∧ t • cross3 (v3 - v0) (v1 - v0) =
      cross3 (v3' - v0) (v1 - v0)) : v3 = v3' := by
  obtain ⟨t, htpos, hcr⟩ := hcr
  set e1 : V3 := v1 - v0
  set e2 : V3 := v2 - v0
  set x : V3 := v3 - v0
  set x' : V3 := v3' - v0
  set z : V3 := x - x'
  set n : V3 := cross3 e1 (cross3 e1 e2) with hn_def
  have hxP : x ∈ Submodule.span ℝ ({e1, e2} : Set V3) := by
    have := g482_mem_span_of_coplanar hnc cp
    simpa [e1, e2, x] using this
  have hx'P : x' ∈ Submodule.span ℝ ({e1, e2} : Set V3) := by
    have := g482_mem_span_of_coplanar hnc cp'
    simpa [e1, e2, x'] using this
  have he1ne : e1 ≠ 0 := by
    intro h
    apply hnc
    have hv : v1 = v0 := sub_eq_zero.mp h
    rw [hv]
    simpa using collinear_pair ℝ v0 v2
  have hd0n : ‖x‖ = ‖x'‖ := by
    have h := d0
    rw [dist_eq_norm, dist_eq_norm] at h
    rw [show ‖x‖ = ‖v0 - v3‖ from by
          rw [show x = v3 - v0 from rfl, ← neg_sub, norm_neg],
      show ‖x'‖ = ‖v0 - v3'‖ from by
          rw [show x' = v3' - v0 from rfl, ← neg_sub, norm_neg]]
    exact h
  have hd1n : ‖x - e1‖ = ‖x' - e1‖ := by
    have h := d1
    rw [dist_eq_norm, dist_eq_norm] at h
    have e : x - e1 = v3 - v1 := by simp [x, e1]
    have e' : x' - e1 = v3' - v1 := by simp [x', e1]
    rw [e, e',
      show ‖v3 - v1‖ = ‖v1 - v3‖ from by rw [← neg_sub, norm_neg],
      show ‖v3' - v1‖ = ‖v1 - v3'‖ from by rw [← neg_sub, norm_neg]]
    exact h
  have hcross_ne : cross3 e1 e2 ≠ 0 := by
    have := g482_cross_ne v0 v1 v2 hnc
    simpa [e1, e2] using this
  have hnform : n = (e1 ⬝ᵥ e2) • e1 - (e1 ⬝ᵥ e1) • e2 := by
    rw [hn_def]
    exact g482_n_formula e1 e2
  have hninner : inner ℝ e1 n = 0 := by
    rw [hn_def]
    exact g482_n_perp e1 e2
  have hLpos : (0 : ℝ) < e1 ⬝ᵥ e1 := by
    rw [← norm_sq_eq_dot]
    exact pow_pos (norm_pos_iff.mpr he1ne) 2
  have hnmem : n ∈ Submodule.span ℝ ({e1, e2} : Set V3) := by
    rw [hnform]
    refine Submodule.sub_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have he2mem : e2 ∈ Submodule.span ℝ ({e1, n} : Set V3) := by
    have hL : (e1 ⬝ᵥ e1) ≠ 0 := ne_of_gt hLpos
    have heq : e2 = ((e1 ⬝ᵥ e2) / (e1 ⬝ᵥ e1)) • e1 - (1 / (e1 ⬝ᵥ e1)) • n := by
      calc e2 = (1 / (e1 ⬝ᵥ e1)) • ((e1 ⬝ᵥ e1) • e2) := by
              rw [smul_smul, one_div, inv_mul_cancel₀ hL, one_smul]
        _ = (1 / (e1 ⬝ᵥ e1)) • ((e1 ⬝ᵥ e2) • e1 - n) := by
              have h : (e1 ⬝ᵥ e1) • e2 = (e1 ⬝ᵥ e2) • e1 - n := by
                rw [hnform]; abel
              rw [h]
        _ = (1 / (e1 ⬝ᵥ e1)) • ((e1 ⬝ᵥ e2) • e1) - (1 / (e1 ⬝ᵥ e1)) • n := by
              rw [smul_sub]
        _ = ((e1 ⬝ᵥ e2) / (e1 ⬝ᵥ e1)) • e1 - (1 / (e1 ⬝ᵥ e1)) • n := by
              rw [smul_smul, div_eq_inv_mul]
              ring_nf
    rw [heq]
    refine Submodule.sub_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hspan : Submodule.span ℝ ({e1, n} : Set V3) = Submodule.span ℝ ({e1, e2} : Set V3) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact hnmem
    · rw [Submodule.span_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact he2mem
  have hzP : z ∈ Submodule.span ℝ ({e1, n} : Set V3) := by
    rw [hspan]
    exact Submodule.sub_mem _ hxP hx'P
  have hxP' : x ∈ Submodule.span ℝ ({e1, n} : Set V3) := by
    rw [hspan]; exact hxP
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hzP
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hxP'
  have hze1 : inner ℝ z e1 = 0 := by
    have h0 : ‖x‖ ^ 2 = ‖x'‖ ^ 2 := by rw [hd0n]
    have h1 : ‖x - e1‖ ^ 2 = ‖x' - e1‖ ^ 2 := by rw [hd1n]
    have h2 : ‖x - e1‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x e1 + ‖e1‖ ^ 2 :=
      norm_sub_sq_real x e1
    have h3 : ‖x' - e1‖ ^ 2 = ‖x'‖ ^ 2 - 2 * inner ℝ x' e1 + ‖e1‖ ^ 2 :=
      norm_sub_sq_real x' e1
    have hx1 : inner ℝ x e1 = inner ℝ x' e1 := by linarith
    change inner ℝ (x - x') e1 = 0
    rw [inner_sub_left, hx1, sub_self]
  have ha0 : a = 0 := by
    have hn' : inner ℝ n e1 = 0 := by rw [real_inner_comm]; exact hninner
    have hz' : inner ℝ (a • e1 + b • n) e1 = 0 := by rw [hab]; exact hze1
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hn',
      real_inner_self_eq_norm_sq] at hz'
    have hL : (0 : ℝ) < ‖e1‖ ^ 2 := pow_pos (norm_pos_iff.mpr he1ne) 2
    have h : a * ‖e1‖ ^ 2 = 0 := by linarith
    exact (mul_eq_zero.mp h).resolve_right (ne_of_gt hL)
  have hzn : z = b • n := by
    rw [← hab, ha0, zero_smul, zero_add]
  have hx'eq : x' = p • e1 + (q - b) • n := by
    have hxz : x - z = x' := by
      change x - (x - x') = x'
      exact sub_sub_cancel x x'
    rw [← hxz, ← hpq, hzn]
    module
  have hN0 : b * (2 * q - b) * ‖n‖ ^ 2 = 0 := by
    have h0 : ‖x‖ ^ 2 = ‖x'‖ ^ 2 := by rw [hd0n]
    have hx1 : ‖x‖ ^ 2 = p ^ 2 * ‖e1‖ ^ 2 + q ^ 2 * ‖n‖ ^ 2 := by
      rw [← hpq]
      exact g482_norm_decomp p q e1 n hninner
    have hx2 : ‖x'‖ ^ 2 = p ^ 2 * ‖e1‖ ^ 2 + (q - b) ^ 2 * ‖n‖ ^ 2 := by
      rw [hx'eq]
      exact g482_norm_decomp p (q - b) e1 n hninner
    have hq : q ^ 2 * ‖n‖ ^ 2 = (q - b) ^ 2 * ‖n‖ ^ 2 := by linarith
    have hfac : q ^ 2 * ‖n‖ ^ 2 - (q - b) ^ 2 * ‖n‖ ^ 2
        = b * (2 * q - b) * ‖n‖ ^ 2 := by ring
    linarith
  have hxcross : cross3 x e1 = q • cross3 n e1 := by
    rw [← hpq, g482_cross_add_smul, g482_cross_self, smul_zero, zero_add]
  have hx'cross : cross3 x' e1 = (q - b) • cross3 n e1 := by
    rw [hx'eq, g482_cross_add_smul, g482_cross_self, smul_zero, zero_add]
  have hncn : cross3 n e1 ≠ 0 := by
    rw [hn_def]
    exact g482_n_cross_ne e1 e2 he1ne hcross_ne
  have hcross_eq : (t * q - (q - b)) • cross3 n e1 = 0 := by
    have h : t • cross3 x e1 = cross3 x' e1 := by
      simpa [x, x', e1] using hcr
    rw [hxcross, hx'cross, smul_smul] at h
    rw [sub_smul, h, sub_self]
  have htq : t * q = q - b := by
    rcases smul_eq_zero.mp hcross_eq with h | h
    · linarith
    · exact absurd h hncn
  have hb_eq : b = (1 - t) * q := by
    rw [sub_mul, one_mul]
    linarith
  have hz0 : z = 0 := by
    by_cases hN : ‖n‖ ^ 2 = 0
    · have hn0 : n = 0 := by
        have hn : ‖n‖ = 0 := by nlinarith [norm_nonneg n, hN]
        exact norm_eq_zero.mp hn
      rw [hzn, hn0, smul_zero]
    · have hNpos : 0 < ‖n‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hN)
      have hbq : b * (2 * q - b) = 0 := by
        rcases mul_eq_zero.mp hN0 with h | h
        · exact h
        · exact absurd h (ne_of_gt hNpos)
      have hb0 : b = 0 := by
        by_cases hq : q = 0
        · rw [hb_eq, hq]; ring
        · have hprod : (1 - t) * (1 + t) * q ^ 2 = 0 := by
            have hfac : ((1 - t) * q) * (2 * q - (1 - t) * q) = (1 - t) * (1 + t) * q ^ 2 := by
              ring
            rw [hb_eq] at hbq
            rw [hfac] at hbq
            exact hbq
          have h2 : (1 - t) = 0 := by
            have h12 : (1 - t) * (1 + t) = 0 :=
              (mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 2 hq)
            exact (mul_eq_zero.mp h12).resolve_right (by linarith)
          rw [hb_eq, h2]; ring
      rw [hzn, hb0, zero_smul]
  have hxx : x = x' := by
    have : x - x' = 0 := hz0
    exact sub_eq_zero.mp this
  have hv : v3 - v0 = v3' - v0 := by
    simpa [x, x'] using hxx
  have := congrArg (fun w : V3 => w + v0) hv
  simpa using this

/-- Continuity of `cross3` along continuous curves (kit for
`mk_planar2_continuous`; HOL `CONTINUOUS_CROSS` + the bilinear bound).
Private: no repo twin on this side. -/
private theorem continuousAt_cross3_p21 {f g : ℝ → V3} {a : ℝ}
    (hf : ContinuousAt f a) (hg : ContinuousAt g a) :
    ContinuousAt (fun t => cross3 (f t) (g t)) a := by
  have hb : ∀ t : ℝ, dist (cross3 (f t) (g t)) (cross3 (f a) (g a))
      ≤ ‖f t - f a‖ * ‖g t‖ + ‖f a‖ * ‖g t - g a‖ := by
    intro t
    have hid : cross3 (f t) (g t) - cross3 (f a) (g a)
        = cross3 (f t - f a) (g t) + cross3 (f a) (g t - g a) := by
      ext i
      fin_cases i <;> simp [cross3, crossProduct] <;> ring
    rw [dist_eq_norm, hid]
    refine le_trans (norm_add_le _ _) ?_
    exact add_le_add (NORM_CROSS_LE_p37 _ _) (NORM_CROSS_LE_p37 _ _)
  have h1 : Filter.Tendsto (fun t => ‖f t - f a‖) (nhds a) (nhds 0) := by
    have h : Filter.Tendsto (fun t => ‖f t - f a‖) (nhds a) (nhds (‖f a - f a‖)) :=
      (hf.sub continuousAt_const).norm.tendsto
    rwa [sub_self, norm_zero] at h
  have h2 : Filter.Tendsto (fun t => ‖g t - g a‖) (nhds a) (nhds 0) := by
    have h : Filter.Tendsto (fun t => ‖g t - g a‖) (nhds a) (nhds (‖g a - g a‖)) :=
      (hg.sub continuousAt_const).norm.tendsto
    rwa [sub_self, norm_zero] at h
  have hgcont : Filter.Tendsto (fun t => ‖g t‖) (nhds a) (nhds (‖g a‖)) := hg.norm.tendsto
  have hsum : Filter.Tendsto
      (fun t => ‖f t - f a‖ * ‖g t‖ + ‖f a‖ * ‖g t - g a‖) (nhds a) (nhds 0) := by
    have hA : Filter.Tendsto (fun t => ‖f t - f a‖ * ‖g t‖) (nhds a) (nhds 0) := by
      simpa using h1.mul hgcont
    have hB : Filter.Tendsto (fun t => ‖f a‖ * ‖g t - g a‖) (nhds a) (nhds 0) := by
      simpa using (tendsto_const_nhds (x := ‖f a‖)).mul h2
    simpa using hA.add hB
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun t => dist_nonneg) hb

/-- HOL `mk_planar2_continuous` (CUXVZOZ.hl:974): `mk_planar2` is
real-continuous in all parameters (s fixed). -/
theorem mk_planar2_continuous_p21 (v0 v1 v2 : ℝ → V3) (x1 x2 x3 x5 x6 : ℝ → ℝ) (a s : ℝ)
    (hx1 : 0 < x1 a) (hu1 : 0 < upsX (x1 a) (x2 a) (x6 a))
    (hu2 : 0 < upsX (x1 a) (x3 a) (x5 a))
    (hv0 : ContinuousAt v0 a) (hv1 : ContinuousAt v1 a) (hv2 : ContinuousAt v2 a)
    (hc1 : ContinuousAt x1 a) (hc2 : ContinuousAt x2 a) (hc3 : ContinuousAt x3 a)
    (hc5 : ContinuousAt x5 a) (hc6 : ContinuousAt x6 a) :
    ContinuousAt (fun t => mkPlanar2 (v0 t) (v1 t) (v2 t) (x1 t) (x2 t) (x3 t) (x5 t) (x6 t) s)
      a := by
  have _hu2 := hu2
  have hx1ne : x1 a ≠ 0 := ne_of_gt hx1
  have hu1ne : upsX (x1 a) (x2 a) (x6 a) ≠ 0 := ne_of_gt hu1
  have h2x1 : (2 : ℝ) * x1 a ≠ 0 := by positivity
  have hcoef : ContinuousAt (fun t => (x1 t + x3 t - x5 t) / (2 * x1 t)) a := by
    refine ContinuousAt.div ?_ ?_ h2x1
    · fun_prop
    · fun_prop
  have hN : ContinuousAt (fun t => upsX (x1 t) (x3 t) (x5 t)) a := by
    simp only [upsX]; fun_prop
  have hD : ContinuousAt (fun t => upsX (x1 t) (x2 t) (x6 t)) a := by
    simp only [upsX]; fun_prop
  have hratio : ContinuousAt
      (fun t => upsX (x1 t) (x3 t) (x5 t) / upsX (x1 t) (x2 t) (x6 t)) a :=
    hN.div hD hu1ne
  have hcoef2 : ContinuousAt
      (fun t => (s / x1 t) * Real.sqrt (upsX (x1 t) (x3 t) (x5 t) / upsX (x1 t) (x2 t) (x6 t))) a :=
    (continuousAt_const.div hc1 hx1ne).mul hratio.sqrt
  have hcross : ContinuousAt
      (fun t => cross3 (v1 t - v0 t) (cross3 (v1 t - v0 t) (v2 t - v0 t))) a :=
    continuousAt_cross3_p21 (hv1.sub hv0)
      (continuousAt_cross3_p21 (hv1.sub hv0) (hv2.sub hv0))
  simp only [mkPlanar2]
  exact (hv0.add (hcoef.smul (hv1.sub hv0))).add (hcoef2.smul hcross)


/-- HOL `collinear_expand` (CUXVZOZ.hl:1004): a vector coplanar with the
plane spanned off the origin expands over the two non-collinear vectors. -/
theorem collinear_expand_p21 (v1 v2 v3 : V3)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hc : Coplanar ({0, v1, v2, v3} : Set V3)) :
    ∃ t1 t2 : ℝ, v3 = t1 • v1 + t2 • v2 := by
  obtain ⟨u, v, w, hsub⟩ := hc
  have h0 : (0 : V3) ∈ affineSpan ℝ ({u, v, w} : Set V3) := hsub (by simp)
  have h1 : v1 ∈ affineSpan ℝ ({u, v, w} : Set V3) := hsub (by simp)
  have h2 : v2 ∈ affineSpan ℝ ({u, v, w} : Set V3) := hsub (by simp)
  have h3 : v3 ∈ affineSpan ℝ ({u, v, w} : Set V3) := hsub (by simp)
  have hv1S : v1 ∈ vectorSpan ℝ ({u, v, w} : Set V3) := by
    have hm : v1 -ᵥ (0 : V3) ∈ vectorSpan ℝ ({u, v, w} : Set V3) := by
      have hd : v1 -ᵥ (0 : V3) ∈ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
        vsub_mem_vectorSpan (k := ℝ) (p₁ := v1) (p₂ := (0 : V3)) h1 h0
      rwa [direction_affineSpan] at hd
    simpa using hm
  have hv2S : v2 ∈ vectorSpan ℝ ({u, v, w} : Set V3) := by
    have hm : v2 -ᵥ (0 : V3) ∈ vectorSpan ℝ ({u, v, w} : Set V3) := by
      have hd : v2 -ᵥ (0 : V3) ∈ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
        vsub_mem_vectorSpan (k := ℝ) (p₁ := v2) (p₂ := (0 : V3)) h2 h0
      rwa [direction_affineSpan] at hd
    simpa using hm
  have hv3S : v3 ∈ vectorSpan ℝ ({u, v, w} : Set V3) := by
    have hm : v3 -ᵥ (0 : V3) ∈ vectorSpan ℝ ({u, v, w} : Set V3) := by
      have hd : v3 -ᵥ (0 : V3) ∈ (affineSpan ℝ ({u, v, w} : Set V3)).direction :=
        vsub_mem_vectorSpan (k := ℝ) (p₁ := v3) (p₂ := (0 : V3)) h3 h0
      rwa [direction_affineSpan] at hd
    simpa using hm
  have hle : Submodule.span ℝ ({v1, v2} : Set V3) ≤ vectorSpan ℝ ({u, v, w} : Set V3) := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hv1S
    · exact hv2S
  have hS2 : Module.finrank ℝ (vectorSpan ℝ ({u, v, w} : Set V3)) ≤ 2 := by
    rw [vectorSpan_eq_span_vsub_set_right (k := ℝ) (p := u) (by simp)]
    rw [g482_image_vsub3 u v w]
    rw [g482_span_zero_insert (v -ᵥ u) (w -ᵥ u)]
    exact g482_finrank_pair_le (v -ᵥ u) (w -ᵥ u)
  have hvec0 : vectorSpan ℝ ({0, v1, v2} : Set V3) = Submodule.span ℝ ({v1, v2} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right (k := ℝ) (p := (0 : V3)) (by simp)]
    rw [show ((fun x : V3 => x -ᵥ (0 : V3)) '' ({0, v1, v2} : Set V3))
        = ({0, v1, v2} : Set V3) from by
      rw [g482_image_vsub3 (0 : V3) v1 v2]
      simp]
    rw [g482_span_zero_insert v1 v2]
  have hpair_ge : 2 ≤ Module.finrank ℝ (Submodule.span ℝ ({v1, v2} : Set V3)) := by
    have h := collinear_iff_finrank_le_one (k := ℝ) (s := ({0, v1, v2} : Set V3))
    have h' : ¬ Module.finrank ℝ (vectorSpan ℝ ({0, v1, v2} : Set V3)) ≤ 1 := by
      intro hle1
      exact hnc (h.mpr hle1)
    rw [hvec0] at h'
    omega
  have hpair_dim : Module.finrank ℝ (Submodule.span ℝ ({v1, v2} : Set V3)) = 2 :=
    le_antisymm (g482_finrank_pair_le v1 v2) hpair_ge
  have hSdim : Module.finrank ℝ (vectorSpan ℝ ({u, v, w} : Set V3)) = 2 := by
    have hmono : Module.finrank ℝ (Submodule.span ℝ ({v1, v2} : Set V3))
        ≤ Module.finrank ℝ (vectorSpan ℝ ({u, v, w} : Set V3)) := Submodule.finrank_mono hle
    omega
  have hEq : Submodule.span ℝ ({v1, v2} : Set V3) = vectorSpan ℝ ({u, v, w} : Set V3) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hpair_dim, hSdim])
  have hv3' : v3 ∈ Submodule.span ℝ ({v1, v2} : Set V3) := by
    rw [← hEq] at hv3S
    exact hv3S
  obtain ⟨t1, t2, ht⟩ := Submodule.mem_span_pair.mp hv3'
  exact ⟨t1, t2, ht.symm⟩

/-- HOL let `f1` (CUXVZOZ.hl:1417): the `mk_simplex1` deformation moving
`v2` within the 684 face with both edges prescribed. -/
private noncomputable def planarF1_p21 (v0 v2 v3 : V3) (g02 g23 : ℝ → ℝ) :
    V3 → ℝ → V3 :=
  fun w t => if w = v2 then
    mkSimplex1 0 v3 v0 (‖v3‖ ^ 2) (‖v0‖ ^ 2) (‖v2‖ ^ 2)
      ((dist v0 v2 + g02 t) ^ 2) ((dist v3 v2 + g23 t) ^ 2) (dist v0 v3 ^ 2)
  else w

/-- HOL let `f` (CUXVZOZ.hl:1421): the planar deformation moving `v2` by
`f1` and `v1` along the coplanar ray (`mk_planar2` with `s = -1`). -/
private noncomputable def planarF_p21 (v0 v1 v2 v3 : V3) (g01 g02 g23 : ℝ → ℝ) :
    V3 → ℝ → V3 :=
  fun w t => if w = v2 then planarF1_p21 v0 v2 v3 g02 g23 v2 t
    else if w = v1 then
      mkPlanar2 0 v0 (planarF1_p21 v0 v2 v3 g02 g23 v2 t)
        (‖v0‖ ^ 2) (‖v2‖ ^ 2) (‖v1‖ ^ 2)
        ((dist v0 v1 + g01 t) ^ 2) ((dist v0 v2 + g02 t) ^ 2) (-1)
    else w

/-- HOL let `f` (CUXVZOZ.hl:1419): the planar deformation second version —
`mk_planar2` reading the `(f1 v2 t, v0)` slots. -/
private noncomputable def planar2F_p21 (v0 v1 v2 v3 : V3) (g12 g02 g23 : ℝ → ℝ) :
    V3 → ℝ → V3 :=
  fun w t => if w = v2 then planarF1_p21 v0 v2 v3 g02 g23 v2 t
    else if w = v1 then
      mkPlanar2 0 (planarF1_p21 v0 v2 v3 g02 g23 v2 t) v0
        (‖v2‖ ^ 2) (‖v0‖ ^ 2) (‖v1‖ ^ 2)
        ((dist v1 v2 + g12 t) ^ 2) ((dist v0 v2 + g02 t) ^ 2) (-1)
    else w

/-- HOL `deform_planar` (CUXVZOZ.hl:1030): the planar two-vertex
deformation (edge-12 version). -/
theorem deform_planar_p21 (V : Set V3) (g01 g02 g23 : ℝ → ℝ) (v0 v1 v2 v3 : V3) (e : ℝ)
    (h1 : ¬ Coplanar ({0, v0, v2, v3} : Set V3))
    (h2 : Coplanar ({0, v0, v1, v2} : Set V3))
    (hc1 : v2 ⬝ᵥ cross3 v3 v0 > 0) (hc2 : cross3 v1 v0 ⬝ᵥ cross3 v2 v0 > 0)
    (hne : v1 ≠ v2) (he : 0 < e)
    (h23 : ContinuousOn g23 (Ioo (-e) e)) (h23z : g23 0 = 0)
    (h01 : ContinuousOn g01 (Ioo (-e) e)) (h01z : g01 0 = 0)
    (h02 : ContinuousOn g02 (Ioo (-e) e)) (h02z : g02 0 = 0) :
    ∃ e', 0 < e' ∧ Deformation (planarF_p21 v0 v1 v2 v3 g01 g02 g23) V (-e') e' ∧
      (∀ v t, v ≠ v1 ∧ v ≠ v2 → planarF_p21 v0 v1 v2 v3 g01 g02 g23 v t = v) ∧
      (∀ t, |t| < e' →
        Coplanar ({0, v0, planarF_p21 v0 v1 v2 v3 g01 g02 g23 v1 t,
          planarF_p21 v0 v1 v2 v3 g01 g02 g23 v2 t} : Set V3) ∧
        dist v0 (planarF_p21 v0 v1 v2 v3 g01 g02 g23 v1 t) = dist v0 v1 + g01 t ∧
        ‖planarF_p21 v0 v1 v2 v3 g01 g02 g23 v1 t‖ = ‖v1‖ ∧
        dist (planarF_p21 v0 v1 v2 v3 g01 g02 g23 v2 t) v0 = dist v2 v0 + g02 t ∧
        dist (planarF_p21 v0 v1 v2 v3 g01 g02 g23 v2 t) v3 = dist v2 v3 + g23 t ∧
        ‖planarF_p21 v0 v1 v2 v3 g01 g02 g23 v2 t‖ = ‖v2‖) := by
  -- DISCHARGES: HOL `deform_planar` (340 lines): the 684 decrease stacked
  -- with the `mk_planar2` coplanar decrease (skip4 slot), continuity and
  -- non-coplanarity management. NEEDS: same kit as the edge23 giant plus
  -- `mk_planar_unique`.
  sorry

/-- HOL `deform_planar_exists` (CUXVZOZ.hl:1374): existential-witness form
of the preceding theorem. -/
theorem deform_planar_exists_p21 (V : Set V3) (g01 g02 g23 : ℝ → ℝ) (v0 v1 v2 v3 : V3) (e : ℝ) :
    ∃ f : V3 → ℝ → V3,
      (¬ Coplanar ({0, v0, v2, v3} : Set V3) → Coplanar ({0, v0, v1, v2} : Set V3) →
        v2 ⬝ᵥ cross3 v3 v0 > 0 → cross3 v1 v0 ⬝ᵥ cross3 v2 v0 > 0 → v1 ≠ v2 → 0 < e →
        ContinuousOn g23 (Ioo (-e) e) → g23 0 = 0 →
        ContinuousOn g01 (Ioo (-e) e) → g01 0 = 0 →
        ContinuousOn g02 (Ioo (-e) e) → g02 0 = 0 →
        ∃ e', 0 < e' ∧ Deformation f V (-e') e' ∧
          (∀ v t, v ≠ v1 ∧ v ≠ v2 → f v t = v) ∧
          (∀ t, |t| < e' → Coplanar ({0, v0, f v1 t, f v2 t} : Set V3) ∧
            dist v0 (f v1 t) = dist v0 v1 + g01 t ∧ ‖f v1 t‖ = ‖v1‖ ∧
            dist (f v2 t) v0 = dist v2 v0 + g02 t ∧
            dist (f v2 t) v3 = dist v2 v3 + g23 t ∧ ‖f v2 t‖ = ‖v2‖)) :=
  ⟨planarF_p21 v0 v1 v2 v3 g01 g02 g23, fun h1 h2 hc1 hc2 hne he h23 h23z h01 h01z h02 h02z =>
    deform_planar_p21 V g01 g02 g23 v0 v1 v2 v3 e h1 h2 hc1 hc2 hne he h23 h23z h01 h01z
      h02 h02z⟩

/-- HOL `deform_planar_second_version` (CUXVZOZ.hl:1413): the planar
two-vertex deformation (edge-23-second version, `v0` fixed slot). -/
theorem deform_planar_second_version_p21 (V : Set V3) (g12 g02 g23 : ℝ → ℝ)
    (v0 v1 v2 v3 : V3) (e : ℝ)
    (h1 : ¬ Coplanar ({0, v0, v2, v3} : Set V3))
    (h2 : Coplanar ({0, v0, v1, v2} : Set V3))
    (hc1 : v2 ⬝ᵥ cross3 v3 v0 > 0) (hc2 : cross3 v1 v2 ⬝ᵥ cross3 v0 v2 > 0)
    (hne : v1 ≠ v0) (he : 0 < e)
    (h23 : ContinuousOn g23 (Ioo (-e) e)) (h23z : g23 0 = 0)
    (h12 : ContinuousOn g12 (Ioo (-e) e)) (h12z : g12 0 = 0)
    (h02 : ContinuousOn g02 (Ioo (-e) e)) (h02z : g02 0 = 0) :
    ∃ e', 0 < e' ∧ Deformation (planar2F_p21 v0 v1 v2 v3 g12 g02 g23) V (-e') e' ∧
      (∀ v t, v ≠ v1 ∧ v ≠ v2 → planar2F_p21 v0 v1 v2 v3 g12 g02 g23 v t = v) ∧
      (∀ t, |t| < e' →
        Coplanar ({0, v0, planar2F_p21 v0 v1 v2 v3 g12 g02 g23 v1 t,
          planar2F_p21 v0 v1 v2 v3 g12 g02 g23 v2 t} : Set V3) ∧
        dist (planar2F_p21 v0 v1 v2 v3 g12 g02 g23 v1 t)
          (planar2F_p21 v0 v1 v2 v3 g12 g02 g23 v2 t) = dist v1 v2 + g12 t ∧
        ‖planar2F_p21 v0 v1 v2 v3 g12 g02 g23 v1 t‖ = ‖v1‖ ∧
        dist (planar2F_p21 v0 v1 v2 v3 g12 g02 g23 v2 t) v0 = dist v2 v0 + g02 t ∧
        dist (planar2F_p21 v0 v1 v2 v3 g12 g02 g23 v2 t) v3 = dist v2 v3 + g23 t ∧
        ‖planar2F_p21 v0 v1 v2 v3 g12 g02 g23 v2 t‖ = ‖v2‖) := by
  -- DISCHARGES: HOL `deform_planar_second_version` (350 lines): the mirror
  -- of `deform_planar` with `mk_planar2` reading the (v2,v0) slots.
  -- NEEDS: same kit as the edge23 giant plus `mk_planar_unique`.
  sorry

/-- HOL `deform_planar_exists_second_version` (CUXVZOZ.hl:1762):
existential-witness form of the preceding theorem. -/
theorem deform_planar_exists_second_version_p21 (V : Set V3) (g12 g02 g23 : ℝ → ℝ)
    (v0 v1 v2 v3 : V3) (e : ℝ) :
    ∃ f : V3 → ℝ → V3,
      (¬ Coplanar ({0, v0, v2, v3} : Set V3) → Coplanar ({0, v0, v1, v2} : Set V3) →
        v2 ⬝ᵥ cross3 v3 v0 > 0 → cross3 v1 v2 ⬝ᵥ cross3 v0 v2 > 0 → v1 ≠ v0 → 0 < e →
        ContinuousOn g23 (Ioo (-e) e) → g23 0 = 0 →
        ContinuousOn g12 (Ioo (-e) e) → g12 0 = 0 →
        ContinuousOn g02 (Ioo (-e) e) → g02 0 = 0 →
        ∃ e', 0 < e' ∧ Deformation f V (-e') e' ∧
          (∀ v t, v ≠ v1 ∧ v ≠ v2 → f v t = v) ∧
          (∀ t, |t| < e' → Coplanar ({0, v0, f v1 t, f v2 t} : Set V3) ∧
            dist (f v1 t) (f v2 t) = dist v1 v2 + g12 t ∧ ‖f v1 t‖ = ‖v1‖ ∧
            dist (f v2 t) v0 = dist v2 v0 + g02 t ∧
            dist (f v2 t) v3 = dist v2 v3 + g23 t ∧ ‖f v2 t‖ = ‖v2‖)) := by
  refine ⟨planar2F_p21 v0 v1 v2 v3 g12 g02 g23, fun h1 h2 hc1 hc2 hne he h23 h23z h12 h12z
    h02 h02z => ?_⟩
  have h := deform_planar_second_version_p21 V g12 g02 g23 v0 v1 v2 v3 e h1 h2 hc1 hc2 hne he
    h23 h23z h12 h12z h02 h02z
  exact h

/-- HOL `deformation_restrict` (CUXVZOZ.hl:3529): shrink the deformation
window. -/
theorem deformation_restrict_p21 (e : ℝ) (f : V3 → ℝ → V3) (V : Set V3) (e' : ℝ)
    (h : Deformation f V (-e) e) (he : 0 < e') (hs : ∀ t, |t| < e' → |t| < e) :
    Deformation f V (-e') e' := by
  obtain ⟨h0, hc, hfix⟩ := h
  have he0 : 0 ≤ e := le_of_lt h0.2
  have hee : e' ≤ e := by
    rcases lt_or_ge e e' with hlt | hge
    · have htp : 0 < (e + e') / 2 := by linarith
      have ht : |(e + e') / 2| = (e + e') / 2 := abs_of_pos htp
      have h1 := hs ((e + e') / 2) (by rw [ht]; linarith)
      rw [ht] at h1
      linarith
    · exact hge
  refine ⟨⟨by linarith, by linarith⟩, ?_, hfix⟩
  intro v hv r hr
  exact hc v hv r ⟨by linarith [hr.1, hee], by linarith [hr.2, hee]⟩

/-! ## Section D: periodic/mod kit -/

/-- Shift a `k`-periodic family back to the `mod k` residue; the
`Oxl_def.periodic_mod` workhorse of the reductions. -/
private theorem periodic_mod_p21 {α : Sort u} {f : ℕ → α} {k : ℕ} (_hk : k ≠ 0)
    (hper : ∀ i, f (i + k) = f i) (i : ℕ) : f (i % k) = f i := by
  have shiftq : ∀ q r : ℕ, f (r + k * q) = f r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
        intro r
        have h1 : r + k * (q + 1) = r + k * q + k := by
          rw [Nat.mul_succ, Nat.add_assoc]
        rw [h1, hper, ih]
  have hii : i = i % k + k * (i / k) := (Nat.mod_add_div i k).symm
  conv_rhs => rw [hii]
  exact (shiftq _ _).symm

/-- HOL `SKOLEM_PERIODIC` (CUXVZOZ.hl:1802): a downward-monotone periodic
family with pointwise ε has a uniform ε. -/
theorem SKOLEM_PERIODIC_p21 {P : ℕ → ℝ → Prop} (k : ℕ) (hper : Periodic P k)
    (hk : k ≠ 0) (hmono : ∀ i e e', e ≤ e' → P i e' → P i e) :
    ((∀ i, ∃ e, 0 < e ∧ P i e) ↔ ∃ e, 0 < e ∧ ∀ i, P i e) := by
  constructor
  · intro h
    have key : ∀ e i, P (i % k) e → P i e := by
      intro e i hh
      have hi : P (i % k) e = P i e :=
        congrFun (periodic_mod_p21 (f := fun j => P j) hk hper i) e
      rw [← hi]
      exact hh
    have hfin : ∀ i : Fin k, ∃ e, 0 < e ∧ P i e := fun i => h i
    choose g hg1 hg2 using hfin
    have hne : ((Finset.univ : Finset (Fin k))).Nonempty :=
      ⟨⟨0, Nat.pos_of_ne_zero hk⟩, Finset.mem_univ _⟩
    refine ⟨-Finset.univ.sup' hne (fun x => -g x), ?_, ?_⟩
    · have hS : Finset.univ.sup' hne (fun x => -g x) < 0 := by
        rw [Finset.sup'_lt_iff]
        intro x _
        have hgx := hg1 x
        linarith
      exact neg_pos.mpr hS
    · intro i
      have hi : i % k < k := Nat.mod_lt i (Nat.pos_of_ne_zero hk)
      have hle : -Finset.univ.sup' hne (fun x => -g x) ≤ g ⟨i % k, hi⟩ := by
        have h1 := Finset.le_sup' (f := fun x : Fin k => -g x) (b := (⟨i % k, hi⟩ : Fin k))
          (Finset.mem_univ _)
        linarith
      exact key _ i (hmono _ _ _ hle (hg2 ⟨i % k, hi⟩))
  · rintro ⟨e, he, hall⟩ i
    exact ⟨e, he, hall i⟩

/-- HOL `SKOLEM_PERIODIC2` (CUXVZOZ.hl:1834): two-parameter version. -/
theorem SKOLEM_PERIODIC2_p21 {P : ℕ → ℕ → ℝ → Prop} (k : ℕ) (hper : Periodic2 P k)
    (hk : k ≠ 0) (hmono : ∀ i j e e', e ≤ e' → P i j e' → P i j e) :
    ((∀ i j, ∃ e, 0 < e ∧ P i j e) ↔ ∃ e, 0 < e ∧ ∀ i j, P i j e) := by
  constructor
  · intro h
    have key : ∀ e i j, P (i % k) (j % k) e → P i j e := by
      intro e i j hh
      have hj : P i (j % k) e = P i j e :=
        congrFun (periodic_mod_p21 (f := fun m => P i m) hk (fun m => (hper i m).2) j) e
      have hix : P (i % k) (j % k) e = P i (j % k) e :=
        congrFun (periodic_mod_p21 (f := fun m => P m (j % k)) hk
          (fun m => (hper m (j % k)).1) i) e
      rw [← hj, ← hix]
      exact hh
    have hfin : ∀ p : Fin k × Fin k, ∃ e, 0 < e ∧ P p.1 p.2 e := fun p => h p.1 p.2
    choose g hg1 hg2 using hfin
    have hne : ((Finset.univ : Finset (Fin k × Fin k))).Nonempty :=
      ⟨(⟨0, Nat.pos_of_ne_zero hk⟩, ⟨0, Nat.pos_of_ne_zero hk⟩), Finset.mem_univ _⟩
    refine ⟨-Finset.univ.sup' hne (fun p => -g p), ?_, ?_⟩
    · have hS : Finset.univ.sup' hne (fun p => -g p) < 0 := by
        rw [Finset.sup'_lt_iff]
        intro p _
        have hgp := hg1 p
        linarith
      exact neg_pos.mpr hS
    · intro i j
      have hi : i % k < k := Nat.mod_lt i (Nat.pos_of_ne_zero hk)
      have hj : j % k < k := Nat.mod_lt j (Nat.pos_of_ne_zero hk)
      have hle : -Finset.univ.sup' hne (fun p => -g p) ≤ g (⟨i % k, hi⟩, ⟨j % k, hj⟩) := by
        have h1 := Finset.le_sup' (f := fun p : Fin k × Fin k => -g p)
          (b := (⟨i % k, hi⟩, ⟨j % k, hj⟩)) (Finset.mem_univ _)
        linarith
      exact key _ i j (hmono _ _ _ _ hle (hg2 (⟨i % k, hi⟩, ⟨j % k, hj⟩)))
  · rintro ⟨e, he, hall⟩ i j
    exact ⟨e, he, hall i j⟩

/-- HOL `scs_k_bounds` (CUXVZOZ.hl:1875). -/
theorem scs_k_bounds_p21 (s : ScsV39) (h : isScsV39 s) : 3 ≤ s.k ∧ s.k ≤ 6 :=
  ⟨h.2.1, h.2.2.1⟩

/-- HOL `periodic2_MOD` (CUXVZOZ.hl:2340). -/
theorem periodic2_MOD_p21 {α : Sort u} {a : ℕ → ℕ → α} {i j k : ℕ} (hk : k ≠ 0)
    (hper : Periodic2 a k) : a i j = a (i % k) (j % k) := by
  have step1 : a i j = a i (j % k) :=
    (periodic_mod_p21 (f := fun m => a i m) hk (fun m => (hper i m).2) j).symm
  have step2 : a i (j % k) = a (i % k) (j % k) :=
    (periodic_mod_p21 (f := fun m => a m (j % k)) hk
      (fun m => (hper m (j % k)).1) i).symm
  exact step1.trans step2

/-- HOL `MOD_periodic2` (CUXVZOZ.hl:2359). -/
theorem MOD_periodic2_p21 {α : Sort u} {a : ℕ → ℕ → α} {k : ℕ} (_hk : k ≠ 0)
    (h : ∀ i j, a i j = a (i % k) (j % k)) : Periodic2 a k := by
  intro i j
  refine ⟨?_, ?_⟩
  · rw [h (i + k) j, h i j, Nat.add_mod_right]
  · rw [h i (j + k), h i j, Nat.add_mod_right]

/-- HOL `azim_dominated_split` (CUXVZOZ.hl:2371): a split azimuth identity
transports under two dominated azimuths on non-collinear triples. -/
theorem azim_dominated_split_p21 (v0 v1 v2 v3 v4 v0' v1' v2' v3' v4' : V3)
    (h1 : ¬ Collinear ℝ ({v0', v1', v3'} : Set V3))
    (h2 : ¬ Collinear ℝ ({v0', v1', v4'} : Set V3))
    (h3 : ¬ Collinear ℝ ({v0', v1', v2'} : Set V3))
    (hsplit : azim v0 v1 v2 v3 + azim v0 v1 v3 v4 = azim v0 v1 v2 v4)
    (hd1 : azim v0' v1' v2' v3' ≤ azim v0 v1 v2 v3)
    (hd2 : azim v0' v1' v3' v4' ≤ azim v0 v1 v3 v4) :
    azim v0' v1' v2' v3' + azim v0' v1' v3' v4' = azim v0' v1' v2' v4' := by
  have hxv : v1' ≠ v0' := by
    intro he
    apply h1
    have hset : ({v0', v1', v3'} : Set V3) = {v0', v3'} := by
      rw [he]
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact collinear_pair ℝ v0' v3'
  have hlt : azim v0' v1' v2' v3' + azim v0' v1' v3' v4' < 2 * Real.pi := by
    have hle : azim v0' v1' v2' v3' + azim v0' v1' v3' v4' ≤ azim v0 v1 v2 v4 := by
      rw [← hsplit]
      exact add_le_add hd1 hd2
    exact lt_of_le_of_lt hle (azim_lt_two_pi v0 v1 v2 v4)
  exact (sum3_azim_fan hxv h3 h1 h2 hlt).symm

/-- HOL `MOD_SHIFT` (CUXVZOZ.hl:2674). -/
theorem MOD_SHIFT_p21 (k a b c : ℕ) (_hk : k ≠ 0) (h : a % k = b % k) :
    (a + c) % k = (b + c) % k := by
  calc (a + c) % k = (a % k + c % k) % k := Nat.add_mod a c k
    _ = (b % k + c % k) % k := by rw [h]
    _ = (b + c) % k := (Nat.add_mod b c k).symm

/-- HOL `I_IMP` (CUXVZOZ.hl:2399). -/
theorem I_IMP_p21 (x : Prop) (h : id x) : x := h

/-- HOL `psort_inj` (CUXVZOZ.hl:2407). -/
theorem psort_inj_p21 (k a b c d : ℕ) (h : psort k (a, b) = psort k (c, d)) :
    a % k = c % k ∨ a % k = d % k := by
  simp only [psort] at h
  split_ifs at h
  · simp only [Prod.mk.injEq] at h
    exact Or.inl h.1
  · simp only [Prod.mk.injEq] at h
    exact Or.inr h.1
  · simp only [Prod.mk.injEq] at h
    exact Or.inr h.2
  · simp only [Prod.mk.injEq] at h
    exact Or.inl h.2

/-- HOL `psort_mod` (CUXVZOZ.hl:3539). -/
theorem psort_mod_p21 (k a b : ℕ) (_hk : k ≠ 0) :
    psort k (a % k, b % k) = psort k (a, b) := by
  simp only [psort]
  rw [Nat.mod_mod_of_dvd a (dvd_refl k), Nat.mod_mod_of_dvd b (dvd_refl k)]

/-- HOL `solve_mod_k` (CUXVZOZ.hl:3589). -/
theorem solve_mod_k_p21 (k a b x : ℕ) (hk : k ≠ 0) (h : b = (x + a) % k) :
    x % k = (b + k - a % k) % k := by
  rw [h, Nat.add_mod]
  have hr : x % k < k := Nat.mod_lt x (Nat.pos_of_ne_zero hk)
  have hs : a % k < k := Nat.mod_lt a (Nat.pos_of_ne_zero hk)
  rcases Nat.lt_or_ge (x % k + a % k) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
    have h1 : x % k + a % k + k - a % k = x % k + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_mod_of_dvd x (dvd_refl k)]
  · have h2 : x % k + a % k < 2 * k := by omega
    have hb : (x % k + a % k) % k = x % k + a % k - k := by
      conv_lhs => rw [show x % k + a % k = x % k + a % k - k + k from by omega]
      rw [Nat.add_mod_right]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hb]
    have h3 : x % k + a % k - k + k - a % k = x % k := by omega
    rw [h3, Nat.mod_eq_of_lt hr]

/-- HOL `sin_azim_pos` (CUXVZOZ.hl:3107). -/
theorem sin_azim_pos_p21 (v1 v2 v3 v4 : V3) :
    0 < Real.sin (azim v1 v2 v3 v4) ↔
      (0 < azim v1 v2 v3 v4 ∧ azim v1 v2 v3 v4 < Real.pi) := by
  have hnn : 0 ≤ azim v1 v2 v3 v4 := azim_nonneg v1 v2 v3 v4
  have h2π : azim v1 v2 v3 v4 < 2 * Real.pi := azim_lt_two_pi v1 v2 v3 v4
  constructor
  · intro h
    rcases lt_or_ge (azim v1 v2 v3 v4) Real.pi with hlt | hge
    · refine ⟨?_, hlt⟩
      by_contra hnonpos
      have h0 : azim v1 v2 v3 v4 = 0 := le_antisymm (not_lt.mp hnonpos) hnn
      rw [h0] at h
      simp at h
    · exfalso
      have hpos : 0 ≤ azim v1 v2 v3 v4 - Real.pi := by linarith
      have hle : azim v1 v2 v3 v4 - Real.pi ≤ Real.pi := by linarith
      have hsn : 0 ≤ Real.sin (azim v1 v2 v3 v4 - Real.pi) :=
        Real.sin_nonneg_of_nonneg_of_le_pi hpos hle
      have hsub : Real.sin (azim v1 v2 v3 v4 - Real.pi) = -Real.sin (azim v1 v2 v3 v4) := by
        rw [Real.sin_sub, Real.cos_pi, Real.sin_pi]
        ring
      rw [hsub] at hsn
      linarith
  · rintro ⟨h1, h2⟩
    exact Real.sin_pos_of_mem_Ioo ⟨h1, h2⟩

/-! ## W3 private kit -/

private theorem w3b_periodic_mod {α : Sort*} {f : ℕ → α} {k : ℕ} (hk : k ≠ 0)
    (hf : Periodic f k) (i : ℕ) : f (i % k) = f i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    if h : i < k then
      rw [Nat.mod_eq_of_lt h]
    else
      have hle : k ≤ i := le_of_not_gt h
      rw [Nat.mod_eq_sub_mod hle, ih (i - k) (by omega), ← hf (i - k)]
      congr 1
      omega

private theorem w3b_eps_fixed {α : Sort*} [Nonempty α] {pr : α → Prop} {a : α}
    (hpa : pr a) (huniq : ∀ y, pr y → y = a) : Classical.epsilon pr = a := by
  by_contra hne
  exact hne (huniq _ (Classical.epsilon_spec ⟨a, hpa⟩))

private theorem w3b_mod_ne_add {k a c : ℕ} (_hk0 : 0 < k) (hck : c < k) (hc0 : 0 < c) :
    a % k ≠ (a + c) % k := by
  intro h
  have hd : k ∣ a + c - a := Nat.modEq_iff_dvd' (by omega) |>.mp h
  rw [Nat.add_sub_cancel_left] at hd
  have hd2 : c % k = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  rw [Nat.mod_eq_of_lt hck] at hd2
  omega

private theorem w3b_hedge_of_localFan {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}
    (h : LocalFan V E FF) : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
  obtain ⟨hfan, x, hx, hFF, hD, h2reg⟩ := h
  intro v hv
  have h2 : (ee v E).ncard = 2 := h2reg v hv
  have hne : (ee v E).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty.mp hc, Set.ncard_empty] at h2
    omega
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hw⟩

private theorem w3b_distinct_succ_pred {vv : ℕ → V3} {k : ℕ} (hper : Periodic vv k)
    (hk3 : 3 ≤ k)
    (hinj : ∀ i j, i < k → j < k → vv i = vv j → i = j) (i : ℕ) :
    vv (i + 1) ≠ vv (i + (k - 1)) := by
  have hk0 : k ≠ 0 := by omega
  have hkpow : 0 < k := by omega
  intro h
  have h1 : vv ((i + 1) % k) = vv (i + 1) := w3b_periodic_mod hk0 hper (i + 1)
  have h2 : vv ((i + (k - 1)) % k) = vv (i + (k - 1)) :=
    w3b_periodic_mod hk0 hper (i + (k - 1))
  have hlt1 : (i + 1) % k < k := Nat.mod_lt _ hkpow
  have hlt2 : (i + (k - 1)) % k < k := Nat.mod_lt _ hkpow
  have hmod := hinj _ _ hlt1 hlt2 (by rw [h1, h2, h])
  have hc : i + (k - 1) = (i + 1) + (k - 2) := by omega
  rw [hc] at hmod
  exact absurd hmod (w3b_mod_ne_add hkpow (by omega) (by omega))

/-- `sigma_fan 0 univ E (vv i) (vv (i+1)) = vv (i+k-1)`: the neighbour set is
the two-point `ee` set (`EE_vv`), and the epsilon witness is forced. -/
private theorem w3b_sigmaFan_eq_vv (vv : ℕ → V3) (k i : ℕ) (hper : Periodic vv k)
    (hk3 : 3 ≤ k)
    (hinj : ∀ i j, i < k → j < k → vv i = vv j → i = j) :
    Fan.sigmaFan 0 Set.univ (Set.range fun i => ({vv i, vv (i + 1)} : Set V3))
      (vv i) (vv (i + 1)) = vv (i + (k - 1)) := by
  have hEE := EE_vv vv k i hper hk3 (fun i j h => hinj i j h.1 h.2.1 h.2.2)
  have hne := w3b_distinct_succ_pred hper hk3 hinj i
  have hS : Fan.setOfEdge (vv i) Set.univ (Set.range fun i => ({vv i, vv (i + 1)} : Set V3))
      = ({vv (i + 1), vv (i + (k - 1))} : Set V3) := by
    rw [← hEE]
    ext w
    simp [Fan.setOfEdge, ee]
  have hnesing : Fan.setOfEdge (vv i) Set.univ
      (Set.range fun i => ({vv i, vv (i + 1)} : Set V3)) ≠ {vv (i + 1)} := by
    intro hc
    have hz : vv (i + (k - 1)) ∈ ({vv (i + 1)} : Set V3) := by
      rw [← hc, hS]
      exact Set.mem_insert_of_mem _ rfl
    exact hne (Set.mem_singleton_iff.mp hz).symm
  unfold Fan.sigmaFan
  rw [if_neg hnesing]
  refine w3b_eps_fixed ⟨?_, ?_, ?_⟩ ?_
  · rw [hS]
    exact Set.mem_insert_of_mem _ rfl
  · exact fun hc => hne hc.symm
  · intro w1 hw1 hw1u
    rw [hS] at hw1
    rcases Set.mem_insert_iff.mp hw1 with h1 | h1
    · exact absurd h1 hw1u
    · rw [Set.mem_singleton_iff.mp h1]
  · intro y hy
    rw [hS] at hy
    rcases Set.mem_insert_iff.mp hy.1 with hy1 | hy1
    · exact absurd hy1 hy.2.1
    · exact Set.mem_singleton_iff.mp hy1

/-! ## Section E: BBs / local-fan transport -/

/-- HOL `VV_SUC_EQ_IVS_RHO_NODE_PRIME` (CUXVZOZ.hl:18): `ivs_rho_node1` of
an scs realisation lands at the `k-1` successor. -/
theorem VV_SUC_EQ_IVS_RHO_NODE_PRIME_p21 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (s : ScsV39) (vv : ℕ → V3) (u : V3) (k p1 : ℕ)
    (hk : s.k = k) (hu : vv p1 = u) (hV : Set.range vv = V)
    (hE : Set.range (fun i => {vv i, vv (i + 1)}) = E)
    (hFF : Set.range (fun i => (vv i, vv (i + 1))) = FF)
    (hs : isScsV39 s) (hk3 : ¬ (k ≤ 3)) (hBB : BBsV39 s vv) :
    ivsRhoNode1 FF u = vv (p1 + (k - 1)) := by
  have hconv : ConvexLocalFan V E FF := by
    rcases hBB.2.2.2 with h3 | hcf
    · exact absurd (by rw [hk] at h3; exact h3) hk3
    · rw [hV, hE, hFF] at hcf
      exact hcf
  have hLF := hconv.1
  have hedge := w3b_hedge_of_localFan hLF
  have hlf2 := localFan_p2.of_LocalFan_noIso hLF hedge
  have huV : u ∈ V := by
    rw [← hV, ← hu]
    exact Set.mem_range_self p1
  have hivsV : ivsRhoNode1 FF u ∈ V := LOCAL_FAN_IVS_IN_V hlf2 huV
  have hpairV : vv (p1 + (k - 1)) ∈ V := by
    rw [← hV]
    exact Set.mem_range_self _
  have hkey : rhoNode1 FF (ivsRhoNode1 FF u) = rhoNode1 FF (vv (p1 + (k - 1))) := by
    have hivsrho : rhoNode1 FF (ivsRhoNode1 FF u) = u := LOCAL_FAN_RHO_NODE_IVS hlf2 huV
    rw [hivsrho]
    have hp35 := VV_SUC_EQ_RHO_NODE_PRIME_p35 s k (p1 + (k - 1)) (p1 + (k - 1)) 0
      (vv (p1 + (k - 1))) V E FF vv hk rfl hV hE hFF hs hk3 hBB 1
    simp only [Function.iterate_one] at hp35
    have hstep : rhoNode1 FF (vv (p1 + (k - 1))) = vv (p1 + k) := by
      rw [hp35]
      congr 1
      omega
    have hper : Periodic vv k := hk ▸ hBB.2.1
    rw [hstep, hper p1]
    exact hu.symm
  exact (RHO_NODE1_INJECTIVE hLF hedge _ hivsV _ hpairV).mp hkey

/-- HOL `vv_azim_le_alt` (CUXVZOZ.hl:2056): the successor azimuth dominates
over the convex local fan. -/
theorem vv_azim_le_alt_p21 (vv : ℕ → V3) (k i j : ℕ) (hper : Periodic vv k)
    (hk3 : 3 ≤ k)
    (hcf : ConvexLocalFan (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ i j, i < k → j < k → vv i = vv j → i = j) :
    azim 0 (vv i) (vv (i + 1)) (vv j) ≤ azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
  have hshift : i + k - 1 = i + (k - 1) := by omega
  rw [hshift]
  have hinj' : ∀ i j, i < k ∧ j < k ∧ vv i = vv j → i = j :=
    fun i j h => hinj i j h.1 h.2.1 h.2.2
  have hEE := EE_vv vv k i hper hk3 hinj'
  have hmem : vv j ∈ wedgeInFanGe ((vv i, vv (i + 1)))
      (Set.range fun i => ({vv i, vv (i + 1)} : Set V3)) :=
    (hcf.2 (vv i, vv (i + 1)) ⟨i, rfl⟩).2 (Set.mem_range_self j)
  have hcard : 1 < (ee (vv i) (Set.range fun i => ({vv i, vv (i + 1)} : Set V3))).ncard := by
    rw [hEE, Set.ncard_pair (w3b_distinct_succ_pred hper hk3 hinj i)]
    norm_num
  simp only [wedgeInFanGe, if_pos hcard] at hmem
  simp only [wedgeGe, Set.mem_setOf_eq] at hmem
  rw [w3b_sigmaFan_eq_vv vv k i hper hk3 hinj] at hmem
  exact hmem.2

/-- HOL `vv_split_azim_alt` (CUXVZOZ.hl:2091): the azimuth to the `k-1`
predecessor splits over an interior vertex. -/
theorem vv_split_azim_alt_p21 (vv : ℕ → V3) (k i j : ℕ) (hper : Periodic vv k)
    (hk3 : 3 ≤ k)
    (h1 : ¬ Collinear ℝ ({0, vv i, vv j} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, vv i, vv (i + k - 1)} : Set V3))
    (h3 : ¬ Collinear ℝ ({0, vv i, vv (i + 1)} : Set V3))
    (hcf : ConvexLocalFan (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ i j, i < k → j < k → vv i = vv j → i = j) :
    azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) =
      azim 0 (vv i) (vv (i + 1)) (vv j) + azim 0 (vv i) (vv j) (vv (i + k - 1)) := by
  have hle := vv_azim_le_alt_p21 vv k i j hper hk3 hcf hinj
  have hxv : vv i ≠ 0 := by
    intro h0
    apply h3
    rw [h0]
    have hset : ({0, 0, vv (i + 1)} : Set V3) = {0, vv (i + 1)} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hset]
    exact collinear_pair ℝ 0 (vv (i + 1))
  exact sum4_azim_fan (x := 0) (v := vv i) (u := vv (i + 1)) (w1 := vv j)
    (w2 := vv (i + k - 1)) hxv h3 h1 h2 hle

/-- HOL `interior_angle1_azim` (CUXVZOZ.hl:2123). Here definitional:
`interiorAngle1 x FF v := azim x v (rhoNode1 FF v) (ivsRhoNode1 FF v)`. -/
theorem interior_angle1_azim_p21 (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3))
    (v : V3) (_h : LocalFan V E FF) (_hv : v ∈ V) :
    interiorAngle1 0 FF v = azim 0 v (rhoNode1 FF v) (ivsRhoNode1 FF v) := rfl

/-- HOL `LOFA_IMP_INANGLE_EQ_AZIM_IVS` (CUXVZOZ.hl:2140): verbatim duplicate
of `interior_angle1_azim` in the source (same statement, same proof). -/
theorem LOFA_IMP_INANGLE_EQ_AZIM_IVS_p21 (V : Set V3) (E : Set (Set V3))
    (FF : Set (V3 × V3)) (v : V3) (_h : LocalFan V E FF) (_hv : v ∈ V) :
    interiorAngle1 0 FF v = azim 0 v (rhoNode1 FF v) (ivsRhoNode1 FF v) := rfl

/-- HOL `BBs_inj` (CUXVZOZ.hl:2154): an scs realisation is injective below
`k` (the `a i j ≥ 2` lower bound off the diagonal). -/
theorem BBs_inj_p21 (s : ScsV39) (v : ℕ → V3) (k : ℕ) (hs : isScsV39 s) (hk : s.k = k)
    (hBB : BBsV39 s v) : ∀ i j, i < k → j < k → v i = v j → i = j := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdiag, _, _, _, _, _⟩ := hs
  obtain ⟨_, _, hdist, _⟩ := hBB
  intro i j hi hj hvv
  by_contra hne
  have hik : i < s.k := by rw [hk]; exact hi
  have hjk : j < s.k := by rw [hk]; exact hj
  have h2 : (2 : ℝ) ≤ s.a i j := hdiag i j ⟨hik, hjk, hne⟩
  have hle : s.a i j ≤ dist (v i) (v j) := (hdist i j).1
  rw [hvv, dist_self] at hle
  linarith

/-- HOL `IMAGE_FF` (CUXVZOZ.hl:2169): the two `IMAGE` spellings of the
deformed dart set coincide (HOL `FST`/`SND` vs pattern pair — both are the
same projection in Lean, so the equality is definitional). -/
theorem IMAGE_FF_p21 (FF : Set (V3 × V3)) (f : V3 → ℝ → V3) (t : ℝ) :
    (fun uv : V3 × V3 => (f uv.1 t, f uv.2 t)) '' FF =
      (fun p : V3 × V3 => (f p.1 t, f p.2 t)) '' FF := rfl

/-- HOL `interior_angle1_azim_scs` (CUXVZOZ.hl:2178): the interior angle of
the deformed fan stays the deformed azimuth near `0`. -/
theorem interior_angle1_azim_scs_p21 (s : ScsV39) (v : ℕ → V3) (k : ℕ)
    (f : V3 → ℝ → V3) (e : ℝ)
    (he : 0 < e) (hd : Deformation f (Set.range v) (-e) e) (hs : isScsV39 s)
    (hk : s.k = k) (hk3 : 3 < k) (hBB : BBsV39 s v) :
    ∃ e', 0 < e' ∧ ∀ t, |t| < e' →
      interiorAngle1 0
          (Set.image (fun p : V3 × V3 => (f p.1 t, f p.2 t))
            (Set.range fun i => (v i, v (i + 1)))) (f (v i) t) =
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) := by
  have hconv : ConvexLocalFan (Set.range v) (Set.range fun i => {v i, v (i + 1)})
      (Set.range fun i => (v i, v (i + 1))) := by
    rcases hBB.2.2.2 with h3 | hcf
    · exact absurd (by rw [hk] at h3; exact h3) (by omega : ¬ k ≤ 3)
    · exact hcf
  have hLF := hconv.1
  have hedge := w3b_hedge_of_localFan hLF
  obtain ⟨e1, he1, hfanT⟩ := XRECQNS_UPDATE_p37 hd hLF
  refine ⟨min e e1, lt_min he he1, ?_⟩
  intro t ht
  have ht1 : |t| < e1 := lt_of_lt_of_le ht (min_le_right e e1)
  have hρ := deformation_rho_node1_equivariant1_p14 f (Set.range v)
    (Set.range fun i => {v i, v (i + 1)}) (Set.range fun i => (v i, v (i + 1)))
    (-e) e (v i) t hd hLF hedge (hfanT t ht1) (Set.mem_range_self i)
  have hι := deformation_ivs_rho_node1_equivariant1_p14 f (Set.range v)
    (Set.range fun i => {v i, v (i + 1)}) (Set.range fun i => (v i, v (i + 1)))
    (-e) e (v i) t hd hLF hedge (hfanT t ht1) (Set.mem_range_self i)
  show azim 0 (f (v i) t)
      (rhoNode1 ((fun p : V3 × V3 => (f p.1 t, f p.2 t)) ''
        (Set.range fun i => (v i, v (i + 1)))) (f (v i) t))
      (ivsRhoNode1 ((fun p : V3 × V3 => (f p.1 t, f p.2 t)) ''
        (Set.range fun i => (v i, v (i + 1)))) (f (v i) t)) =
    azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t)
  rw [← hρ, ← hι]
  have hper : Periodic v k := hk ▸ hBB.2.1
  have hinj' : ∀ i j, i < k ∧ j < k ∧ v i = v j → i = j :=
    fun i j h => BBs_inj_p21 s v k hs hk hBB i j h.1 h.2.1 h.2.2
  rw [vv_rho_node1 v k hper (by omega) hinj' i]
  rw [VV_SUC_EQ_IVS_RHO_NODE_PRIME_p21 (Set.range v)
    (Set.range fun i => {v i, v (i + 1)}) (Set.range fun i => (v i, v (i + 1)))
    s v (v i) k i hk rfl rfl rfl rfl hs (by omega) hBB]

/-! ## Section E1: W4 clamp (BBs pair support) -/

noncomputable def w4clamp (f : V3 → ℝ → V3) (e : ℝ) (x : V3) (t : ℝ) : V3 :=
  if |t| < e then f x t else x

/-- HOL `deformation_BBs` (CUXVZOZ.hl:1883; the `//`-commented azim skolem
assumption of the source is dropped): a deformation that is rigid on the
sphere, keeps flat `interior_angle1`s under π and preserves the tight a/b
edges stays in `BBs_v39` for small `t`.
SF-104: `ha`/`hb` are parenthesized as in HOL (`?e1. 0<e1 /\ (tight ==> bound)`);
the previous stub text parsed as `(0<e1 ∧ tight) → bound`, which `e1 := 0`
satisfies vacuously. -/
theorem deformation_BBs_p21 (s : ScsV39) (k : ℕ) (f : V3 → ℝ → V3) (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = k) (hBB : BBsV39 s v) (hg : scsGeneric v)
    (he : 0 < e) (hd : Deformation f (Set.range v) (-e) e)
    (hflat : ∀ i t, t ∈ Ioo (-e) e →
      interiorAngle1 0 (Set.range fun j => (v j, v (j + 1))) (v i) = Real.pi →
        interiorAngle1 0
            (Set.image (fun p : V3 × V3 => (f p.1 t, f p.2 t))
              (Set.range fun j => (v j, v (j + 1)))) (f (v i) t) ≤ Real.pi)
    (hn : ∀ i t, |t| < e → ‖f (v i) t‖ = ‖v i‖)
    (ha : ∀ i j, ∃ e1, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
      ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t)))
    (hb : ∀ i j, ∃ e2, 0 < e2 ∧ (dist (v i) (v j) = s.b i j →
      ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) :
    ∃ e', 0 < e' ∧ ∀ t, |t| < e' → BBsV39 s (fun i => f (v i) t) := by
  obtain ⟨hd0mem, hdcont, hdid⟩ := hd
  obtain ⟨-, hk1, -, -, -, -, -, hpa, -, -, hpb, -, -, -, -, -, -, -, -, -⟩ := hs
  have hper : Periodic v k := by rw [← hk]; exact hBB.2.1
  have hkne : k ≠ 0 := by omega
  have hdistcont : ∀ i j, ContinuousAt (fun t => dist (f (v i) t) (f (v j) t)) 0 := by
    intro i j
    have hci : ContinuousAt (fun t => f (v i) t) 0 :=
      hdcont (v i) (Set.mem_range_self i) 0 ⟨by linarith, he⟩
    have hcj : ContinuousAt (fun t => f (v j) t) 0 :=
      hdcont (v j) (Set.mem_range_self j) 0 ⟨by linarith, he⟩
    have hsub : ContinuousAt (fun t => f (v i) t - f (v j) t) 0 := hci.sub hcj
    have hnorm : ContinuousAt (fun t => ‖f (v i) t - f (v j) t‖) 0 := hsub.norm
    simpa only [dist_eq_norm] using hnorm
  have haP : ∀ i j, ∃ ee : ℝ, 0 < ee ∧ ∀ t, |t| < ee →
      s.a i j ≤ dist (f (v i) t) (f (v j) t) := by
    intro i j
    by_cases htight : s.a i j = dist (v i) (v j)
    · obtain ⟨e1, he1, hcond⟩ := ha i j
      exact ⟨e1, he1, fun t ht => hcond htight t ht⟩
    · have hle : s.a i j ≤ dist (v i) (v j) := (hBB.2.2.1 i j).1
      have hlt : s.a i j < dist (v i) (v j) := lt_of_le_of_ne hle htight
      have hg0 : 0 < dist (f (v i) 0) (f (v j) 0) - s.a i j := by
        rw [hdid (v i) (Set.mem_range_self i), hdid (v j) (Set.mem_range_self j)]
        linarith
      have hcontg : ContinuousAt (fun t => dist (f (v i) t) (f (v j) t) - s.a i j) 0 :=
        (hdistcont i j).sub continuousAt_const
      obtain ⟨ee, hee, hall⟩ := continuous_nbd_pos_p21 hcontg hg0
      exact ⟨ee, hee, fun t ht => by
        have h2 : 0 < dist (f (v i) t) (f (v j) t) - s.a i j :=
          hall t (by simpa using ht)
        linarith⟩
  have hbQ : ∀ i j, ∃ ee : ℝ, 0 < ee ∧ ∀ t, |t| < ee →
      dist (f (v i) t) (f (v j) t) ≤ s.b i j := by
    intro i j
    by_cases htight : dist (v i) (v j) = s.b i j
    · obtain ⟨e2, he2, hcond⟩ := hb i j
      exact ⟨e2, he2, fun t ht => hcond htight t ht⟩
    · have hle : dist (v i) (v j) ≤ s.b i j := (hBB.2.2.1 i j).2
      have hlt : dist (v i) (v j) < s.b i j := lt_of_le_of_ne hle htight
      have hg0 : 0 < s.b i j - dist (f (v i) 0) (f (v j) 0) := by
        rw [hdid (v i) (Set.mem_range_self i), hdid (v j) (Set.mem_range_self j)]
        linarith
      have hcontg : ContinuousAt (fun t => s.b i j - dist (f (v i) t) (f (v j) t)) 0 :=
        continuousAt_const.sub (hdistcont i j)
      obtain ⟨ee, hee, hall⟩ := continuous_nbd_pos_p21 hcontg hg0
      exact ⟨ee, hee, fun t ht => by
        have h2 : 0 < s.b i j - dist (f (v i) t) (f (v j) t) :=
          hall t (by simpa using ht)
        linarith⟩
  have hPper : Periodic2 (fun i j (ee : ℝ) =>
      ∀ t, |t| < ee → s.a i j ≤ dist (f (v i) t) (f (v j) t)) k := by
    intro i j
    have hv1 : v (i + k) = v i := hper i
    have ha1 : s.a (i + k) j = s.a i j := by rw [← hk]; exact (hpa i j).1
    have hv2 : v (j + k) = v j := hper j
    have ha2 : s.a i (j + k) = s.a i j := by rw [← hk]; exact (hpa i j).2
    constructor
    · funext ee
      apply propext
      exact ⟨fun h t ht => by simpa only [hv1, ha1] using h t ht,
        fun h t ht => by simpa only [hv1, ha1] using h t ht⟩
    · funext ee
      apply propext
      exact ⟨fun h t ht => by simpa only [hv2, ha2] using h t ht,
        fun h t ht => by simpa only [hv2, ha2] using h t ht⟩
  have hQper : Periodic2 (fun i j (ee : ℝ) =>
      ∀ t, |t| < ee → dist (f (v i) t) (f (v j) t) ≤ s.b i j) k := by
    intro i j
    have hv1 : v (i + k) = v i := hper i
    have hb1 : s.b (i + k) j = s.b i j := by rw [← hk]; exact (hpb i j).1
    have hv2 : v (j + k) = v j := hper j
    have hb2 : s.b i (j + k) = s.b i j := by rw [← hk]; exact (hpb i j).2
    constructor
    · funext ee
      apply propext
      exact ⟨fun h t ht => by simpa only [hv1, hb1] using h t ht,
        fun h t ht => by simpa only [hv1, hb1] using h t ht⟩
    · funext ee
      apply propext
      exact ⟨fun h t ht => by simpa only [hv2, hb2] using h t ht,
        fun h t ht => by simpa only [hv2, hb2] using h t ht⟩
  have hPmono : ∀ i j (ee ee' : ℝ), ee ≤ ee' →
      (∀ t, |t| < ee' → s.a i j ≤ dist (f (v i) t) (f (v j) t)) →
      ∀ t, |t| < ee → s.a i j ≤ dist (f (v i) t) (f (v j) t) :=
    fun i j ee ee' hle h t ht => h t (lt_of_lt_of_le ht hle)
  have hQmono : ∀ i j (ee ee' : ℝ), ee ≤ ee' →
      (∀ t, |t| < ee' → dist (f (v i) t) (f (v j) t) ≤ s.b i j) →
      ∀ t, |t| < ee → dist (f (v i) t) (f (v j) t) ≤ s.b i j :=
    fun i j ee ee' hle h t ht => h t (lt_of_lt_of_le ht hle)
  obtain ⟨e1, he1, hP1⟩ := (SKOLEM_PERIODIC2_p21 k hPper hkne hPmono).mp haP
  obtain ⟨e2, he2, hQ2⟩ := (SKOLEM_PERIODIC2_p21 k hQper hkne hQmono).mp hbQ
  have hball : ∀ t, |t| < e → Set.range (fun i => f (v i) t) ⊆ ballAnnulus := by
    intro t ht x hx
    obtain ⟨i, rfl⟩ := hx
    simpa [ballAnnulus, dist_eq_norm, hn i t ht] using hBB.1 (Set.mem_range_self i)
  have hperD : ∀ t, Periodic (fun i => f (v i) t) s.k := by
    intro t i
    exact congrArg (fun x => f x t) (hBB.2.1 i)
  by_cases hkle : s.k ≤ 3
  · obtain ⟨e', he', h1, h2, h3⟩ := epsilon_triple_p21 e1 e2 e he1 he2 he
    refine ⟨e', he', fun t ht => ?_⟩
    exact ⟨hball t (h3 t ht), hperD t,
      fun i j => ⟨hP1 i j t (h1 t ht), hQ2 i j t (h2 t ht)⟩, Or.inl hkle⟩
  · have hconv : ConvexLocalFan (Set.range v) (Set.range fun i => {v i, v (i + 1)})
        (Set.range fun i => (v i, v (i + 1))) := by
      rcases hBB.2.2.2 with h3 | hcf
      · exact absurd h3 hkle
      · exact hcf
    have hd' : Deformation (w4clamp f e) (Set.range v) (-e) e := by
      refine ⟨⟨by linarith, he⟩, ?_, ?_⟩
      · intro w hw r hr
        have hcont : ContinuousAt (fun t => f w t) r := hdcont w hw r hr
        have hfun : (fun t => w4clamp f e w t) =ᶠ[nhds r] (fun t => f w t) := by
          filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
          exact if_pos (abs_lt.mpr ht)
        exact hcont.congr hfun.symm
      · intro w hw
        exact (if_pos (by simpa using he) : w4clamp f e w 0 = f w 0).trans (hdid w hw)
    have h4c : ∀ w ∈ Set.range v, ∀ t ∈ Icc (-e) e,
        interiorAngle1 0 (Set.range fun j => (v j, v (j + 1))) w = Real.pi →
        interiorAngle1 0 ((fun d => (w4clamp f e d.1 t, w4clamp f e d.2 t)) ''
          (Set.range fun j => (v j, v (j + 1)))) (w4clamp f e w t) ≤ Real.pi := by
      intro w hw t ht hangle
      obtain ⟨i, rfl⟩ := hw
      by_cases hti : |t| < e
      · have hiff : ∀ x, w4clamp f e x t = f x t := fun x => if_pos hti
        have himg : (fun d : V3 × V3 => (w4clamp f e d.1 t, w4clamp f e d.2 t)) ''
            (Set.range fun j => (v j, v (j + 1))) =
            (fun p : V3 × V3 => (f p.1 t, f p.2 t)) ''
              (Set.range fun j => (v j, v (j + 1))) := by
          apply Set.image_congr
          intro d _
          rw [hiff d.1, hiff d.2]
        rw [himg, hiff (v i)]
        exact hflat i t (abs_lt.mp hti) hangle
      · have hiff : ∀ x, w4clamp f e x t = x := fun x => if_neg hti
        have himg : (fun d : V3 × V3 => (w4clamp f e d.1 t, w4clamp f e d.2 t)) ''
            (Set.range fun j => (v j, v (j + 1))) = (Set.range fun j => (v j, v (j + 1))) := by
          have hid : (fun d : V3 × V3 => (w4clamp f e d.1 t, w4clamp f e d.2 t)) = id := by
            funext d
            rw [hiff d.1, hiff d.2]
            rfl
          rw [hid, Set.image_id]
        rw [himg, hiff (v i), hangle]
    obtain ⟨εc, hεc, hconvT⟩ :=
      ZLZTHIC_p14 (-e) e (Set.range v) (Set.range fun i => {v i, v (i + 1)})
        (Set.range fun i => (v i, v (i + 1))) (w4clamp f e) hconv hg hd' h4c
    obtain ⟨e', he', h1, h2, h3, h4⟩ := epsilon_quad_p21 εc e1 e2 e hεc he1 he2 he
    refine ⟨e', he', fun t ht => ?_⟩
    refine ⟨hball t (h4 t ht), hperD t,
      fun i j => ⟨hP1 i j t (h2 t ht), hQ2 i j t (h3 t ht)⟩, Or.inr ?_⟩
    obtain ⟨hgt, -⟩ := hconvT t (abs_lt.mp (h1 t ht))
    have hfc : ∀ x, w4clamp f e x t = f x t := fun x => if_pos (h4 t ht)
    have hVimg : (fun x => w4clamp f e x t) '' (Set.range v) =
        Set.range (fun i => f (v i) t) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact hfc (v i)
    have hEimg : (fun s => (fun x => w4clamp f e x t) '' s) ''
        (Set.range fun i => ({v i, v (i + 1)} : Set V3)) =
        Set.range (fun i => ({f (v i) t, f (v (i + 1)) t} : Set V3)) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp only [Function.comp_apply]
      rw [Set.image_pair, hfc (v i), hfc (v (i + 1))]
    have hFimg : (fun d : V3 × V3 => (w4clamp f e d.1 t, w4clamp f e d.2 t)) ''
        (Set.range fun i => (v i, v (i + 1))) =
        Set.range (fun i => (f (v i) t, f (v (i + 1)) t)) := by
      rw [← Set.range_comp]
      congr 1
      funext i
      simp only [Function.comp_apply]
      rw [hfc (v i), hfc (v (i + 1))]
    rwa [hVimg, hEimg, hFimg] at hgt

/-- HOL `deformation_BBs_ALT` (CUXVZOZ.hl:2249): the azim-skolem variant —
the flat-angle hypothesis is replaced by the azimuth `≤ π` skolem chain via
`interior_angle1_azim_scs` + `SKOLEM_PERIODIC`.
SF-104: `haz` and the two a/b skolems are parenthesized as in HOL; the
previous stub text parsed as `(0<e ∧ premise) → bound` (vacuous at `e := 0`). -/
theorem deformation_BBs_ALT_p21 (s : ScsV39) (k : ℕ) (f : V3 → ℝ → V3) (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = k) (hk3 : 3 < k) (hBB : BBsV39 s v) (hg : scsGeneric v)
    (he : 0 < e) (hd : Deformation f (Set.range v) (-e) e)
    (haz : ∀ i, ∃ e0, 0 < e0 ∧
      (azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi →
        ∀ t, |t| < e0 →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) ≤ Real.pi))
    (hn : ∀ i t, |t| < e → ‖f (v i) t‖ = ‖v i‖)
    (ha : ∀ i j, ∃ e1, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
      ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t)))
    (hb : ∀ i j, ∃ e2, 0 < e2 ∧ (dist (v i) (v j) = s.b i j →
      ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) :
    ∃ e', 0 < e' ∧ ∀ t, |t| < e' → BBsV39 s (fun i => f (v i) t) := by
  have hper : Periodic v k := by rw [← hk]; exact hBB.2.1
  have hkne : k ≠ 0 := by omega
  have hinj' : ∀ i j, i < k ∧ j < k ∧ v i = v j → i = j :=
    fun i j h => BBs_inj_p21 s v k hs hk hBB i j h.1 h.2.1 h.2.2
  -- uniformize haz over i (period k)
  have hP1per : Periodic (fun i (ee : ℝ) =>
      azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi →
        ∀ t, |t| < ee →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) ≤ Real.pi) k := by
    intro i
    have h1 : v (i + k) = v i := hper i
    have h2 : v ((i + k) + 1) = v (i + 1) := by
      rw [show (i + k) + 1 = (i + 1) + k by omega]; exact hper (i + 1)
    have h3 : v ((i + k) + (k - 1)) = v (i + (k - 1)) := by
      rw [show (i + k) + (k - 1) = (i + (k - 1)) + k by omega]
      exact hper (i + (k - 1))
    funext ee
    apply propext
    exact ⟨fun h hpi t ht => by
        rw [← h1, ← h2, ← h3] at hpi
        simpa only [← h1, ← h2, ← h3] using h hpi t ht,
      fun h hpi t ht => by
        rw [h1, h2, h3] at hpi
        simpa only [h1, h2, h3] using h hpi t ht⟩
  have hP1mono : ∀ i (ee ee' : ℝ), ee ≤ ee' →
      (azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi →
        ∀ t, |t| < ee' →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) ≤ Real.pi) →
      (azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi →
        ∀ t, |t| < ee →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) ≤ Real.pi) :=
    fun i ee ee' hle h hpi t ht => h hpi t (lt_of_lt_of_le ht hle)
  obtain ⟨e0, he0, hP1u⟩ := (SKOLEM_PERIODIC_p21 k hP1per hkne hP1mono).mp haz
  -- uniformize interior_angle1_azim_scs over i (period k)
  have hIAper : Periodic (fun i (ee : ℝ) =>
      ∀ t, |t| < ee →
        interiorAngle1 0 (Set.image (fun p : V3 × V3 => (f p.1 t, f p.2 t))
            (Set.range fun j => (v j, v (j + 1)))) (f (v i) t) =
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t)) k := by
    intro i
    have h1 : v (i + k) = v i := hper i
    have h2 : v ((i + k) + 1) = v (i + 1) := by
      rw [show (i + k) + 1 = (i + 1) + k by omega]; exact hper (i + 1)
    have h3 : v ((i + k) + (k - 1)) = v (i + (k - 1)) := by
      rw [show (i + k) + (k - 1) = (i + (k - 1)) + k by omega]
      exact hper (i + (k - 1))
    funext ee
    apply propext
    exact ⟨fun h t ht => by simpa only [h1, h2, h3] using h t ht,
      fun h t ht => by simpa only [h1, h2, h3] using h t ht⟩
  have hIAmono : ∀ i (ee ee' : ℝ), ee ≤ ee' →
      (∀ t, |t| < ee' →
        interiorAngle1 0 (Set.image (fun p : V3 × V3 => (f p.1 t, f p.2 t))
            (Set.range fun j => (v j, v (j + 1)))) (f (v i) t) =
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t)) →
      ∀ t, |t| < ee →
        interiorAngle1 0 (Set.image (fun p : V3 × V3 => (f p.1 t, f p.2 t))
            (Set.range fun j => (v j, v (j + 1)))) (f (v i) t) =
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) :=
    fun i ee ee' hle h t ht => h t (lt_of_lt_of_le ht hle)
  have hIA : ∀ i, ∃ ee : ℝ, 0 < ee ∧ ∀ t, |t| < ee →
      interiorAngle1 0 (Set.image (fun p : V3 × V3 => (f p.1 t, f p.2 t))
          (Set.range fun j => (v j, v (j + 1)))) (f (v i) t) =
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) :=
    fun i => interior_angle1_azim_scs_p21 (i := i) s v k f e he hd hs hk hk3 hBB
  obtain ⟨e_ia, he_ia, hIAu⟩ := (SKOLEM_PERIODIC_p21 k hIAper hkne hIAmono).mp hIA
  -- interiorAngle1 = azim at the original configuration
  have hia : ∀ i, interiorAngle1 0 (Set.range fun j => (v j, v (j + 1))) (v i)
      = azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) := by
    intro i
    show azim 0 (v i) (rhoNode1 (Set.range fun j => (v j, v (j + 1))) (v i))
        (ivsRhoNode1 (Set.range fun j => (v j, v (j + 1))) (v i)) = _
    rw [vv_rho_node1 v k hper (by omega) hinj' i]
    rw [VV_SUC_EQ_IVS_RHO_NODE_PRIME_p21 (Set.range v) (Set.range fun i => {v i, v (i + 1)})
      (Set.range fun i => (v i, v (i + 1))) s v (v i) k i hk rfl rfl rfl rfl hs (by omega) hBB]
  -- assembly
  set et : ℝ := min (min e0 e_ia) e with het_def
  have het : 0 < et := lt_min (lt_min he0 he_ia) he
  have het0 : et ≤ e0 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hetia : et ≤ e_ia := le_trans (min_le_left _ _) (min_le_right _ _)
  have hete : et ≤ e := min_le_right _ _
  have hd_et : Deformation f (Set.range v) (-et) et := by
    obtain ⟨h0m, hcont, hid⟩ := hd
    refine ⟨⟨by linarith, het⟩, ?_, hid⟩
    intro w hw r hr
    exact hcont w hw r ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hn_et : ∀ i t, |t| < et → ‖f (v i) t‖ = ‖v i‖ :=
    fun i t ht => hn i t (lt_of_lt_of_le ht hete)
  have hflat' : ∀ i t, t ∈ Ioo (-et) et →
      interiorAngle1 0 (Set.range fun j => (v j, v (j + 1))) (v i) = Real.pi →
      interiorAngle1 0 (Set.image (fun p : V3 × V3 => (f p.1 t, f p.2 t))
          (Set.range fun j => (v j, v (j + 1)))) (f (v i) t) ≤ Real.pi := by
    intro i t ht hangle
    have hlt : |t| < et := abs_lt.mpr ht
    have h0 : |t| < e0 := lt_of_lt_of_le hlt het0
    have hi : |t| < e_ia := lt_of_lt_of_le hlt hetia
    have hpi : azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi := by
      rw [← hia i]
      exact hangle
    rw [hIAu i t hi]
    exact hP1u i hpi t h0
  exact deformation_BBs_p21 s k f v et hs hk hBB hg het hd_et hflat' hn_et ha hb

/-! ## Section F: assumption reductions -/

/-- HOL `a_assumption_reduction` (CUXVZOZ.hl:2417): two tight `a`-edges at
`v p1` suffice for all tight edges, off the `scs_diag`/`psort` bookkeeping. -/
theorem a_assumption_reduction_p21 (s : ScsV39) (k p1 : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ) (hs : isScsV39 s) (hk : s.k = k) (hBB : BBsV39 s v)
    (hk3 : 3 < k)
    (hdiag : ∀ i j, scsDiag k i j → psort k (i, j) ≠ psort k (p1 + 1, p1 + (k - 1)) →
      s.a i j < dist (v i) (v j))
    (hd : Deformation f (Set.range v) (-e) e)
    (hfr : ∀ w t, w ≠ v p1 → f w t = w)
    (ha1 : ∃ e1, 0 < e1 ∧ s.a p1 (p1 + 1) = dist (v p1) (v (p1 + 1)) →
      ∀ t, |t| < e1 → s.a p1 (p1 + 1) ≤ dist (f (v p1) t) (f (v (p1 + 1)) t))
    (ha2 : ∃ e1, 0 < e1 ∧ s.a p1 (p1 + (k - 1)) = dist (v p1) (v (p1 + (k - 1))) →
      ∀ t, |t| < e1 → s.a p1 (p1 + (k - 1)) ≤ dist (f (v p1) t) (f (v (p1 + (k - 1))) t)) :
    ∀ i j, ∃ e1, 0 < e1 ∧ s.a i j = dist (v i) (v j) →
      ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t) := by
  -- DISCHARGES: HOL `a_assumption_reduction` (120 lines): mod-k transport
  -- (periodic2_MOD, MOD_LT), BBs_inj injectivity routing, and the freeze
  -- case analysis; the fan bookkeeping (`I_IMP` chain) needs the
  -- deformation-transport kit. NEEDS: merge.
  sorry

/-- HOL `b_assumption_reduction` (CUXVZOZ.hl:2541): the `b`-edge mirror —
two tight `b`-edges at `v p1` suffice, off the `4 * h0` diagonal bound. -/
theorem b_assumption_reduction_p21 (s : ScsV39) (k p1 : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ) (hs : isScsV39 s) (hk : s.k = k) (hBB : BBsV39 s v)
    (hk3 : 3 < k)
    (hdiag : ∀ i j, scsDiag k i j → 4 * h0 < s.b i j)
    (hd : Deformation f (Set.range v) (-e) e)
    (hfr : ∀ w t, w ≠ v p1 → f w t = w)
    (hb1 : ∃ e1, 0 < e1 ∧ dist (v p1) (v (p1 + 1)) = s.b p1 (p1 + 1) →
      ∀ t, |t| < e1 → dist (f (v p1) t) (f (v (p1 + 1)) t) ≤ s.b p1 (p1 + 1))
    (hb2 : ∃ e1, 0 < e1 ∧ dist (v p1) (v (p1 + (k - 1))) = s.b p1 (p1 + (k - 1)) →
      ∀ t, |t| < e1 → dist (f (v p1) t) (f (v (p1 + (k - 1))) t) ≤
        s.b p1 (p1 + (k - 1))) :
    ∀ i j, ∃ e1, 0 < e1 ∧ dist (v i) (v j) = s.b i j →
      ∀ t, |t| < e1 → dist (f (v i) t) (f (v j) t) ≤ s.b i j := by
  -- DISCHARGES: HOL `b_assumption_reduction` (130 lines): same mod-k /
  -- BBs_inj routing as the `a` version over the b-slots.
  -- NEEDS: merge.
  sorry

/-- HOL `azim_assumption_reduction` (CUXVZOZ.hl:2727, the longest theorem of
the file): the azimuth bookkeeping of the one-vertex deformation — split
identities at `v p1`, frozen azimuths off its mod-k class, the flat-`π`
skolem chain, and the frozen neighbours. -/
theorem azim_assumption_reduction_p21 (s : ScsV39) (k p1 : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ) (hs : isScsV39 s) (hk : s.k = k) (hBB : BBsV39 s v)
    (hgen : scsGeneric v) (hk3 : 3 < k)
    (hnc : ¬ Coplanar ({0, v p1, v (p1 + 1), v (p1 + (k - 1))} : Set V3))
    (hd : Deformation f (Set.range v) (-e) e)
    (hfr : ∀ w t, w ≠ v p1 → f w t = w)
    (hz : azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) < Real.pi)
    (h1 : azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + (k - 2))) < Real.pi ∨
      ∃ e1, 0 < e1 ∧ ∀ t, |t| < e1 →
        azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + 1)) ≤
          azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)))
    (h2 : azim 0 (v (p1 + 1)) (v (p1 + 2)) (v p1) < Real.pi ∨
      ∃ e1, 0 < e1 ∧ ∀ t, |t| < e1 →
        azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t) ≤
          azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1)) :
    azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + (k - 2))) =
        azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) +
          azim 0 (v (p1 + (k - 1))) (v (p1 + 1)) (v (p1 + (k - 2))) ∧
      azim 0 (v (p1 + 1)) (v (p1 + 2)) (v p1) =
        azim 0 (v (p1 + 1)) (v (p1 + 2)) (v (p1 + (k - 1))) +
          azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1) ∧
      (∀ i t, p1 % k ≠ i % k → p1 % k ≠ (i + 1) % k → p1 % k ≠ (i + (k - 1)) % k →
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) =
          azim 0 (v i) (v (i + 1)) (v (i + (k - 1)))) ∧
      (∀ i t, p1 % k = i % k →
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) =
          azim 0 (f (v p1) t) (v (p1 + 1)) (v (p1 + (k - 1)))) ∧
      (∀ i t, p1 % k = (i + 1) % k →
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) =
          azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + (k - 2)))) ∧
      (∀ i t, p1 % k = (i + (k - 1)) % k →
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) =
          azim 0 (v (p1 + 1)) (v (p1 + 2)) (f (v p1) t)) ∧
      (∀ i, ∃ e0, 0 < e0 ∧
        azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi →
        ∀ t, |t| < e0 →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) ≤ Real.pi) ∧
      (∃ e1, 0 < e1 ∧ ∀ t, |t| < e1 →
        azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + (k - 2))) =
          azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + 1)) +
            azim 0 (v (p1 + (k - 1))) (v (p1 + 1)) (v (p1 + (k - 2))) ∧
        azim 0 (v (p1 + 1)) (v (p1 + 2)) (f (v p1) t) =
          azim 0 (v (p1 + 1)) (v (p1 + 2)) (v (p1 + (k - 1))) +
            azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t)) ∧
      (∀ t, f (v (p1 + 1)) t = v (p1 + 1) ∧
        f (v (p1 + (k - 1))) t = v (p1 + (k - 1)) ∧
        f (v (p1 + (k - 2))) t = v (p1 + (k - 2)) ∧
        f (v (p1 + 2)) t = v (p1 + 2)) := by
  -- DISCHARGES: HOL `azim_assumption_reduction` (380 lines): the
  -- MOD_SHIFT/periodic routing, BBs_inj, WNWSHJT_ALT-style azimuth
  -- openness, vv_split_azim_alt splits and the psort/mod bookkeeping.
  -- NEEDS: merge with the Terminal azimuth-addition lane.
  sorry

/-- HOL `WNWSHJT_ALT` (CUXVZOZ.hl:2682): openness of a positive azimuth
range under a three-point deformation. -/
theorem WNWSHJT_ALT_p21 (w0 w1 w2 : V3) (f : V3 → ℝ → V3) (a b c : ℝ)
    (hd : Deformation f {w0, w1, w2} a b)
    (h1 : ¬ Collinear ℝ ({0, w1, w2} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, w1, w0} : Set V3))
    (h3 : 0 < azim 0 w1 w2 w0) (h4 : azim 0 w1 w2 w0 < c) :
    ∃ e, 0 < e ∧ ∀ t, |t| < e →
      0 < azim 0 (f w1 t) (f w2 t) (f w0 t) ∧
      azim 0 (f w1 t) (f w2 t) (f w0 t) < c := by
  -- DISCHARGES: HOL REAL_CONTINUOUS_ATREAL_AZIM_COMPOSE (azimuth
  -- continuity, Xbjrphc) + Zlzthic.azim_pos_iff_nz + continuous_nbd_pos;
  -- the azimuth-continuity kit is not ported on this side.
  -- NEEDS: merge with the azimuth-continuity lane.
  sorry

/-! ## Section G: obtuse-monotonicity kit -/

/-- HOL `dih_x5_mono` (CUXVZOZ.hl:3116): `dih_x` decreases in `x5` while
`delta_x6` is negative (MVT over the derived form). -/
theorem dih_x5_mono_p21 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hΔ : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu1 : 0 < upsX x1 x2 x6)
    (hu2 : 0 < upsX x1 x3 x5) (hΔ6 : deltaX6_p21 x1 x2 x3 x4 x5 x6 < 0) :
    ∃ e, 0 < e ∧ ∀ t, |t| < e → t ≤ 0 →
      dihXf x1 x2 x3 x4 (x5 + t) x6 ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  -- DISCHARGES: HOL Ocbicby.derived_form_dih_x_wrt_x5 (the ∂dih_x/∂x5
  -- derivative form `--sqrt x1 * delta_x6 / (ups_x x1 x3 * sqrt delta_x)`)
  -- + REAL_MVT_VERY_SIMPLE + epsilon_triple bookkeeping; the derivative
  -- kit is not ported on this side. NEEDS: merge with the Ocbicby lane.
  sorry

/-- HOL `delta_x5_delta_x6` (CUXVZOZ.hl:3173): `delta_x6` is `delta_x5`
under the `(x2,x3)`/`(x5,x6)` swap; a pure ring identity. -/
theorem delta_x5_delta_x6_p21 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX6_p21 x1 x3 x2 x4 x6 x5 = deltaX5 x1 x2 x3 x4 x5 x6 := by
  unfold deltaX6_p21 deltaX5
  ring

/-- HOL `dih_obtuse_mono` (CUXVZOZ.hl:3182): under a negative `delta_x5`
both `dih_x` at `x4+t` and at `x6+t` decrease. -/
theorem dih_obtuse_mono_p21 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hΔ : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu1 : 0 < upsX x1 x2 x6)
    (hu2 : 0 < upsX x1 x3 x5) (hΔ5 : deltaX5 x1 x2 x3 x4 x5 x6 < 0) :
    ∃ e, 0 < e ∧ ∀ t, |t| < e → t ≤ 0 →
      dihXf x1 x2 x3 (x4 + t) x5 x6 ≤ dihXf x1 x2 x3 x4 x5 x6 ∧
      dihXf x1 x2 x3 x4 x5 (x6 + t) ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  -- DISCHARGES: HOL uses dih_x5_mono (via delta_x5_delta_x6 and
  -- Merge_ineq.delta_x_sym), epsilon_pair bookkeeping and
  -- Tame_inequalities.DIH_X_MONO_LT_4; the delta_x-symmetry and tame
  -- inequalities lanes are not on this side. NEEDS: merge.
  sorry

/-- HOL `dih_obtuse_mono_b` (CUXVZOZ.hl:3228): the unconditional half of
`dih_obtuse_mono` (only the `x4+t` slot, no `delta_x5` hypothesis). -/
theorem dih_obtuse_mono_b_p21 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hΔ : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu1 : 0 < upsX x1 x2 x6)
    (hu2 : 0 < upsX x1 x3 x5) :
    ∃ e, 0 < e ∧ ∀ t, |t| < e → t ≤ 0 →
      dihXf x1 x2 x3 (x4 + t) x5 x6 ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  -- DISCHARGES: HOL Tame_inequalities.DIH_X_MONO_LT_4 + the delta_x
  -- continuity nbd bookkeeping. NEEDS: merge with the tame-inequalities
  -- lane.
  sorry

/-- HOL `square_add_neg_lemma` (CUXVZOZ.hl:3258). -/
theorem square_add_neg_lemma_p21 (y t : ℝ) (ht : t ≤ 0) (h : 0 ≤ t + 2 * y) :
    2 * y * t + t * t ≤ 0 := by
  have h1 : (0 - t) * (t + 2 * y) ≥ 0 := mul_nonneg (by linarith) h
  have h2 : 2 * y * t + t * t = -((0 - t) * (t + 2 * y)) := by ring
  rw [h2]
  linarith

/-- HOL `dihV_obtuse_mono_a` (CUXVZOZ.hl:3269): the obtuse `dihV` decreases
when `v2` moves along the `v2-v3` edge towards `v3`. -/
theorem dihV_obtuse_mono_a_p21 (v0 v1 v2 v3 : V3)
    (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3))
    (hz : Real.pi / 2 < dihV v0 v2 v3 v1) :
    ∃ e, 0 < e ∧ ∀ v2' : V3, ∀ t : ℝ, |t| < e → t ≤ 0 →
      dist v0 v2' = dist v0 v2 → dist v1 v2' = dist v1 v2 →
      dist v2' v3 = dist v2 v3 + t →
      dihV v0 v3 v2' v1 ≤ dihV v0 v3 v2 v1 := by
  -- DISCHARGES: HOL Merge_ineq.DIHV_DIH_X (dihV = dih_x on the squared
  -- distances), Collect_geom2.NOT_COL_EQ_UPS_X_POS, Merge_ineq.dih_gt_pi2
  -- and the epsilon_quad bookkeeping; the DIHV_DIH_X bridge is not on this
  -- side. NEEDS: merge with the Merge_ineq lane.
  sorry

/-- HOL `dihV_obtuse_mono_b` (CUXVZOZ.hl:3378): the opposite-handed half —
`dihV v0 v1 v2' v3` decreases under the same edge move. -/
theorem dihV_obtuse_mono_b_p21 (v0 v1 v2 v3 : V3)
    (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3)) :
    ∃ e, 0 < e ∧ ∀ v2' : V3, ∀ t : ℝ, |t| < e → t ≤ 0 →
      dist v0 v2' = dist v0 v2 → dist v1 v2' = dist v1 v2 →
      dist v2' v3 = dist v2 v3 + t →
      dihV v0 v1 v2' v3 ≤ dihV v0 v1 v2 v3 := by
  -- DISCHARGES: HOL Merge_ineq.DIHV_DIH_X + square_add_neg_lemma +
  -- epsilon_quad bookkeeping. NEEDS: the DIHV_DIH_X bridge (see above).
  sorry

/-- HOL `dihV_obtuse_mono` (CUXVZOZ.hl:3476): the combined statement —
from `dihV_obtuse_mono_a` (obtuse case, ε interleaved with `_b` via
`epsilon_pair`) and `dihV_obtuse_mono_b`. -/
theorem dihV_obtuse_mono_p21 (v0 v1 v2 v3 : V3)
    (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3)) :
    ∃ e, 0 < e ∧
      (Real.pi / 2 < dihV v0 v2 v3 v1 → ∀ v2' : V3, ∀ t : ℝ, |t| < e → t ≤ 0 →
        dist v0 v2' = dist v0 v2 → dist v1 v2' = dist v1 v2 →
        dist v2' v3 = dist v2 v3 + t →
        dihV v0 v3 v2' v1 ≤ dihV v0 v3 v2 v1) ∧
      (∀ v2' : V3, ∀ t : ℝ, |t| < e → t ≤ 0 →
        dist v0 v2' = dist v0 v2 → dist v1 v2' = dist v1 v2 →
        dist v2' v3 = dist v2 v3 + t →
        dihV v0 v1 v2' v3 ≤ dihV v0 v1 v2 v3) := by
  by_cases hz : Real.pi / 2 < dihV v0 v2 v3 v1
  · obtain ⟨e1, he1, h1⟩ := dihV_obtuse_mono_a_p21 v0 v1 v2 v3 hnc hz
    obtain ⟨e2, he2, h2⟩ := dihV_obtuse_mono_b_p21 v0 v1 v2 v3 hnc
    refine ⟨min e1 e2, lt_min he1 he2, ?_, ?_⟩
    · intro _ v2' t ht h1' h2' h3'
      exact h1 v2' t (lt_min_iff.mp ht).1 h1' h2' h3'
    · intro v2' t ht h1' h2' h3'
      exact h2 v2' t (lt_min_iff.mp ht).2 h1' h2' h3'
  · obtain ⟨e2, he2, h2⟩ := dihV_obtuse_mono_b_p21 v0 v1 v2 v3 hnc
    refine ⟨e2, he2, ?_, h2⟩
    intro hcon
    exact absurd hcon hz

/-- HOL `real_continuous_abs` (CUXVZOZ.hl:3517). -/
theorem real_continuous_abs_p21 (x : ℝ) : ContinuousAt abs x :=
  (Real.uniformContinuous_abs.continuous.continuousAt : ContinuousAt abs x)

/-! ## Section H: terminal chain -/

/-- HOL `MMs_minimize_tau_fun` (CUXVZOZ.hl:3549): the tau-fun sum is
minimized over `MMs_v39`. -/
theorem MMs_minimize_tau_fun_p21 (s : ScsV39) (k : ℕ) (v w : ℕ → V3)
    (hs : isScsV39 s) (hbasic : scsBasicV39 s) (hk : s.k = k) (hk3 : 3 < k)
    (hv : v ∈ BBprimeV39 s) (hw : BBsV39 s w) :
    setSum {i | i < k}
        (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + (k - 1)))) ≤
      setSum {i | i < k}
        (fun i => rhoFun ‖w i‖ * azim 0 (w i) (w (i + 1)) (w (i + (k - 1)))) := by
  -- DISCHARGES: HOL Appendix.taustar_v39 / BBprime_v39 unfoldings,
  -- Terminal.tau_fun_azim, Appendix.dsv_J_empty, Appendix.scs_basic and
  -- Ayqjtmd.unadorned_MMs; the taustar registry lane is not on this side.
  -- NEEDS: merge with the taustar/BBprime lane.
  sorry

/-- HOL `tau3_taum_nonplanar` (CUXVZOZ.hl:3608): off the coplanar locus
`tau3` is the truncated tau `taum` on the edge lengths. -/
theorem tau3_taum_nonplanar_p21 (v0 v1 v2 : V3)
    (hnc : ¬ Coplanar ({0, v0, v1, v2} : Set V3)) :
    tau3 v0 v1 v2 =
      taum ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1) := by
  have hcopl : ∀ {z w w1 w2 : V3}, Collinear3 z w w1 → Coplanar ({z, w, w1, w2} : Set V3) := by
    intro z w w1 w2 hc
    by_cases hzw : z = w
    · subst hzw
      have hset : ({z, z, w1, w2} : Set V3) = {z, w1, w2} := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset]
      exact coplanar_triple z w1 w2
    · have hwz : w ≠ z := fun h => hzw h.symm
      have hspan : w1 ∈ (affineSpan ℝ ({z, w} : Set V3) : Set V3) := by
        obtain ⟨c, hsmul⟩ := (collinear3_iff_smul (w := w) (v := z) hwz).mp hc
        refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨c, ?_⟩
        rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
        exact (sub_eq_iff_eq_add.mp hsmul).symm
      refine ⟨z, w, w2, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with hz | hw | hw1' | hw2
      · rw [hz]; exact mem_affineSpan ℝ (by simp)
      · rw [hw]; exact mem_affineSpan ℝ (by simp)
      · rw [hw1']
        refine affineSpan_mono ℝ ?_ hspan
        intro q hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
        tauto
      · rw [hw2]; exact mem_affineSpan ℝ (by simp)
  have hswap : ∀ {a b c : V3}, Collinear3 a b c → Collinear3 a c b := by
    intro a b c h
    unfold Collinear3
    rw [show ({a, c, b} : Set V3) = {a, b, c} from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact h
  have hn01 : ¬ Collinear3 0 v0 v1 := fun hc => hnc (hcopl hc)
  have hn02 : ¬ Collinear3 0 v0 v2 := fun hc =>
    hnc (by
      have h := hcopl (z := 0) (w := v0) (w1 := v2) (w2 := v1) hc
      have hset : ({0, v0, v2, v1} : Set V3) = ({0, v0, v1, v2} : Set V3) := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at h)
  have hn12 : ¬ Collinear3 0 v1 v2 := fun hc =>
    hnc (by
      have h := hcopl (z := 0) (w := v1) (w1 := v2) (w2 := v0) hc
      have hset : ({0, v1, v2, v0} : Set V3) = ({0, v0, v1, v2} : Set V3) := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at h)
  have hn10 : ¬ Collinear3 0 v1 v0 := fun hc => hn01 (hswap hc)
  have hn20 : ¬ Collinear3 0 v2 v0 := fun hc => hn02 (hswap hc)
  have hn21 : ¬ Collinear3 0 v2 v1 := fun hc => hn12 (hswap hc)
  rw [taum_dih_y_p16 ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1)]
  unfold tau3
  rw [DIHV_EQ_DIH_Y_4PT_B 0 v0 v1 v2 hn01 hn02,
      DIHV_EQ_DIH_Y_4PT_B 0 v1 v2 v0 hn12 hn10,
      DIHV_EQ_DIH_Y_4PT_B 0 v2 v0 v1 hn20 hn21]
  simp only [dist_comm, dist_zero_right]

/-- 三点共线 ⟹ 加点后共面（`{z,w,w1,w2}`）；用于从 `¬ Coplanar` 反推
`¬ Collinear3`（LuneVolume 同名私件不在本闭包内，此处重证）。 -/
private theorem collinear3_coplanar4 {z w w1 w2 : V3} (hc : Collinear3 z w w1) :
    Coplanar ({z, w, w1, w2} : Set V3) := by
  by_cases hzw : z = w
  · subst hzw
    have hset : ({z, z, w1, w2} : Set V3) = {z, w1, w2} := by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact coplanar_triple z w1 w2
  · have hwz : w ≠ z := fun h => hzw h.symm
    have hspan : w1 ∈ (affineSpan ℝ ({z, w} : Set V3) : Set V3) := by
      obtain ⟨c, hsmul⟩ := (collinear3_iff_smul (w := w) (v := z) hwz).mp hc
      refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨c, ?_⟩
      rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      exact (sub_eq_iff_eq_add.mp hsmul).symm
    refine ⟨z, w, w2, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hz | hw | hw1' | hw2
    · rw [hz]; exact mem_affineSpan ℝ (by simp)
    · rw [hw]; exact mem_affineSpan ℝ (by simp)
    · rw [hw1']
      refine affineSpan_mono ℝ ?_ hspan
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
      tauto
    · rw [hw2]; exact mem_affineSpan ℝ (by simp)

/-- `Collinear3` 的后两位对换。 -/
private theorem collinear3_swap23 {a b c : V3} (h : Collinear3 a b c) :
    Collinear3 a c b := by
  unfold Collinear3
  rw [show ({a, c, b} : Set V3) = {a, b, c} from by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  exact h

/-- HOL `tau3_azim` (CUXVZOZ.hl:3629): the azimuth rendering of `tau3`. -/
theorem tau3_azim_p21 (v0 v1 v2 : V3)
    (hnc : ¬ Coplanar ({0, v0, v1, v2} : Set V3))
    (haz : azim 0 v0 v1 v2 ≤ Real.pi) :
    tau3 v0 v1 v2 = rho ‖v0‖ * azim 0 v0 v1 v2 +
        rho ‖v1‖ * azim 0 v1 v2 v0 + rho ‖v2‖ * azim 0 v2 v0 v1 -
        (Real.pi + sol0) := by
  have hn01 : ¬ Collinear3 0 v0 v1 := fun hc => hnc (collinear3_coplanar4 hc)
  have hn02 : ¬ Collinear3 0 v0 v2 := fun hc =>
    hnc (by
      have h := collinear3_coplanar4 (z := 0) (w := v0) (w1 := v2) (w2 := v1) hc
      have hset : ({0, v0, v2, v1} : Set V3) = ({0, v0, v1, v2} : Set V3) := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at h)
  have hn12 : ¬ Collinear3 0 v1 v2 := fun hc =>
    hnc (by
      have h := collinear3_coplanar4 (z := 0) (w := v1) (w1 := v2) (w2 := v0) hc
      have hset : ({0, v1, v2, v0} : Set V3) = ({0, v0, v1, v2} : Set V3) := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at h)
  have hn10 : ¬ Collinear3 0 v1 v0 := fun hc => hn01 (collinear3_swap23 hc)
  have hn20 : ¬ Collinear3 0 v2 v0 := fun hc => hn02 (collinear3_swap23 hc)
  have hn21 : ¬ Collinear3 0 v2 v1 := fun hc => hn12 (collinear3_swap23 hc)
  have hπ2 : azim 0 v1 v2 v0 ≤ Real.pi := FSQKWKK_p16 0 v0 v1 v2 haz
  have hπ3 : azim 0 v2 v0 v1 ≤ Real.pi := FSQKWKK_p16 0 v1 v2 v0 hπ2
  have e1 : dihV 0 v0 v1 v2 = azim 0 v0 v1 v2 :=
    (AZIM_DIHV_SAME_STRONG hn01 hn02 haz).symm
  have e2 : dihV 0 v1 v2 v0 = azim 0 v1 v2 v0 :=
    (AZIM_DIHV_SAME_STRONG hn12 hn10 hπ2).symm
  have e3 : dihV 0 v2 v0 v1 = azim 0 v2 v0 v1 :=
    (AZIM_DIHV_SAME_STRONG hn20 hn21 hπ3).symm
  unfold tau3
  rw [e1, e2, e3]

/-- HOL `general_482_deformation` (CUXVZOZ.hl:3649, 640 lines): the master
482-cell deformation theorem. -/
theorem general_482_deformation_p21 (h : mainNonlinearTerminalV11_p21)
    (s : ScsV39) (FF : Set (V3 × V3)) (k p0 p1 p2 : ℕ) (v : ℕ → V3)
    (hpair : ({v p0, v p2} : Set V3) = ({v (p1 + 1), v (p1 + (k - 1))} : Set V3))
    (hFF : FF = Set.range fun i => (v i, v (i + 1)))
    (hs : isScsV39 s) (hk : k = s.k) (hk3 : 3 < k) (hMMs : v ∈ MMsV39 s)
    (hbasic : scsBasicV39 s) (hgen : scsGeneric v)
    (h3 : 3 ≤ dist (v p0) (v p2))
    (ha : ∀ i j, scsDiag k i j → psort k (i, j) ≠ psort k (p0, p2) →
      s.a i j < dist (v i) (v j))
    (hb : ∀ i j, scsDiag k i j → 4 * h0 < s.b i j)
    (hang : interiorAngle1 0 FF (v p1) < Real.pi)
    (hcase : Real.pi / 2 < interiorAngle1 0 FF (v p1) ∨
      interiorAngle1 0 FF (v p2) < Real.pi)
    (ha12 : s.a p1 p2 = 2) (hb12 : s.b p1 p2 ≤ 2 * h0)
    (h2 : 2 ≤ dist (v p0) (v p1)) (hdc : dist (v p0) (v p1) ≤ cstab) :
    dist (v p1) (v p2) = 2 := by
  -- DISCHARGES: HOL `general_482_deformation` (640 lines): the strata
  -- dispatch (obtuse/nonplanar/acute subcases) assembling the a/b/azim
  -- assumption reductions, deformation_BBs, general_482 lemmas and the
  -- nonlinear registry entries. NEEDS: the full CUXVZOZ terminal chain.
  sorry

/-- HOL `CUXVZOZ` (CUXVZOZ.hl:4289): the check-completeness lemma — from
`general_482_deformation` by `p0 := p1 + (k-1)`, `p2 := p1 + 1` (exactly the
HOL proof's instantiation + `SET_TAC`). -/
theorem CUXVZOZ_p21 (h : mainNonlinearTerminalV11_p21) (s : ScsV39)
    (FF : Set (V3 × V3)) (k p1 : ℕ) (v : ℕ → V3)
    (hFF : FF = Set.range fun i => (v i, v (i + 1)))
    (hs : isScsV39 s) (hk : k = s.k) (hk3 : 3 < k) (hMMs : v ∈ MMsV39 s)
    (hbasic : scsBasicV39 s) (hgen : scsGeneric v)
    (hd : 3 ≤ dist (v (p1 + (k - 1))) (v (p1 + 1)))
    (ha : ∀ i j, scsDiag k i j → psort k (i, j) ≠ psort k (p1 + (k - 1), p1 + 1) →
      s.a i j < dist (v i) (v j))
    (hb : ∀ i j, scsDiag k i j → 4 * h0 < s.b i j)
    (hang : interiorAngle1 0 FF (v p1) < Real.pi)
    (hcase : Real.pi / 2 < interiorAngle1 0 FF (v p1) ∨
      interiorAngle1 0 FF (v (p1 + 1)) < Real.pi)
    (ha12 : s.a p1 (p1 + 1) = 2) (hb12 : s.b p1 (p1 + 1) ≤ 2 * h0)
    (h2 : 2 ≤ dist (v (p1 + (k - 1))) (v p1))
    (hdc : dist (v (p1 + (k - 1))) (v p1) ≤ cstab) :
    dist (v p1) (v (p1 + 1)) = 2 := by
  have hgen2 := general_482_deformation_p21 h s FF k (p1 + (k - 1)) p1 (p1 + 1) v
    (Set.pair_comm _ _) hFF hs hk hk3 hMMs hbasic hgen hd
    (fun i j hdiag hps => ha i j hdiag hps)
    hb hang hcase ha12 hb12 h2 hdc
  exact hgen2

/-- HOL `CJBDXXN` (CUXVZOZ.hl:4319): the mirrored check-completeness lemma —
from `general_482_deformation` by `p0 := p1 + 1`, `p2 := p1 + (k-1)`. -/
theorem CJBDXXN_p21 (h : mainNonlinearTerminalV11_p21) (s : ScsV39)
    (FF : Set (V3 × V3)) (k p1 : ℕ) (v : ℕ → V3)
    (hFF : FF = Set.range fun i => (v i, v (i + 1)))
    (hs : isScsV39 s) (hk : k = s.k) (hk3 : 3 < k) (hMMs : v ∈ MMsV39 s)
    (hbasic : scsBasicV39 s) (hgen : scsGeneric v)
    (hd : 3 ≤ dist (v (p1 + 1)) (v (p1 + (k - 1))))
    (ha : ∀ i j, scsDiag k i j → psort k (i, j) ≠ psort k (p1 + 1, p1 + (k - 1)) →
      s.a i j < dist (v i) (v j))
    (hb : ∀ i j, scsDiag k i j → 4 * h0 < s.b i j)
    (hang : interiorAngle1 0 FF (v p1) < Real.pi)
    (hcase : Real.pi / 2 < interiorAngle1 0 FF (v p1) ∨
      interiorAngle1 0 FF (v (p1 + (k - 1))) < Real.pi)
    (ha12 : s.a p1 (p1 + (k - 1)) = 2) (hb12 : s.b p1 (p1 + (k - 1)) ≤ 2 * h0)
    (h2 : 2 ≤ dist (v (p1 + 1)) (v p1))
    (hdc : dist (v (p1 + 1)) (v p1) ≤ cstab) :
    dist (v p1) (v (p1 + (k - 1))) = 2 := by
  exact general_482_deformation_p21 h s FF k (p1 + 1) p1 (p1 + (k - 1)) v rfl hFF hs
    hk hk3 hMMs hbasic hgen hd (fun i j hdiag hps => ha i j hdiag hps) hb hang hcase
    ha12 hb12 h2 hdc

end Kepler.Text
