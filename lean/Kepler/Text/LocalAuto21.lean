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

/-- helper: `(a + c) % k ≠ a % k` for `0 < c < k`. -/
private theorem add_mod_ne_p21 (a c k : ℕ) (hc0 : 0 < c) (hck : c < k) :
    (a + c) % k ≠ a % k := by
  intro h
  have h1 : (a + c) % k = (a % k + c) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hck]
  rw [h1] at h
  have hr : a % k < k := Nat.mod_lt _ (lt_trans hc0 hck)
  rcases Nat.lt_or_ge (a % k + c) k with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have h2 : a % k + c - k < k := by omega
    rw [show a % k + c = (a % k + c - k) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt h2] at h
    omega

/-- HOL `WNWSHJT_ALT` (CUXVZOZ.hl:2682), private copy: the public
`WNWSHJT_ALT_p21` is declared *after* `azim_assumption_reduction_p21` in
source order, so the azimuth reduction consumes this copy (the public
theorem below is the same statement, proved from this). -/
private theorem w_nwshjt_p21 (w0 w1 w2 : V3) (f : V3 → ℝ → V3) (a b c : ℝ)
    (hd : Deformation f {w0, w1, w2} a b)
    (h1 : ¬ Collinear ℝ ({0, w1, w2} : Set V3))
    (h2 : ¬ Collinear ℝ ({0, w1, w0} : Set V3))
    (h3 : 0 < azim 0 w1 w2 w0) (h4 : azim 0 w1 w2 w0 < c) :
    ∃ e, 0 < e ∧ ∀ t, |t| < e →
      0 < azim 0 (f w1 t) (f w2 t) (f w0 t) ∧
      azim 0 (f w1 t) (f w2 t) (f w0 t) < c := by
  obtain ⟨h0mem, hcont, hfix⟩ := hd
  have hc1 : ContinuousAt (fun t => f w1 t) 0 := hcont w1 (by simp) 0 h0mem
  have hc2 : ContinuousAt (fun t => f w2 t) 0 := hcont w2 (by simp) 0 h0mem
  have hc0 : ContinuousAt (fun t => f w0 t) 0 := hcont w0 (by simp) 0 h0mem
  have hf1 : f w1 0 = w1 := hfix w1 (by simp)
  have hf2 : f w2 0 = w2 := hfix w2 (by simp)
  have hf0 : f w0 0 = w0 := hfix w0 (by simp)
  have hcol1 : ¬ Collinear ℝ ({0, f w1 0, f w2 0} : Set V3) := by
    rw [hf1, hf2]; exact h1
  have hcol2 : ¬ Collinear ℝ ({0, f w1 0, f w0 0} : Set V3) := by
    rw [hf1, hf0]; exact h2
  have hpos0 : azim 0 (f w1 0) (f w2 0) (f w0 0) ≠ 0 := by
    rw [hf1, hf2, hf0]
    exact ne_of_gt h3
  have hazc : ContinuousAt (fun t => azim 0 (f w1 t) (f w2 t) (f w0 t)) 0 :=
    w5cA3_continuousAt_azim hc1 hc2 hc0 hcol1 hcol2 hpos0
  have hpos : ∃ e, 0 < e ∧ ∀ t, |t| < e → 0 < azim 0 (f w1 t) (f w2 t) (f w0 t) := by
    have h := continuous_nbd_pos_p21 hazc (t := 0) (by rw [hf1, hf2, hf0]; exact h3)
    simpa using h
  have hbound : ∃ e, 0 < e ∧ ∀ t, |t| < e → azim 0 (f w1 t) (f w2 t) (f w0 t) < c := by
    have hct : ContinuousAt (fun t => c - azim 0 (f w1 t) (f w2 t) (f w0 t)) 0 :=
      continuousAt_const.sub hazc
    have hpt : 0 < c - azim 0 (f w1 0) (f w2 0) (f w0 0) := by
      rw [hf1, hf2, hf0]; linarith
    obtain ⟨e, he, hall⟩ := continuous_nbd_pos_p21 hct hpt
    refine ⟨e, he, fun t ht => ?_⟩
    have := hall t (by simpa using ht)
    linarith
  obtain ⟨e1, he1, hb1⟩ := hpos
  obtain ⟨e2, he2, hb2⟩ := hbound
  exact ⟨min e1 e2, lt_min he1 he2, fun t ht => ⟨
    hb1 t (lt_of_lt_of_le ht (min_le_left _ _)),
    hb2 t (lt_of_lt_of_le ht (min_le_right _ _))⟩⟩

/-- HOL `a_assumption_reduction` (CUXVZOZ.hl:2417): two tight `a`-edges at
`v p1` suffice for all tight edges, off the `scs_diag`/`psort` bookkeeping. -/
theorem a_assumption_reduction_p21 (s : ScsV39) (k p1 : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ) (hs : isScsV39 s) (hk : s.k = k) (hBB : BBsV39 s v)
    (hk3 : 3 < k)
    (hdiag : ∀ i j, scsDiag k i j → psort k (i, j) ≠ psort k (p1 + 1, p1 + (k - 1)) →
      s.a i j < dist (v i) (v j))
    (hd : Deformation f (Set.range v) (-e) e)
    (hfr : ∀ w t, w ≠ v p1 → f w t = w)
    (ha1 : ∃ e1, 0 < e1 ∧ (s.a p1 (p1 + 1) = dist (v p1) (v (p1 + 1)) →
      ∀ t, |t| < e1 → s.a p1 (p1 + 1) ≤ dist (f (v p1) t) (f (v (p1 + 1)) t)))
    (ha2 : ∃ e1, 0 < e1 ∧ (s.a p1 (p1 + (k - 1)) = dist (v p1) (v (p1 + (k - 1))) →
      ∀ t, |t| < e1 → s.a p1 (p1 + (k - 1)) ≤ dist (f (v p1) t) (f (v (p1 + (k - 1))) t))) :
    ∀ i j, ∃ e1, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
      ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t)) := by
  -- PROVED: HOL proof ported (mod-k reduction via `periodic2_mod_reduce`,
  -- `BBs_inj` routing for distinct mod classes, and the freeze case).

  have hsK := hs
  have _ := hd
  obtain ⟨-, -, -, -, -, -, -, hpa0, -, -, -, -, hsym, -, -, -, -, -, -, -, -⟩ := hs
  have hkne : k ≠ 0 := by omega
  have hpa : Periodic2 s.a k := hk ▸ hpa0
  have hperv : Periodic v k := hk ▸ hBB.2.1
  have hvmod : ∀ i, v (i % k) = v i := fun i => periodic_mod_p21 hkne hperv i
  have hinjmod : ∀ i j, v (i % k) = v (j % k) → i % k = j % k :=
    fun i j h => BBs_inj_p21 s v k hsK hk hBB (i % k) (j % k)
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h
  have hp1ne : p1 % k ≠ (p1 + 1) % k := fun h =>
    add_mod_ne_p21 p1 1 k one_pos (by omega) h.symm
  have hp1ne' : p1 % k ≠ (p1 + (k - 1)) % k := fun h =>
    add_mod_ne_p21 p1 (k - 1) k (by omega) (by omega) h.symm
  have hamod : ∀ i j, s.a i j = s.a (i % k) (j % k) := fun i j =>
    periodic2_MOD_p21 (a := s.a) (i := i) (j := j) (k := k) hkne hpa
  -- the p1-anchored claim (`j < k`), in the statement's shape `∃e1, 0<e1 ∧ (eq → B)`
  have hclaim : ∀ j, j < k → ∃ e1, 0 < e1 ∧ (s.a p1 j = dist (v p1) (v j) →
      ∀ t, |t| < e1 → s.a p1 j ≤ dist (f (v p1) t) (f (v j) t)) := by
    intro j hj
    by_cases hdj : scsDiag k p1 j
    · have hps : psort k (p1, j) ≠ psort k (p1 + 1, p1 + (k - 1)) := by
        intro h
        rcases psort_inj_p21 k p1 j (p1 + 1) (p1 + (k - 1)) h with h1 | h2
        · exact hp1ne h1
        · exact hp1ne' h2
      have hlt := hdiag p1 j hdj hps
      exact ⟨1, one_pos, fun heq => absurd heq (ne_of_lt hlt)⟩
    · have hcase : p1 % k = j % k ∨ (p1 + 1) % k = j % k ∨ p1 % k = (j + 1) % k := by
        unfold scsDiag at hdj
        tauto
      rcases hcase with hA | hB | hC
      · -- j ≡ p1: both points frozen, distance 0
        refine ⟨1, one_pos, ?_⟩
        intro heq
        have hvj : v j = v p1 := by rw [← hvmod j, ← hvmod p1, hA]
        intro t ht
        rw [hvj] at heq ⊢
        rw [dist_self] at heq ⊢
        rw [heq]
      · -- j ≡ p1 + 1: use ha1
        obtain ⟨e1, he1, hb⟩ := ha1
        refine ⟨e1, he1, ?_⟩
        intro heq
        have hvj : v j = v (p1 + 1) := by rw [← hvmod j, ← hvmod (p1 + 1), hB]
        have haj : s.a p1 j = s.a p1 (p1 + 1) := by
          rw [hamod p1 j, hamod p1 (p1 + 1), hB]
        intro t ht
        rw [hvj, haj] at heq ⊢
        exact hb heq t ht
      · -- j ≡ p1 + k - 1: use ha2
        obtain ⟨e1, he1, hb⟩ := ha2
        refine ⟨e1, he1, ?_⟩
        intro heq
        have hjk : j % k = (p1 + (k - 1)) % k := by
          have h := MOD_SHIFT_p21 k p1 (j + 1) (k - 1) hkne hC
          rw [show j + 1 + (k - 1) = j + k by omega, Nat.add_mod_right] at h
          exact h.symm
        have hvj : v j = v (p1 + (k - 1)) := by
          rw [← hvmod j, ← hvmod (p1 + (k - 1)), hjk]
        have haj : s.a p1 j = s.a p1 (p1 + (k - 1)) := by
          rw [hamod p1 j, hamod p1 (p1 + (k - 1)), hjk]
        intro t ht
        rw [hvj, haj] at heq ⊢
        exact hb heq t ht
  -- assembly for `i, j < k`
  have hbounded : ∀ i j, i < k → j < k → ∃ e1,
      0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t)) := by
    intro i j hi hj
    by_cases hi1 : i % k = p1 % k
    · obtain ⟨e1, he1, hb⟩ := hclaim j hj
      refine ⟨e1, he1, ?_⟩
      intro heq
      have hvi : v i = v p1 := by rw [← hvmod i, ← hvmod p1, hi1]
      have hai : s.a i j = s.a p1 j := by rw [hamod i j, hamod p1 j, hi1]
      intro t ht
      rw [hvi, hai] at heq ⊢
      exact hb heq t ht
    · by_cases hj1 : j % k = p1 % k
      · obtain ⟨e1, he1, hb⟩ := hclaim i hi
        refine ⟨e1, he1, ?_⟩
        intro heq
        have hvj : v j = v p1 := by rw [← hvmod j, ← hvmod p1, hj1]
        have haji : s.a i j = s.a p1 i := by
          calc s.a i j = s.a (i % k) (j % k) := hamod i j
            _ = s.a (i % k) (p1 % k) := by rw [hj1]
            _ = s.a (p1 % k) (i % k) := (hsym (i % k) (p1 % k)).1
            _ = s.a p1 i := (hamod p1 i).symm
        intro t ht
        rw [hvj, haji] at heq ⊢
        have hble := hb (by rw [dist_comm]; exact heq) t ht
        rwa [dist_comm] at hble
      · refine ⟨1, one_pos, ?_⟩
        intro heq
        have hvi : v i ≠ v p1 := by
          intro hve
          exact hi1 (hinjmod i p1 (by rw [hvmod i, hvmod p1]; exact hve))
        have hvj : v j ≠ v p1 := by
          intro hve
          exact hj1 (hinjmod j p1 (by rw [hvmod j, hvmod p1]; exact hve))
        intro t ht
        rw [hfr (v i) t hvi, hfr (v j) t hvj]
        exact le_of_eq heq
  have hP : ∀ a b, (∃ e1, 0 < e1 ∧ (s.a a b = dist (v a) (v b) →
        ∀ t, |t| < e1 → s.a a b ≤ dist (f (v a) t) (f (v b) t))) =
      (∃ e1, 0 < e1 ∧ (s.a (a % k) (b % k) = dist (v (a % k)) (v (b % k)) →
        ∀ t, |t| < e1 → s.a (a % k) (b % k) ≤ dist (f (v (a % k)) t) (f (v (b % k)) t))) := by
    intro a b
    rw [hamod a b, hvmod a, hvmod b]
  intro i j
  refine periodic2_mod_reduce
    (P := fun i j => ∃ e1, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
      ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t)))
    k hkne ?_ ?_ i j
  · intro i j
    show (∃ e1, 0 < e1 ∧ (s.a (i + k) j = dist (v (i + k)) (v j) →
        ∀ t, |t| < e1 → s.a (i + k) j ≤ dist (f (v (i + k)) t) (f (v j) t))) =
      (∃ e1, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))) ∧
      (∃ e1, 0 < e1 ∧ (s.a i (j + k) = dist (v i) (v (j + k)) →
        ∀ t, |t| < e1 → s.a i (j + k) ≤ dist (f (v i) t) (f (v (j + k)) t))) =
      (∃ e1, 0 < e1 ∧ (s.a i j = dist (v i) (v j) →
        ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t)))
    exact ⟨by rw [hP (i + k) j, hP i j, Nat.add_mod_right],
      by rw [hP i (j + k), hP i j, Nat.add_mod_right]⟩
  · exact fun i j hij => hbounded i j hij.1 hij.2

/-- HOL `b_assumption_reduction` (CUXVZOZ.hl:2541): the `b`-edge mirror —
two tight `b`-edges at `v p1` suffice, off the `4 * h0` diagonal bound. -/
theorem b_assumption_reduction_p21 (s : ScsV39) (k p1 : ℕ) (f : V3 → ℝ → V3)
    (v : ℕ → V3) (e : ℝ) (hs : isScsV39 s) (hk : s.k = k) (hBB : BBsV39 s v)
    (hk3 : 3 < k)
    (hdiag : ∀ i j, scsDiag k i j → 4 * h0 < s.b i j)
    (hd : Deformation f (Set.range v) (-e) e)
    (hfr : ∀ w t, w ≠ v p1 → f w t = w)
    (hb1 : ∃ e1, 0 < e1 ∧ (dist (v p1) (v (p1 + 1)) = s.b p1 (p1 + 1) →
      ∀ t, |t| < e1 → dist (f (v p1) t) (f (v (p1 + 1)) t) ≤ s.b p1 (p1 + 1)))
    (hb2 : ∃ e1, 0 < e1 ∧ (dist (v p1) (v (p1 + (k - 1))) = s.b p1 (p1 + (k - 1)) →
      ∀ t, |t| < e1 → dist (f (v p1) t) (f (v (p1 + (k - 1))) t) ≤
        s.b p1 (p1 + (k - 1)))) :
    ∀ i j, ∃ e1, 0 < e1 ∧ (dist (v i) (v j) = s.b i j →
      ∀ t, |t| < e1 → dist (f (v i) t) (f (v j) t) ≤ s.b i j) := by
  -- PROVED: the `a`-proof over the b-slots, the diagonal case closed by the
  -- `4 * h0` triangle bound on the annulus (`BBsV39` ball-annulus).

  have hsK := hs
  have _ := hd
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpb0, -, hsym, -, -, -, -, -, -, -, -⟩ := hs
  have hkne : k ≠ 0 := by omega
  have hpb : Periodic2 s.b k := hk ▸ hpb0
  have hperv : Periodic v k := hk ▸ hBB.2.1
  have hvmod : ∀ i, v (i % k) = v i := fun i => periodic_mod_p21 hkne hperv i
  have hinjmod : ∀ i j, v (i % k) = v (j % k) → i % k = j % k :=
    fun i j h => BBs_inj_p21 s v k hsK hk hBB (i % k) (j % k)
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h
  have hp1ne : p1 % k ≠ (p1 + 1) % k := fun h =>
    add_mod_ne_p21 p1 1 k one_pos (by omega) h.symm
  have hp1ne' : p1 % k ≠ (p1 + (k - 1)) % k := fun h =>
    add_mod_ne_p21 p1 (k - 1) k (by omega) (by omega) h.symm
  have hbmod : ∀ i j, s.b i j = s.b (i % k) (j % k) := fun i j =>
    periodic2_MOD_p21 (a := s.b) (i := i) (j := j) (k := k) hkne hpb
  have hnorm : ∀ i, dist (v i) 0 ≤ 2 * h0 := fun i =>
    (hBB.1 (Set.mem_range_self i)).1
  -- the p1-anchored claim (`j < k`)
  have hclaim : ∀ j, j < k → ∃ e1, 0 < e1 ∧ (dist (v p1) (v j) = s.b p1 j →
      ∀ t, |t| < e1 → dist (f (v p1) t) (f (v j) t) ≤ s.b p1 j) := by
    intro j hj
    by_cases hdj : scsDiag k p1 j
    · have hlt := hdiag p1 j hdj
      have htri : dist (v p1) (v j) ≤ 4 * h0 := by
        have h1 := dist_triangle (v p1) 0 (v j)
        have h2 := hnorm p1
        have h3 : dist 0 (v j) ≤ 2 * h0 := by rw [dist_comm]; exact hnorm j
        linarith
      exact ⟨1, one_pos, fun heq => absurd heq (ne_of_lt (by linarith))⟩
    · have hcase : p1 % k = j % k ∨ (p1 + 1) % k = j % k ∨ p1 % k = (j + 1) % k := by
        unfold scsDiag at hdj
        tauto
      rcases hcase with hA | hB | hC
      · -- j ≡ p1: distance 0 on both sides
        refine ⟨1, one_pos, ?_⟩
        intro heq
        have hvj : v j = v p1 := by rw [← hvmod j, ← hvmod p1, hA]
        intro t ht
        rw [hvj] at heq ⊢
        rw [dist_self] at heq ⊢
        rw [← heq]
      · -- j ≡ p1 + 1: use hb1
        obtain ⟨e1, he1, hb⟩ := hb1
        refine ⟨e1, he1, ?_⟩
        intro heq
        have hvj : v j = v (p1 + 1) := by rw [← hvmod j, ← hvmod (p1 + 1), hB]
        have hbj : s.b p1 j = s.b p1 (p1 + 1) := by
          rw [hbmod p1 j, hbmod p1 (p1 + 1), hB]
        intro t ht
        rw [hvj, hbj] at heq ⊢
        exact hb heq t ht
      · -- j ≡ p1 + k - 1: use hb2
        obtain ⟨e1, he1, hb⟩ := hb2
        refine ⟨e1, he1, ?_⟩
        intro heq
        have hjk : j % k = (p1 + (k - 1)) % k := by
          have h := MOD_SHIFT_p21 k p1 (j + 1) (k - 1) hkne hC
          rw [show j + 1 + (k - 1) = j + k by omega, Nat.add_mod_right] at h
          exact h.symm
        have hvj : v j = v (p1 + (k - 1)) := by
          rw [← hvmod j, ← hvmod (p1 + (k - 1)), hjk]
        have hbj : s.b p1 j = s.b p1 (p1 + (k - 1)) := by
          rw [hbmod p1 j, hbmod p1 (p1 + (k - 1)), hjk]
        intro t ht
        rw [hvj, hbj] at heq ⊢
        exact hb heq t ht
  -- assembly for `i, j < k`
  have hbounded : ∀ i j, i < k → j < k → ∃ e1,
      0 < e1 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e1 → dist (f (v i) t) (f (v j) t) ≤ s.b i j) := by
    intro i j hi hj
    by_cases hi1 : i % k = p1 % k
    · obtain ⟨e1, he1, hb⟩ := hclaim j hj
      refine ⟨e1, he1, ?_⟩
      intro heq
      have hvi : v i = v p1 := by rw [← hvmod i, ← hvmod p1, hi1]
      have hbi : s.b i j = s.b p1 j := by rw [hbmod i j, hbmod p1 j, hi1]
      intro t ht
      rw [hvi, hbi] at heq ⊢
      exact hb heq t ht
    · by_cases hj1 : j % k = p1 % k
      · obtain ⟨e1, he1, hb⟩ := hclaim i hi
        refine ⟨e1, he1, ?_⟩
        intro heq
        have hvj : v j = v p1 := by rw [← hvmod j, ← hvmod p1, hj1]
        have hbji : s.b i j = s.b p1 i := by
          calc s.b i j = s.b (i % k) (j % k) := hbmod i j
            _ = s.b (i % k) (p1 % k) := by rw [hj1]
            _ = s.b (p1 % k) (i % k) := (hsym (i % k) (p1 % k)).2.2.2.1
            _ = s.b p1 i := (hbmod p1 i).symm
        intro t ht
        rw [hvj, hbji] at heq ⊢
        have hble := hb (by rw [dist_comm]; exact heq) t ht
        rwa [dist_comm] at hble
      · refine ⟨1, one_pos, ?_⟩
        intro heq
        have hvi : v i ≠ v p1 := by
          intro hve
          exact hi1 (hinjmod i p1 (by rw [hvmod i, hvmod p1]; exact hve))
        have hvj : v j ≠ v p1 := by
          intro hve
          exact hj1 (hinjmod j p1 (by rw [hvmod j, hvmod p1]; exact hve))
        intro t ht
        rw [hfr (v i) t hvi, hfr (v j) t hvj]
        exact le_of_eq heq
  have hP : ∀ a b, (∃ e1, 0 < e1 ∧ (dist (v a) (v b) = s.b a b →
        ∀ t, |t| < e1 → dist (f (v a) t) (f (v b) t) ≤ s.b a b)) =
      (∃ e1, 0 < e1 ∧ (dist (v (a % k)) (v (b % k)) = s.b (a % k) (b % k) →
        ∀ t, |t| < e1 → dist (f (v (a % k)) t) (f (v (b % k)) t) ≤ s.b (a % k) (b % k))) := by
    intro a b
    rw [hbmod a b, hvmod a, hvmod b]
  intro i j
  refine periodic2_mod_reduce
    (P := fun i j => ∃ e1, 0 < e1 ∧ (dist (v i) (v j) = s.b i j →
      ∀ t, |t| < e1 → dist (f (v i) t) (f (v j) t) ≤ s.b i j))
    k hkne ?_ ?_ i j
  · intro i j
    show (∃ e1, 0 < e1 ∧ (dist (v (i + k)) (v j) = s.b (i + k) j →
        ∀ t, |t| < e1 → dist (f (v (i + k)) t) (f (v j) t) ≤ s.b (i + k) j)) =
      (∃ e1, 0 < e1 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e1 → dist (f (v i) t) (f (v j) t) ≤ s.b i j)) ∧
      (∃ e1, 0 < e1 ∧ (dist (v i) (v (j + k)) = s.b i (j + k) →
        ∀ t, |t| < e1 → dist (f (v i) t) (f (v (j + k)) t) ≤ s.b i (j + k))) =
      (∃ e1, 0 < e1 ∧ (dist (v i) (v j) = s.b i j →
        ∀ t, |t| < e1 → dist (f (v i) t) (f (v j) t) ≤ s.b i j))
    exact ⟨by rw [hP (i + k) j, hP i j, Nat.add_mod_right],
      by rw [hP i (j + k), hP i j, Nat.add_mod_right]⟩
  · exact fun i j hij => hbounded i j hij.1 hij.2

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
        (azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi →
        ∀ t, |t| < e0 →
          azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) ≤ Real.pi)) ∧
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
  -- PROVED: HOL proof ported piecewise: (A1)/(A2) are
  -- `vv_split_azim_alt_p21` instances, (A3)-(A6) the frozen/mod-class
  -- rewrites, (A7) the flat-`π` skolem chain, (A8) the two azimuth
  -- splits via `w_nwshjt_p21` + `sum3_azim_fan` /
  -- `azim_dominated_split_p21`, (A9) the frozen neighbours.

  have hkne : k ≠ 0 := by omega
  have hk3' : 3 ≤ k := by omega
  have hperv : Periodic v k := hk ▸ hBB.2.1
  have hsub : Set.range v ⊆ ballAnnulus := hBB.1
  have hcf : ConvexLocalFan (Set.range v) (Set.range fun i => {v i, v (i + 1)})
      (Set.range fun i => (v i, v (i + 1))) := by
    rcases hBB.2.2.2 with h3k | h
    · omega
    · exact h
  have hinj : ∀ a b, a < k → b < k → v a = v b → a = b :=
    fun a b ha hb => BBs_inj_p21 s v k hs hk hBB a b ha hb
  have hinj' : ∀ a b, a < k ∧ b < k ∧ v a = v b → a = b :=
    fun a b h => hinj a b h.1 h.2.1 h.2.2
  have hvmod : ∀ i, v (i % k) = v i := fun i => periodic_mod_p21 hkne hperv i
  have hinjmod : ∀ i j, v (i % k) = v (j % k) → i % k = j % k :=
    fun i j h => hinj (i % k) (j % k) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h
  have hncol : ∀ a b, a < k → b < k → a ≠ b → ¬ Collinear ℝ ({0, v a, v b} : Set V3) := by
    intro a b ha hb hab
    have hne : v a ≠ v b := fun h => hab (hinj a b ha hb h)
    exact PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 (Set.range v)
      (Set.range fun i => {v i, v (i + 1)}) (Set.range fun i => (v i, v (i + 1)))
      (v a) (v b) hcf.1 ⟨a, rfl⟩ ⟨b, rfl⟩ hne hgen
  have hncolmod : ∀ a b, a % k ≠ b % k → ¬ Collinear ℝ ({0, v a, v b} : Set V3) := by
    intro a b hab
    have h := hncol (a % k) (b % k) (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hab
    rwa [hvmod a, hvmod b] at h
  -- mod-k distinctness toolkit
  have hne_add : ∀ a c : ℕ, 0 < c → c < k → a % k ≠ (a + c) % k :=
    fun a c hc0 hck h => add_mod_ne_p21 a c k hc0 hck h.symm
  have hp1ne : p1 % k ≠ (p1 + 1) % k := hne_add p1 1 one_pos (by omega)
  have hp1ne2 : p1 % k ≠ (p1 + 2) % k := hne_add p1 2 (by norm_num) (by omega)
  have hp1ne_k1 : p1 % k ≠ (p1 + (k - 1)) % k := hne_add p1 (k - 1) (by omega) (by omega)
  have hp1ne_k2 : p1 % k ≠ (p1 + (k - 2)) % k := hne_add p1 (k - 2) (by omega) (by omega)
  have hne_add_1 : ∀ a : ℕ, a % k ≠ (a + 1) % k :=
    fun a => hne_add a 1 one_pos (by omega)
  have hne_add_k1 : ∀ a : ℕ, a % k ≠ (a + k - 1) % k := by
    intro a
    have h : a + k - 1 = a + (k - 1) := by omega
    rw [h]
    exact hne_add a (k - 1) (by omega) (by omega)
  have hsucc_ne_k1 : (p1 + (k - 1)) % k ≠ (p1 + 1) % k := by
    have hkk : p1 + (k - 1) = (p1 + 1) + (k - 2) := by omega
    rw [hkk]
    exact (hne_add (p1 + 1) (k - 2) (by omega) (by omega)).symm
  have hne_k1_k2 : (p1 + (k - 1)) % k ≠ (p1 + (k - 2)) % k := by
    have hkk : (p1 + (k - 2)) + 1 = p1 + (k - 1) := by omega
    rw [← hkk]
    exact (hne_add (p1 + (k - 2)) 1 one_pos (by omega)).symm
  have hp1dx : (p1 + 1) % k ≠ ((p1 + 1) + k - 1) % k := by
    have h : (p1 + 1) + k - 1 = p1 + k := by omega
    rw [h, Nat.add_mod_right]
    exact fun hh => hp1ne hh.symm
  have hne_of_mod : ∀ a, p1 % k ≠ a % k → v a ≠ v p1 := by
    intro a ha hve
    exact ha (hinjmod a p1 (by rw [hvmod a, hvmod p1]; exact hve)).symm
  -- index facts for the two splits
  have i1 : (p1 + (k - 1)) + 1 = p1 + k := by omega
  have i2 : (p1 + (k - 1)) + k - 1 = p1 + (k - 2) + k := by omega
  have j1 : (p1 + 1) + 1 = p1 + 2 := by omega
  have j2 : (p1 + 1) + k - 1 = p1 + k := by omega
  -- (A1)
  have hA1 : azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + (k - 2))) =
      azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) +
        azim 0 (v (p1 + (k - 1))) (v (p1 + 1)) (v (p1 + (k - 2))) := by
    have hsplit := vv_split_azim_alt_p21 v k (p1 + (k - 1)) (p1 + 1) hperv hk3'
      (hncolmod (p1 + (k - 1)) (p1 + 1) hsucc_ne_k1)
      (hncolmod (p1 + (k - 1)) ((p1 + (k - 1)) + k - 1) (hne_add_k1 (p1 + (k - 1))))
      (hncolmod (p1 + (k - 1)) ((p1 + (k - 1)) + 1) (hne_add_1 (p1 + (k - 1))))
      hcf hinj
    simpa only [i1, i2, hperv p1, hperv (p1 + (k - 2))] using hsplit
  -- (A2)
  have hA2 : azim 0 (v (p1 + 1)) (v (p1 + 2)) (v p1) =
      azim 0 (v (p1 + 1)) (v (p1 + 2)) (v (p1 + (k - 1))) +
        azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1) := by
    have hsplit := vv_split_azim_alt_p21 v k (p1 + 1) (p1 + (k - 1)) hperv hk3'
      (hncolmod (p1 + 1) (p1 + (k - 1)) hsucc_ne_k1.symm)
      (hncolmod (p1 + 1) ((p1 + 1) + k - 1) hp1dx)
      (hncolmod (p1 + 1) ((p1 + 1) + 1) (hne_add_1 (p1 + 1)))
      hcf hinj
    simpa only [j1, j2, hperv p1] using hsplit
  -- (A3)
  have hA3 : ∀ i t, p1 % k ≠ i % k → p1 % k ≠ (i + 1) % k →
      p1 % k ≠ (i + (k - 1)) % k →
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) =
        azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) := by
    intro i t h1' h2' h3'
    rw [hfr (v i) t (hne_of_mod i h1'), hfr (v (i + 1)) t (hne_of_mod (i + 1) h2'),
      hfr (v (i + (k - 1))) t (hne_of_mod (i + (k - 1)) h3')]
  -- (A4)
  have hA4 : ∀ i t, p1 % k = i % k →
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) =
        azim 0 (f (v p1) t) (v (p1 + 1)) (v (p1 + (k - 1))) := by
    intro i t h
    have hvi : v i = v p1 := by rw [← hvmod i, ← hvmod p1, h]
    have h1mod : (i + 1) % k = (p1 + 1) % k := MOD_SHIFT_p21 k i p1 1 hkne h.symm
    have h2mod : (i + (k - 1)) % k = (p1 + (k - 1)) % k :=
      MOD_SHIFT_p21 k i p1 (k - 1) hkne h.symm
    have hv1 : v (i + 1) = v (p1 + 1) := by rw [← hvmod (i + 1), ← hvmod (p1 + 1), h1mod]
    have hv2 : v (i + (k - 1)) = v (p1 + (k - 1)) := by
      rw [← hvmod (i + (k - 1)), ← hvmod (p1 + (k - 1)), h2mod]
    rw [hvi, hv1, hv2, hfr (v (p1 + 1)) t (hne_of_mod (p1 + 1) hp1ne),
      hfr (v (p1 + (k - 1))) t (hne_of_mod (p1 + (k - 1)) hp1ne_k1)]
  -- (A5)
  have hA5 : ∀ i t, p1 % k = (i + 1) % k →
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) =
        azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + (k - 2))) := by
    intro i t h
    have himod : i % k = (p1 + (k - 1)) % k := by
      have hh := MOD_SHIFT_p21 k p1 (i + 1) (k - 1) hkne h
      rw [show i + 1 + (k - 1) = i + k by omega, Nat.add_mod_right] at hh
      exact hh.symm
    have h1mod : (i + (k - 1)) % k = (p1 + (k - 2)) % k := by
      have hh := MOD_SHIFT_p21 k p1 (i + 1) (k - 2) hkne h
      rw [show i + 1 + (k - 2) = i + (k - 1) by omega] at hh
      exact hh.symm
    have hvi : v i = v (p1 + (k - 1)) := by rw [← hvmod i, ← hvmod (p1 + (k - 1)), himod]
    have hv1 : v (i + 1) = v p1 := by rw [← hvmod (i + 1), ← hvmod p1, h]
    have hv2 : v (i + (k - 1)) = v (p1 + (k - 2)) := by
      rw [← hvmod (i + (k - 1)), ← hvmod (p1 + (k - 2)), h1mod]
    rw [hvi, hv1, hv2, hfr (v (p1 + (k - 1))) t (hne_of_mod (p1 + (k - 1)) hp1ne_k1),
      hfr (v (p1 + (k - 2))) t (hne_of_mod (p1 + (k - 2)) hp1ne_k2)]
  -- (A6)
  have hA6 : ∀ i t, p1 % k = (i + (k - 1)) % k →
      azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) =
        azim 0 (v (p1 + 1)) (v (p1 + 2)) (f (v p1) t) := by
    intro i t h
    have himod : i % k = (p1 + 1) % k := by
      have hh := MOD_SHIFT_p21 k p1 (i + (k - 1)) 1 hkne h
      rw [show i + (k - 1) + 1 = i + k by omega, Nat.add_mod_right] at hh
      exact hh.symm
    have h1mod : (i + 1) % k = (p1 + 2) % k := by
      have hh := MOD_SHIFT_p21 k p1 (i + (k - 1)) 2 hkne h
      rw [show i + (k - 1) + 2 = (i + 1) + k by omega, Nat.add_mod_right] at hh
      exact hh.symm
    have hv0 : v i = v (p1 + 1) := by rw [← hvmod i, ← hvmod (p1 + 1), himod]
    have hv1 : v (i + 1) = v (p1 + 2) := by rw [← hvmod (i + 1), ← hvmod (p1 + 2), h1mod]
    have hv2 : v (i + (k - 1)) = v p1 := by rw [← hvmod (i + (k - 1)), ← hvmod p1, h]
    rw [hv0, hv1, hv2, hfr (v (p1 + 1)) t (hne_of_mod (p1 + 1) hp1ne),
      hfr (v (p1 + 2)) t (hne_of_mod (p1 + 2) hp1ne2)]
  -- (A9)
  have hA9 : ∀ t, f (v (p1 + 1)) t = v (p1 + 1) ∧
      f (v (p1 + (k - 1))) t = v (p1 + (k - 1)) ∧
      f (v (p1 + (k - 2))) t = v (p1 + (k - 2)) ∧
      f (v (p1 + 2)) t = v (p1 + 2) := by
    intro t
    exact ⟨hfr _ t (hne_of_mod _ hp1ne), hfr _ t (hne_of_mod _ hp1ne_k1),
      hfr _ t (hne_of_mod _ hp1ne_k2), hfr _ t (hne_of_mod _ hp1ne2)⟩
  -- non-collinearity facts
  have hnP_ab : ¬ Collinear ℝ ({0, v (p1 + (k - 1)), v p1} : Set V3) :=
    hncolmod (p1 + (k - 1)) p1 hp1ne_k1.symm
  have hnP_ac : ¬ Collinear ℝ ({0, v (p1 + (k - 1)), v (p1 + 1)} : Set V3) :=
    hncolmod (p1 + (k - 1)) (p1 + 1) hsucc_ne_k1
  have hnP_ad : ¬ Collinear ℝ ({0, v (p1 + (k - 1)), v (p1 + (k - 2))} : Set V3) :=
    hncolmod (p1 + (k - 1)) (p1 + (k - 2)) hne_k1_k2
  have hnQ_ab : ¬ Collinear ℝ ({0, v (p1 + 1), v (p1 + (k - 1))} : Set V3) :=
    hncolmod (p1 + 1) (p1 + (k - 1)) hsucc_ne_k1.symm
  have hnQ_ac : ¬ Collinear ℝ ({0, v (p1 + 1), v p1} : Set V3) :=
    hncolmod (p1 + 1) p1 hp1ne.symm
  have hnQ_ad : ¬ Collinear ℝ ({0, v (p1 + 1), v (p1 + 2)} : Set V3) :=
    hncolmod (p1 + 1) (p1 + 2) (hne_add (p1 + 1) 1 one_pos (by omega))
  -- non-coplanarity in the two permuted forms
  have hcop1 : ¬ Coplanar ({0, v (p1 + (k - 1)), v p1, v (p1 + 1)} : Set V3) := by
    intro h
    apply hnc
    have hset : ({0, v (p1 + (k - 1)), v p1, v (p1 + 1)} : Set V3) =
        {0, v p1, v (p1 + 1), v (p1 + (k - 1))} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset] at h
  have hcop2 : ¬ Coplanar ({0, v (p1 + 1), v (p1 + (k - 1)), v p1} : Set V3) := by
    intro h
    apply hnc
    have hset : ({0, v (p1 + 1), v (p1 + (k - 1)), v p1} : Set V3) =
        {0, v p1, v (p1 + 1), v (p1 + (k - 1))} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset] at h
  have hAbase_pos : 0 < azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) := by
    rw [azim_pos_iff_nz_p14]
    intro h0
    exact hcop1 ((AZIM_COND_FOR_COPLANAR 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1))).mp (Or.inl h0))
  have hA2base_pos : 0 < azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1) := by
    rw [azim_pos_iff_nz_p14]
    intro h0
    exact hcop2 ((AZIM_COND_FOR_COPLANAR 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1)).mp (Or.inl h0))
  -- continuity bookkeeping for the moving point
  have hcont_move : ContinuousAt (fun t => f (v p1) t) 0 := hd.2.1 (v p1) ⟨p1, rfl⟩ 0 hd.1
  have hfix0 : f (v p1) 0 = v p1 := hd.2.2 (v p1) ⟨p1, rfl⟩
  have hdynP : ∃ ec, 0 < ec ∧ ∀ t, |t| < ec →
      ¬ Collinear3 0 (v (p1 + (k - 1))) (f (v p1) t) := by
    have hbase : ¬ Collinear3 0 (v (p1 + (k - 1))) (f (v p1) 0) := by
      rw [hfix0]
      exact hnP_ab
    have h := CONTINUOUS_PRESERVE_COLLINEAR 0 (fun _ => v (p1 + (k - 1)))
      (fun t => f (v p1) t) 0 continuousAt_const hcont_move hbase
    simpa using h
  have hdynQ : ∃ ec, 0 < ec ∧ ∀ t, |t| < ec →
      ¬ Collinear3 0 (v (p1 + 1)) (f (v p1) t) := by
    have hbase : ¬ Collinear3 0 (v (p1 + 1)) (f (v p1) 0) := by
      rw [hfix0]
      exact hnQ_ac
    have h := CONTINUOUS_PRESERVE_COLLINEAR 0 (fun _ => v (p1 + 1))
      (fun t => f (v p1) t) 0 continuousAt_const hcont_move hbase
    simpa using h
  -- deformation restricted to the three relevant points
  have hdsubP : Deformation f ({v (p1 + 1), v (p1 + (k - 1)), v p1} : Set V3) (-e) e := by
    refine deformation_subset_p14 f _ (Set.range v) (-e) e ?_ hd
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Set.mem_range_self (p1 + 1)
    · exact Set.mem_range_self (p1 + (k - 1))
    · exact Set.mem_range_self p1
  have hdsubQ : Deformation f ({v p1, v (p1 + 1), v (p1 + (k - 1))} : Set V3) (-e) e := by
    refine deformation_subset_p14 f _ (Set.range v) (-e) e ?_ hd
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Set.mem_range_self p1
    · exact Set.mem_range_self (p1 + 1)
    · exact Set.mem_range_self (p1 + (k - 1))
  -- the first split claim (with the `≤ π` half)
  have hPclaim : ∃ e1, 0 < e1 ∧ ∀ t, |t| < e1 →
      azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + (k - 2))) =
        azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + 1)) +
          azim 0 (v (p1 + (k - 1))) (v (p1 + 1)) (v (p1 + (k - 2))) ∧
      azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + (k - 2))) ≤ Real.pi := by
    have hFULLle : azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + (k - 2))) ≤ Real.pi := by
      have h := convex_local_fan_azim_le_pi v k (p1 + (k - 1)) hperv hk3' hinj' hcf hsub
      simpa only [i1, i2, hperv p1, hperv (p1 + (k - 2))] using h
    rcases h1 with hlt | ⟨e1b, he1b, hbound⟩
    · obtain ⟨ec, hec, hcnc⟩ := hdynP
      have hwn := w_nwshjt_p21 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1) f (-e) e
        (Real.pi - azim 0 (v (p1 + (k - 1))) (v (p1 + 1)) (v (p1 + (k - 2))))
        hdsubP hnP_ab hnP_ac hAbase_pos (by linarith)
      obtain ⟨ew, hew, hw⟩ := hwn
      refine ⟨min ew ec, lt_min hew hec, fun t ht => ?_⟩
      have hwt := hw t (lt_of_lt_of_le ht (min_le_left _ _))
      have hct := hcnc t (lt_of_lt_of_le ht (min_le_right _ _))
      rw [hA9 t |>.1, hA9 t |>.2.1] at hwt
      have hxv : v (p1 + (k - 1)) ≠ 0 := by
        intro h0
        apply hnP_ab
        rw [h0]
        have hset : ({0, 0, v p1} : Set V3) = {0, v p1} := by
          ext x
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [hset]
        exact collinear_pair ℝ 0 (v p1)
      have hlt2 : azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + 1)) +
          azim 0 (v (p1 + (k - 1))) (v (p1 + 1)) (v (p1 + (k - 2))) < 2 * Real.pi := by
        have hp := Real.pi_pos
        linarith [hwt.2]
      have hsum := sum3_azim_fan (x := (0 : V3)) (v := v (p1 + (k - 1)))
        (u := f (v p1) t) (w1 := v (p1 + 1)) (w2 := v (p1 + (k - 2)))
        hxv hct hnP_ac hnP_ad hlt2
      exact ⟨hsum, by rw [hsum]; linarith [hwt.2]⟩
    · obtain ⟨ec, hec, hcnc⟩ := hdynP
      refine ⟨min e1b ec, lt_min he1b hec, fun t ht => ?_⟩
      have hbd := hbound t (lt_of_lt_of_le ht (min_le_left _ _))
      have hct := hcnc t (lt_of_lt_of_le ht (min_le_right _ _))
      have hsplit := azim_dominated_split_p21 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1))
        (v (p1 + (k - 2))) 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + 1)) (v (p1 + (k - 2)))
        hnP_ac hnP_ad hct hA1.symm hbd (le_refl _)
      exact ⟨hsplit.symm, by rw [← hsplit]; linarith⟩
  -- the second split claim (with the `≤ π` half)
  have hQclaim : ∃ e1, 0 < e1 ∧ ∀ t, |t| < e1 →
      azim 0 (v (p1 + 1)) (v (p1 + 2)) (f (v p1) t) =
        azim 0 (v (p1 + 1)) (v (p1 + 2)) (v (p1 + (k - 1))) +
          azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t) ∧
      azim 0 (v (p1 + 1)) (v (p1 + 2)) (f (v p1) t) ≤ Real.pi := by
    have hFULL2le : azim 0 (v (p1 + 1)) (v (p1 + 2)) (v p1) ≤ Real.pi := by
      have h := convex_local_fan_azim_le_pi v k (p1 + 1) hperv hk3' hinj' hcf hsub
      simpa only [j1, j2, hperv p1] using h
    rcases h2 with hlt | ⟨e2b, he2b, hbound⟩
    · obtain ⟨ec, hec, hcnc⟩ := hdynQ
      have hwn := w_nwshjt_p21 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) f (-e) e
        (Real.pi - azim 0 (v (p1 + 1)) (v (p1 + 2)) (v (p1 + (k - 1))))
        hdsubQ hnQ_ab hnQ_ac hA2base_pos (by linarith)
      obtain ⟨ew, hew, hw⟩ := hwn
      refine ⟨min ew ec, lt_min hew hec, fun t ht => ?_⟩
      have hwt := hw t (lt_of_lt_of_le ht (min_le_left _ _))
      have hct := hcnc t (lt_of_lt_of_le ht (min_le_right _ _))
      rw [hA9 t |>.1, hA9 t |>.2.1] at hwt
      have hxv : v (p1 + 1) ≠ 0 := by
        intro h0
        apply hnQ_ac
        rw [h0]
        have hset : ({0, 0, v p1} : Set V3) = {0, v p1} := by
          ext x
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          tauto
        rw [hset]
        exact collinear_pair ℝ 0 (v p1)
      have hlt2 : azim 0 (v (p1 + 1)) (v (p1 + 2)) (v (p1 + (k - 1))) +
          azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t) < 2 * Real.pi := by
        have hp := Real.pi_pos
        linarith [hwt.2]
      have hsum := sum3_azim_fan (x := (0 : V3)) (v := v (p1 + 1))
        (u := v (p1 + 2)) (w1 := v (p1 + (k - 1))) (w2 := f (v p1) t)
        hxv hnQ_ad hnQ_ab hct hlt2
      exact ⟨hsum, by rw [hsum]; linarith [hwt.2]⟩
    · obtain ⟨ec, hec, hcnc⟩ := hdynQ
      refine ⟨min e2b ec, lt_min he2b hec, fun t ht => ?_⟩
      have hbd := hbound t (lt_of_lt_of_le ht (min_le_left _ _))
      have hct := hcnc t (lt_of_lt_of_le ht (min_le_right _ _))
      have hsplit := azim_dominated_split_p21 0 (v (p1 + 1)) (v (p1 + 2))
        (v (p1 + (k - 1))) (v p1) 0 (v (p1 + 1)) (v (p1 + 2)) (v (p1 + (k - 1)))
        (f (v p1) t) hnQ_ab hct hnQ_ad hA2.symm (le_refl _) hbd
      exact ⟨hsplit.symm, by rw [← hsplit]; linarith⟩
  -- (A8)
  have hA8 : ∃ e1, 0 < e1 ∧ ∀ t, |t| < e1 →
      azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + (k - 2))) =
        azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + 1)) +
          azim 0 (v (p1 + (k - 1))) (v (p1 + 1)) (v (p1 + (k - 2))) ∧
      azim 0 (v (p1 + 1)) (v (p1 + 2)) (f (v p1) t) =
        azim 0 (v (p1 + 1)) (v (p1 + 2)) (v (p1 + (k - 1))) +
          azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t) := by
    obtain ⟨eP, heP, hP⟩ := hPclaim
    obtain ⟨eQ, heQ, hQ⟩ := hQclaim
    obtain ⟨e', he', h1e, h2e⟩ := epsilon_pair_p21 eP eQ heP heQ
    exact ⟨e', he', fun t ht => ⟨(hP t (h1e t ht)).1, (hQ t (h2e t ht)).1⟩⟩
  -- (A7)
  have hA7 : ∀ i, ∃ e0, 0 < e0 ∧
      (azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi →
      ∀ t, |t| < e0 →
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) ≤ Real.pi) := by
    intro i
    by_cases hcase : p1 % k ≠ i % k ∧ p1 % k ≠ (i + 1) % k ∧
        p1 % k ≠ (i + (k - 1)) % k
    · refine ⟨1, one_pos, ?_⟩
      intro hh t ht
      rw [hA3 i t hcase.1 hcase.2.1 hcase.2.2, hh]
    · have hcase' : p1 % k = i % k ∨ p1 % k = (i + 1) % k ∨
          p1 % k = (i + (k - 1)) % k := by
        rcases Classical.em (p1 % k = i % k) with hA | hA
        · exact Or.inl hA
        rcases Classical.em (p1 % k = (i + 1) % k) with hB | hB
        · exact Or.inr (Or.inl hB)
        rcases Classical.em (p1 % k = (i + (k - 1)) % k) with hC | hC
        · exact Or.inr (Or.inr hC)
        · exact absurd ⟨hA, hB, hC⟩ hcase
      rcases hcase' with hA | hB | hC
      · refine ⟨1, one_pos, ?_⟩
        intro hh
        exfalso
        have hcong1 : v i = v p1 := by rw [← hvmod i, ← hvmod p1, hA]
        have hcong2 : v (i + 1) = v (p1 + 1) := by
          rw [← hvmod (i + 1), ← hvmod (p1 + 1), MOD_SHIFT_p21 k i p1 1 hkne hA.symm]
        have hcong3 : v (i + (k - 1)) = v (p1 + (k - 1)) := by
          rw [← hvmod (i + (k - 1)), ← hvmod (p1 + (k - 1)),
            MOD_SHIFT_p21 k i p1 (k - 1) hkne hA.symm]
        rw [hcong1, hcong2, hcong3] at hh
        linarith [hz, hh]
      · obtain ⟨eP, heP, hP⟩ := hPclaim
        refine ⟨eP, heP, ?_⟩
        intro _ t ht
        rw [hA5 i t hB]
        exact (hP t ht).2
      · obtain ⟨eQ, heQ, hQ⟩ := hQclaim
        refine ⟨eQ, heQ, ?_⟩
        intro _ t ht
        rw [hA6 i t hC]
        exact (hQ t ht).2
  exact ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9⟩

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
  -- PROVED: azimuth continuity (`w5cA3_continuousAt_azim`) + persistence
  -- of positivity/bound via `continuous_nbd_pos_p21` (`w_nwshjt_p21`).
  exact w_nwshjt_p21 w0 w1 w2 f a b c hd h1 h2 h3 h4

/-! ## Section G: obtuse-monotonicity kit -/

section GKit

open Filter
open scoped Topology

/-! ### Private re-derivation of the `dih_x` analytic kit

HOL consumes `Ocbicby.derived_form_dih_x_wrt_x5` (the slot-5 derivative
`−√x1·Δ₆/(ups_x x1 x3 x5·√Δ)`) and `Tame_inequalities.DIH_X_MONO_LT_4`
(slot-4 monotonicity).  Neither kit is available on this side, so both are
re-derived here from the canonical `SphereKit` definitions and Mathlib's
mean value theorem.  All helpers are `private`. -/

/-- `atn2 A B = arctan (B/A)` on the right half-plane `A > 0` (HOL
`Trigonometry1.ATN2_BREAKDOWN`, first clause). -/
private theorem g_atn2_eq_arctan {A B : ℝ} (hA : 0 < A) :
    atn2 A B = Real.arctan (B / A) := by
  unfold atn2
  by_cases hb : |B| < A
  · rw [if_pos hb]
  · rw [if_neg hb]
    rcases lt_trichotomy B 0 with hB | hB | hB
    · rw [if_neg (show ¬(0 : ℝ) < B from by linarith), if_pos hB]
      have hAB : A / B < 0 := by
        have h2 : A / B = -(A / (-B)) := by field_simp
        rw [h2, neg_lt_zero]
        exact div_pos hA (neg_pos.mpr hB)
      have hinv := Real.arctan_inv_of_neg hAB
      rw [inv_div] at hinv
      exact hinv.symm
    · exact absurd (show |B| < A by rw [hB]; simpa using hA) hb
    · rw [if_pos hB]
      have hinv := Real.arctan_inv_of_pos (div_pos hB hA)
      rw [inv_div] at hinv
      linarith

/-- `atn2 A B` on the lower-right half-plane (`A > 0`, `B < 0`). -/
private theorem g_atn2_of_neg {A B : ℝ} (hA : 0 < A) (hB : B < 0) :
    atn2 A B = -(Real.pi / 2) - Real.arctan (A / B) := by
  unfold atn2
  by_cases h1 : |B| < A
  · rw [if_pos h1]
    have hBA : B / A < 0 := div_neg_of_neg_of_pos hB hA
    have hrec : A / B = (B / A)⁻¹ := by field_simp [ne_of_lt hB]
    rw [hrec, Real.arctan_inv_of_neg hBA]
    ring
  · rw [if_neg h1]
    by_cases h2 : 0 < B
    · exact absurd h2 (not_lt.mpr hB.le)
    · rw [if_neg h2]
      by_cases h3 : B < 0
      · rw [if_pos h3]
      · exact absurd hB h3

/-- `atn2 A B` on the upper-right half-plane (`A > 0`, `B > 0`). -/
private theorem g_atn2_of_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    atn2 A B = Real.pi / 2 - Real.arctan (A / B) := by
  unfold atn2
  by_cases h1 : |B| < A
  · rw [if_pos h1]
    have hBA : 0 < B / A := div_pos hB hA
    have hrec : A / B = (B / A)⁻¹ := by field_simp [ne_of_gt hB]
    rw [hrec, Real.arctan_inv_of_pos hBA]
    ring
  · rw [if_neg h1]
    by_cases h2 : 0 < B
    · rw [if_pos h2]
    · exact absurd hB h2

/-- Derivative of `s ↦ atn2 (A s) (B s)` while `A s > 0` (all branches). -/
private theorem g_hasDerivAt_atn2 {A B : ℝ → ℝ} {A' B' t : ℝ}
    (hA : 0 < A t) (hA' : HasDerivAt A A' t) (hB' : HasDerivAt B B' t) :
    HasDerivAt (fun s => atn2 (A s) (B s))
      ((A t * B' - B t * A') / (A t ^ 2 + B t ^ 2)) t := by
  have hA2 : A t ^ 2 + B t ^ 2 ≠ 0 := by positivity
  rcases lt_trichotomy (B t) 0 with hneg | hzero | hpos
  · have hevA : ∀ᶠ s in 𝓝 t, 0 < A s :=
      hA'.continuousAt.eventually (isOpen_Ioi.mem_nhds hA)
    have hevB : ∀ᶠ s in 𝓝 t, B s < 0 :=
      hB'.continuousAt.eventually_lt continuousAt_const hneg
    have heq : (fun s => atn2 (A s) (B s)) =ᶠ[𝓝 t]
        (fun s => -(Real.pi / 2) - Real.arctan (A s / B s)) := by
      filter_upwards [hevA, hevB] with s hsA hsB
      exact g_atn2_of_neg hsA hsB
    have hdiv : HasDerivAt (fun s => A s / B s) ((A' * B t - A t * B') / (B t) ^ 2) t :=
      hA'.div hB' (ne_of_lt hneg)
    have hmain : HasDerivAt (fun s => -(Real.pi / 2) - Real.arctan (A s / B s))
        (0 - (1 / (1 + (A t / B t) ^ 2)) * ((A' * B t - A t * B') / (B t) ^ 2)) t :=
      (hasDerivAt_const (x := t) (c := -(Real.pi / 2))).sub hdiv.arctan
    refine (hmain.congr_of_eventuallyEq heq).congr_deriv ?_
    field_simp [ne_of_lt hneg, hA2]
    ring
  · have hlt : |B t| < A t := by rw [hzero, abs_zero]; exact hA
    have hev : ∀ᶠ s in 𝓝 t, |B s| < A s :=
      (hB'.continuousAt.abs).eventually_lt hA'.continuousAt hlt
    have heq : (fun s => atn2 (A s) (B s)) =ᶠ[𝓝 t]
        (fun s => Real.arctan (B s / A s)) := by
      filter_upwards [hev] with s hs
      unfold atn2
      exact if_pos hs
    have hdiv : HasDerivAt (fun s => B s / A s) ((B' * A t - B t * A') / (A t) ^ 2) t :=
      hB'.div hA' (ne_of_gt hA)
    have hmain : HasDerivAt (fun s => Real.arctan (B s / A s))
        ((1 / (1 + (B t / A t) ^ 2)) * ((B' * A t - B t * A') / (A t) ^ 2)) t :=
      hdiv.arctan
    refine (hmain.congr_of_eventuallyEq heq).congr_deriv ?_
    field_simp [ne_of_gt hA, hA2]
  · have hevA : ∀ᶠ s in 𝓝 t, 0 < A s :=
      hA'.continuousAt.eventually (isOpen_Ioi.mem_nhds hA)
    have hevB : ∀ᶠ s in 𝓝 t, 0 < B s :=
      continuousAt_const.eventually_lt hB'.continuousAt hpos
    have heq : (fun s => atn2 (A s) (B s)) =ᶠ[𝓝 t]
        (fun s => Real.pi / 2 - Real.arctan (A s / B s)) := by
      filter_upwards [hevA, hevB] with s hsA hsB
      exact g_atn2_of_pos hsA hsB
    have hdiv : HasDerivAt (fun s => A s / B s) ((A' * B t - A t * B') / (B t) ^ 2) t :=
      hA'.div hB' (ne_of_gt hpos)
    have hmain : HasDerivAt (fun s => Real.pi / 2 - Real.arctan (A s / B s))
        (0 - (1 / (1 + (A t / B t) ^ 2)) * ((A' * B t - A t * B') / (B t) ^ 2)) t :=
      (hasDerivAt_const (x := t) (c := Real.pi / 2)).sub hdiv.arctan
    refine (hmain.congr_of_eventuallyEq heq).congr_deriv ?_
    field_simp [ne_of_gt hpos, hA2]
    ring

/-- Derivative of a quadratic, in the `a*(q*q) + (b*q+c)` normal form. -/
private theorem g_hasDerivAt_quad (a b c x : ℝ) :
    HasDerivAt (fun q : ℝ => a * (q * q) + (b * q + c)) (a * (x + x) + b) x := by
  have h1 : HasDerivAt (fun q : ℝ => q * q) (x + x) x := by
    exact HasDerivAt.congr_deriv
      ((hasDerivAt_id x).mul (hasDerivAt_id x)) (by norm_num)
  have h2 : HasDerivAt (fun q : ℝ => b * q + c) (b * 1 + 0) x :=
    ((hasDerivAt_id x).const_mul b).add (hasDerivAt_const (x := x) (c := c))
  exact HasDerivAt.congr_deriv ((h1.const_mul a).add h2) (by norm_num)

/-- Derivative of an affine function. -/
private theorem g_hasDerivAt_affine (a b x : ℝ) :
    HasDerivAt (fun q : ℝ => a * q + b) a x := by
  have h : HasDerivAt (fun q : ℝ => a * q + b) (a * 1 + 0) x :=
    ((hasDerivAt_id x).const_mul a).add (hasDerivAt_const (x := x) (c := b))
  exact HasDerivAt.congr_deriv h (by norm_num)

/-- `∂deltaX/∂x4` (HOL `Sphere.delta_x4`). -/
private theorem g_hasDerivAt_deltaX_x4 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX x1 x2 x3 t x5 x6) (deltaX4 x1 x2 x3 x4 x5 x6) x4 := by
  have h := g_hasDerivAt_quad (-x1)
    (x1 * (-x1 + x2 + x3 + x5 + x6) + (x2 * x5 + x3 * x6 - x2 * x3 - x5 * x6))
    (x2 * x5 * (x1 - x2 + x3 - x5 + x6) + x3 * x6 * (x1 + x2 - x3 + x5 - x6)
      - x1 * x3 * x5 - x1 * x2 * x6) x4
  have he : (fun t => deltaX x1 x2 x3 t x5 x6) = fun q => (-x1) * (q * q)
      + ((x1 * (-x1 + x2 + x3 + x5 + x6) + (x2 * x5 + x3 * x6 - x2 * x3 - x5 * x6)) * q
        + (x2 * x5 * (x1 - x2 + x3 - x5 + x6) + x3 * x6 * (x1 + x2 - x3 + x5 - x6)
          - x1 * x3 * x5 - x1 * x2 * x6)) := by
    funext q; unfold deltaX; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by simp only [deltaX4]; ring)

/-- `∂deltaX4/∂x4 = -2*x1`. -/
private theorem g_hasDerivAt_deltaX4_x4 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX4 x1 x2 x3 t x5 x6) (-2 * x1) x4 := by
  have h := g_hasDerivAt_affine (-2 * x1)
    (-x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6 + x1 * (-x1 + x2 + x3 + x5 + x6)) x4
  have he : (fun t => deltaX4 x1 x2 x3 t x5 x6) = fun q => (-2 * x1) * q
      + (-x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6 + x1 * (-x1 + x2 + x3 + x5 + x6)) := by
    funext q; unfold deltaX4; ring
  rw [he]; exact h

/-- `∂deltaX/∂x5` (HOL `Nonlin_def.delta_x5`; canonical `SphereKit.deltaX5`). -/
private theorem g_hasDerivAt_deltaX_x5 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX x1 x2 x3 x4 t x6) (deltaX5 x1 x2 x3 x4 x5 x6) x5 := by
  have h := g_hasDerivAt_quad (-x2)
    (x1 * x4 + x1 * x2 - x2 ^ 2 + x2 * x3 + x2 * x4 + x2 * x6 + x3 * x6 - x1 * x3 - x4 * x6)
    (x1 * x4 * (-x1 + x2 + x3 - x4 + x6) + x3 * x6 * (x1 + x2 - x3 + x4 - x6)
      - x2 * x3 * x4 - x1 * x2 * x6) x5
  have he : (fun t => deltaX x1 x2 x3 x4 t x6) = fun q => (-x2) * (q * q)
      + ((x1 * x4 + x1 * x2 - x2 ^ 2 + x2 * x3 + x2 * x4 + x2 * x6 + x3 * x6 - x1 * x3 - x4 * x6) * q
        + (x1 * x4 * (-x1 + x2 + x3 - x4 + x6) + x3 * x6 * (x1 + x2 - x3 + x4 - x6)
          - x2 * x3 * x4 - x1 * x2 * x6)) := by
    funext q; unfold deltaX; ring
  rw [he]
  exact HasDerivAt.congr_deriv h (by simp only [deltaX5]; ring)

/-- `∂deltaX4/∂x5 = x1 + x2 - x6`. -/
private theorem g_hasDerivAt_deltaX4_x5 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t => deltaX4 x1 x2 x3 x4 t x6) (x1 + x2 - x6) x5 := by
  have h := g_hasDerivAt_affine (x1 + x2 - x6)
    (-x2 * x3 - x1 * x4 + x3 * x6 + x1 * (-x1 + x2 + x3 - x4 + x6)) x5
  have he : (fun t => deltaX4 x1 x2 x3 x4 t x6) = fun q => (x1 + x2 - x6) * q
      + (-x2 * x3 - x1 * x4 + x3 * x6 + x1 * (-x1 + x2 + x3 - x4 + x6)) := by
    funext q; unfold deltaX4; ring
  rw [he]; exact h

/-- HOL `ups_x_delta_x`: `Δ₄² + 4·x₁·Δ = upsX x1 x3 x5 · upsX x1 x2 x6`. -/
private theorem g_ups_delta (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 + 4 * x1 * deltaX x1 x2 x3 x4 x5 x6
      = upsX x1 x3 x5 * upsX x1 x2 x6 := by
  simp only [deltaX, deltaX4, upsX]
  ring

/-- The slot-5 rationalisation identity that turns the raw arctan-derivative
numerator into `-2*x1*Δ₆`. -/
private theorem g_delta_ident_x5 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX4 x1 x2 x3 x4 x5 x6 * deltaX5 x1 x2 x3 x4 x5 x6
      + upsX x1 x2 x6 * deltaX6_p21 x1 x2 x3 x4 x5 x6
      = 2 * deltaX x1 x2 x3 x4 x5 x6 * (x1 + x2 - x6) := by
  simp only [deltaX, deltaX4, deltaX5, deltaX6_p21, upsX]
  ring

/-- Derivative of `x ↦ π/2 + atn2 (√(4*x1*f x)) (-(g x))`. -/
private theorem g_hasDerivAt_dihXf_aux {f g : ℝ → ℝ} {f' g' t x1 : ℝ}
    (hx1 : 0 < x1) (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t)
    (hfpos : 0 < f t) :
    HasDerivAt (fun s => Real.pi / 2 + atn2 (Real.sqrt (4 * x1 * f s)) (-(g s)))
      ((2 * x1 * g t * f' - 4 * x1 * f t * g')
        / (Real.sqrt (4 * x1 * f t) * (4 * x1 * f t + g t ^ 2))) t := by
  have hpos : 0 < 4 * x1 * f t := by positivity
  have hA : 0 < Real.sqrt (4 * x1 * f t) := Real.sqrt_pos.mpr hpos
  have hA' : HasDerivAt (fun s => Real.sqrt (4 * x1 * f s))
      (4 * x1 * f' / (2 * Real.sqrt (4 * x1 * f t))) t :=
    (hf.const_mul (4 * x1)).sqrt (ne_of_gt hpos)
  have hB' : HasDerivAt (fun s => -(g s)) (-g') t := hg.neg
  have h := (hasDerivAt_const (x := t) (c := Real.pi / 2)).add
    (g_hasDerivAt_atn2 hA hA' hB')
  refine h.congr_deriv ?_
  have hA2 : Real.sqrt (4 * x1 * f t) ^ 2 = 4 * x1 * f t := Real.sq_sqrt (le_of_lt hpos)
  have hA0 : Real.sqrt (4 * x1 * f t) ≠ 0 := ne_of_gt hA
  field_simp [hA0]
  rw [hA2]
  ring

/-- `∂dihXf/∂x4 = 2·x₁/√(4·x₁·Δ)`. -/
private theorem g_dihXf_hasDerivAt_x4 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu1 : 0 < upsX x1 x2 x6)
    (hu2 : 0 < upsX x1 x3 x5) :
    HasDerivAt (fun t => dihXf x1 x2 x3 t x5 x6)
      (2 * x1 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) x4 := by
  have h := g_hasDerivAt_dihXf_aux (x1 := x1) (t := x4)
    (f := fun t => deltaX x1 x2 x3 t x5 x6)
    (g := fun t => deltaX4 x1 x2 x3 t x5 x6)
    (f' := deltaX4 x1 x2 x3 x4 x5 x6) (g' := -2 * x1) hx1
    (g_hasDerivAt_deltaX_x4 x1 x2 x3 x4 x5 x6)
    (g_hasDerivAt_deltaX4_x4 x1 x2 x3 x4 x5 x6) hd
  have h' : HasDerivAt (fun t => dihXf x1 x2 x3 t x5 x6)
      ((2 * x1 * deltaX4 x1 x2 x3 x4 x5 x6 * deltaX4 x1 x2 x3 x4 x5 x6
          - 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (-2 * x1))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2))) x4 := by
    simpa only [dihXf] using h
  refine h'.congr_deriv ?_
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hE : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      = upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [add_comm, g_ups_delta, mul_comm]
  have hu126 : upsX x1 x2 x6 ≠ 0 := ne_of_gt hu1
  have hu135 : upsX x1 x3 x5 ≠ 0 := ne_of_gt hu2
  rw [hE]
  field_simp [hA0, hu126, hu135]
  linear_combination hE

/-- `∂dihXf/∂x5 = −2·x₁·Δ₆/(√(4·x₁·Δ)·upsX x1 x3 x5)` (HOL
`Ocbicby.derived_form_dih_x_wrt_x5`). -/
private theorem g_dihXf_hasDerivAt_x5 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu1 : 0 < upsX x1 x2 x6)
    (hu2 : 0 < upsX x1 x3 x5) :
    HasDerivAt (fun t => dihXf x1 x2 x3 x4 t x6)
      (-2 * x1 * deltaX6_p21 x1 x2 x3 x4 x5 x6
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) * upsX x1 x3 x5)) x5 := by
  have h := g_hasDerivAt_dihXf_aux (x1 := x1) (t := x5)
    (f := fun t => deltaX x1 x2 x3 x4 t x6)
    (g := fun t => deltaX4 x1 x2 x3 x4 t x6)
    (f' := deltaX5 x1 x2 x3 x4 x5 x6) (g' := x1 + x2 - x6) hx1
    (g_hasDerivAt_deltaX_x5 x1 x2 x3 x4 x5 x6)
    (g_hasDerivAt_deltaX4_x5 x1 x2 x3 x4 x5 x6) hd
  have h' : HasDerivAt (fun t => dihXf x1 x2 x3 x4 t x6)
      ((2 * x1 * deltaX4 x1 x2 x3 x4 x5 x6 * deltaX5 x1 x2 x3 x4 x5 x6
          - 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 * (x1 + x2 - x6))
        / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
            * (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2))) x5 := by
    simpa only [dihXf] using h
  refine h'.congr_deriv ?_
  have hpos : 0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by positivity
  have hA0 : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hE : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 + deltaX4 x1 x2 x3 x4 x5 x6 ^ 2
      = upsX x1 x2 x6 * upsX x1 x3 x5 := by
    rw [add_comm, g_ups_delta, mul_comm]
  have hu126 : upsX x1 x2 x6 ≠ 0 := ne_of_gt hu1
  have hu135 : upsX x1 x3 x5 ≠ 0 := ne_of_gt hu2
  have hI := g_delta_ident_x5 x1 x2 x3 x4 x5 x6
  rw [hE]
  field_simp [hA0, hu126, hu135]
  nlinarith [hI]

/-- HOL `Nonlinear_lemma.dih_x_sym`: `dihXf` is invariant under the
`(x2 x3)(x5 x6)` swap. -/
private theorem g_dihXf_sym (x1 x2 x3 x4 x5 x6 : ℝ) :
    dihXf x1 x2 x3 x4 x5 x6 = dihXf x1 x3 x2 x4 x6 x5 := by
  have hd : deltaX x1 x3 x2 x4 x6 x5 = deltaX x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX]; ring
  have hd4 : deltaX4 x1 x3 x2 x4 x6 x5 = deltaX4 x1 x2 x3 x4 x5 x6 := by
    simp only [deltaX4]; ring
  simp only [dihXf, hd, hd4]

/-- The slot transposition behind HOL's `delta_x4`/`delta_x5` exchange in
`dihV_obtuse_mono_a` (`delta_x4 b a c e d f = delta_x5 a b c d e f`). -/
private theorem g_deltaX4_eq_deltaX5 (a b c d e f : ℝ) :
    deltaX4 b a c e d f = deltaX5 a b c d e f := by
  simp only [deltaX4, deltaX5]; ring

/-- HOL `dih_gt_pi2` (merge_ineq.hl:2761): `dih_x > π/2` forces `Δ₄ < 0`. -/
private theorem g_dih_gt_pi2 {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hdih : Real.pi / 2 < dihXf x1 x2 x3 x4 x5 x6) :
    deltaX4 x1 x2 x3 x4 x5 x6 < 0 := by
  have hsqrt : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (by positivity)
  have h0 : 0 < atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6)) := by
    have hdih' : Real.pi / 2 < Real.pi / 2 + atn2
        (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
        (-(deltaX4 x1 x2 x3 x4 x5 x6)) := hdih
    linarith
  rw [g_atn2_eq_arctan hsqrt] at h0
  rcases div_pos_iff.mp (Real.arctan_pos.mp h0) with ⟨hpos, -⟩ | ⟨-, hneg⟩
  · linarith
  · linarith [hsqrt]

/-- Monotonicity from a nonnegative derivative (mean value theorem). -/
private theorem g_mono_of_deriv_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hnn : ∀ x ∈ Set.Ioo a b, 0 ≤ f' x) : f a ≤ f b := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [← h]
  · obtain ⟨c, hc, hsl⟩ := exists_hasDerivAt_eq_slope f f' h hcont hderiv
    have hden : 0 < b - a := by linarith
    have hq : 0 ≤ (f b - f a) / (b - a) := by rw [← hsl]; exact hnn c hc
    have hmul := mul_nonneg hq (le_of_lt hden)
    rw [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
    linarith

/-- Interval form of a near-zero positivity hypothesis: if `f` is positive
on `|t'| < e`, it is positive on `[c+t, c]` for `|t| < e`, `t ≤ 0`. -/
private theorem g_nbd_pos_Icc {f : ℝ → ℝ} {c e t : ℝ}
    (h1 : ∀ t' : ℝ, |t'| < e → 0 < f (c + t')) (ht : |t| < e) (ht0 : t ≤ 0) :
    ∀ q ∈ Set.Icc (c + t) c, 0 < f q := by
  intro q hq
  have hq1 : q - c ≤ 0 := by linarith [hq.2]
  have hq2 : t ≤ q - c := by linarith [hq.1]
  have habs : |q - c| ≤ |t| := by
    rw [abs_of_nonpos hq1, abs_of_nonpos ht0]; linarith
  have hlt : |q - c| < e := lt_of_le_of_lt habs ht
  have h := h1 (q - c) hlt
  have hq' : c + (q - c) = q := by ring
  rwa [hq'] at h

/-- `dihXf` is nondecreasing along a compact slot-4 interval on which `Δ`
stays positive. -/
private theorem g_dihXf_mono_x4 {x1 x2 x3 x4 x4' x5 x6 : ℝ} (hx1 : 0 < x1)
    (h44 : x4 ≤ x4')
    (hΔp : ∀ q ∈ Set.Icc x4 x4', 0 < deltaX x1 x2 x3 q x5 x6)
    (hu1 : 0 < upsX x1 x2 x6) (hu2 : 0 < upsX x1 x3 x5) :
    dihXf x1 x2 x3 x4 x5 x6 ≤ dihXf x1 x2 x3 x4' x5 x6 := by
  refine g_mono_of_deriv_nonneg (f := fun q => dihXf x1 x2 x3 q x5 x6)
    (f' := fun q => 2 * x1 / Real.sqrt (4 * x1 * deltaX x1 x2 x3 q x5 x6)) h44 ?_ ?_ ?_
  · intro q hq
    exact ((g_dihXf_hasDerivAt_x4 x1 x2 x3 q x5 x6 hx1 (hΔp q hq) hu1 hu2).continuousAt).continuousWithinAt
  · intro q hq
    exact g_dihXf_hasDerivAt_x4 x1 x2 x3 q x5 x6 hx1
      (hΔp q (Set.Ioo_subset_Icc_self hq)) hu1 hu2
  · intro q hq
    exact div_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- `dihXf` is nondecreasing along a compact slot-5 interval on which `Δ`
and `upsX x1 x3 ·` stay positive and `Δ₆` stays negative. -/
private theorem g_dihXf_mono_x5 {x1 x2 x3 x4 x5 x5' x6 : ℝ} (hx1 : 0 < x1)
    (h55 : x5 ≤ x5')
    (hΔp : ∀ q ∈ Set.Icc x5 x5', 0 < deltaX x1 x2 x3 x4 q x6)
    (hupp : ∀ q ∈ Set.Icc x5 x5', 0 < upsX x1 x3 q)
    (h6p : ∀ q ∈ Set.Icc x5 x5', deltaX6_p21 x1 x2 x3 x4 q x6 < 0)
    (hu1 : 0 < upsX x1 x2 x6) :
    dihXf x1 x2 x3 x4 x5 x6 ≤ dihXf x1 x2 x3 x4 x5' x6 := by
  refine g_mono_of_deriv_nonneg (f := fun q => dihXf x1 x2 x3 x4 q x6)
    (f' := fun q => -2 * x1 * deltaX6_p21 x1 x2 x3 x4 q x6
      / (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 q x6) * upsX x1 x3 q)) h55 ?_ ?_ ?_
  · intro q hq
    exact ((g_dihXf_hasDerivAt_x5 x1 x2 x3 x4 q x6 hx1 (hΔp q hq) hu1 (hupp q hq)).continuousAt).continuousWithinAt
  · intro q hq
    exact g_dihXf_hasDerivAt_x5 x1 x2 x3 x4 q x6 hx1
      (hΔp q (Set.Ioo_subset_Icc_self hq)) hu1 (hupp q (Set.Ioo_subset_Icc_self hq))
  · intro q hq
    have hd : 0 < deltaX x1 x2 x3 x4 q x6 := hΔp q (Set.Ioo_subset_Icc_self hq)
    have hup : 0 < upsX x1 x3 q := hupp q (Set.Ioo_subset_Icc_self hq)
    have h6 : deltaX6_p21 x1 x2 x3 x4 q x6 < 0 := h6p q (Set.Ioo_subset_Icc_self hq)
    have hden : 0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 q x6) * upsX x1 x3 q :=
      mul_pos (Real.sqrt_pos.mpr (by positivity)) hup
    have hnum : 0 ≤ -2 * x1 * deltaX6_p21 x1 x2 x3 x4 q x6 := by nlinarith
    exact div_nonneg hnum (le_of_lt hden)


end GKit

/-- HOL `dih_x5_mono` (CUXVZOZ.hl:3116): `dih_x` decreases in `x5` while
`delta_x6` is negative (MVT over the derived form). -/
theorem dih_x5_mono_p21 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hΔ : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu1 : 0 < upsX x1 x2 x6)
    (hu2 : 0 < upsX x1 x3 x5) (hΔ6 : deltaX6_p21 x1 x2 x3 x4 x5 x6 < 0) :
    ∃ e, 0 < e ∧ ∀ t, |t| < e → t ≤ 0 →
      dihXf x1 x2 x3 x4 (x5 + t) x6 ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  -- PROVED: MVT on the slot-5 derivative `g_dihXf_hasDerivAt_x5`
  -- (`-2·x₁·Δ₆/(√(4·x₁·Δ)·upsX x1 x3 x5) ≥ 0`, HOL
  -- `Ocbicby.derived_form_dih_x_wrt_x5`) with the three positivity radii
  -- from `continuous_nbd_pos_p21` and `epsilon_triple_p21`.
  have hc1 : ContinuousAt (fun t : ℝ => deltaX x1 x2 x3 x4 (x5 + t) x6) 0 := by
    simp only [deltaX]; fun_prop
  obtain ⟨e1, he1, h1⟩ := continuous_nbd_pos_p21 hc1 (by simpa using hΔ)
  have hc2 : ContinuousAt (fun t : ℝ => upsX x1 x3 (x5 + t)) 0 := by
    simp only [upsX]; fun_prop
  obtain ⟨e2, he2, h2⟩ := continuous_nbd_pos_p21 hc2 (by simpa using hu2)
  have hc3 : ContinuousAt (fun t : ℝ => -deltaX6_p21 x1 x2 x3 x4 (x5 + t) x6) 0 := by
    simp only [deltaX6_p21]; fun_prop
  obtain ⟨e3, he3, h3⟩ := continuous_nbd_pos_p21 hc3 (by simpa using (neg_pos.mpr hΔ6))
  obtain ⟨e, he, h1e, h2e, h3e⟩ := epsilon_triple_p21 e1 e2 e3 he1 he2 he3
  refine ⟨e, he, ?_⟩
  intro t ht ht0
  refine g_dihXf_mono_x5 (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4)
    (x5 := x5 + t) (x5' := x5) (x6 := x6) hx1 (by linarith) ?_ ?_ ?_ hu1
  · exact g_nbd_pos_Icc (by simpa only [sub_zero] using h1) (h1e t ht) ht0
  · exact g_nbd_pos_Icc (by simpa only [sub_zero] using h2) (h2e t ht) ht0
  · intro q hq
    have h := g_nbd_pos_Icc (f := fun u => -deltaX6_p21 x1 x2 x3 x4 u x6)
      (by simpa only [sub_zero] using h3) (h3e t ht) ht0 q hq
    linarith

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
  -- PROVED: first conjunct from the slot-4 MVT monotonicity
  -- (`g_dihXf_mono_x4`, HOL `Tame_inequalities.DIH_X_MONO_LT_4`), second
  -- from `dih_x5_mono_p21` under the `(x2 x3)(x5 x6)` swap (HOL
  -- `delta_x5_delta_x6` + `delta_x_sym`), epsilon_pair bookkeeping.
  have hc1 : ContinuousAt (fun t : ℝ => deltaX x1 x2 x3 (x4 + t) x5 x6) 0 := by
    simp only [deltaX]; fun_prop
  obtain ⟨e1, he1, h1⟩ := continuous_nbd_pos_p21 hc1 (by simpa using hΔ)
  have hΔ' : 0 < deltaX x1 x3 x2 x4 x6 x5 := by
    rw [show deltaX x1 x3 x2 x4 x6 x5 = deltaX x1 x2 x3 x4 x5 x6 from by
      simp only [deltaX]; ring]
    exact hΔ
  have hΔ6' : deltaX6_p21 x1 x3 x2 x4 x6 x5 < 0 := by
    rw [delta_x5_delta_x6_p21]
    exact hΔ5
  obtain ⟨e2, he2, h2⟩ := dih_x5_mono_p21 x1 x3 x2 x4 x6 x5 hx1 hΔ' hu2 hu1 hΔ6'
  obtain ⟨e, he, h1e, h2e⟩ := epsilon_pair_p21 e1 e2 he1 he2
  refine ⟨e, he, ?_⟩
  intro t ht ht0
  constructor
  · exact g_dihXf_mono_x4 (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4 + t) (x4' := x4)
      (x5 := x5) (x6 := x6) hx1 (by linarith)
      (g_nbd_pos_Icc (by simpa only [sub_zero] using h1) (h1e t ht) ht0) hu1 hu2
  · have h := h2 t (h2e t ht) ht0
    simpa only [g_dihXf_sym] using h

/-- HOL `dih_obtuse_mono_b` (CUXVZOZ.hl:3228): the unconditional half of
`dih_obtuse_mono` (only the `x4+t` slot, no `delta_x5` hypothesis). -/
theorem dih_obtuse_mono_b_p21 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hΔ : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu1 : 0 < upsX x1 x2 x6)
    (hu2 : 0 < upsX x1 x3 x5) :
    ∃ e, 0 < e ∧ ∀ t, |t| < e → t ≤ 0 →
      dihXf x1 x2 x3 (x4 + t) x5 x6 ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  -- PROVED: `deltaX` continuity nbd (`continuous_nbd_pos_p21`) + the
  -- slot-4 MVT monotonicity `g_dihXf_mono_x4` (derivative
  -- `2·x₁/√(4·x₁·Δ) > 0`, HOL `Tame_inequalities.DIH_X_MONO_LT_4`).
  have hc1 : ContinuousAt (fun t : ℝ => deltaX x1 x2 x3 (x4 + t) x5 x6) 0 := by
    simp only [deltaX]; fun_prop
  obtain ⟨e1, he1, h1⟩ := continuous_nbd_pos_p21 hc1 (by simpa using hΔ)
  refine ⟨e1, he1, ?_⟩
  intro t ht ht0
  exact g_dihXf_mono_x4 (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4 + t) (x4' := x4)
    (x5 := x5) (x6 := x6) hx1 (by linarith)
    (g_nbd_pos_Icc (by simpa only [sub_zero] using h1) ht ht0) hu1 hu2

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
  -- PROVED: HOL `DIHV_DIH_X` (both rotations, via `DIHV_EQ_DIH_Y_4PT`) +
  -- `dih_gt_pi2` + `dih_obtuse_mono` (slot-4/6 MVT monotonicity), with the
  -- moving bridge fed by `ups_x` continuity and `not_col_eq_upsX_pos_p21`;
  -- epsilon_triple bookkeeping.
  obtain ⟨hv01, hv02, hv03, hv12, hv13, hv23⟩ := w2b_ncop_ne_all hnc
  have hx03 : 0 < dist v0 v3 ^ 2 := pow_pos (dist_pos.mpr hv03) 2
  have hx02 : 0 < dist v0 v2 ^ 2 := pow_pos (dist_pos.mpr hv02) 2
  have hd23pos : 0 < dist v2 v3 := dist_pos.mpr hv23
  -- non-collinearity of the four triples at `v0`
  have hncol023 : ¬ Collinear ℝ ({v0, v2, v3} : Set V3) := by
    intro hc
    apply hnc
    have h := w2b_collinear_coplanar (z := v0) (w := v2) (w1 := v3) (w2 := v1) hc
    rwa [show ({v0, v2, v3, v1} : Set V3) = ({v0, v1, v2, v3} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
  have hncol021 : ¬ Collinear ℝ ({v0, v2, v1} : Set V3) := by
    intro hc
    apply hnc
    have h := w2b_collinear_coplanar (z := v0) (w := v2) (w1 := v1) (w2 := v3) hc
    rwa [show ({v0, v2, v1, v3} : Set V3) = ({v0, v1, v2, v3} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
  have hncol032 : ¬ Collinear ℝ ({v0, v3, v2} : Set V3) := by
    intro hc
    apply hnc
    have h := w2b_collinear_coplanar (z := v0) (w := v3) (w1 := v2) (w2 := v1) hc
    rwa [show ({v0, v3, v2, v1} : Set V3) = ({v0, v1, v2, v3} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
  have hncol031 : ¬ Collinear ℝ ({v0, v3, v1} : Set V3) := by
    intro hc
    apply hnc
    have h := w2b_collinear_coplanar (z := v0) (w := v3) (w1 := v1) (w2 := v2) hc
    rwa [show ({v0, v3, v1, v2} : Set V3) = ({v0, v1, v2, v3} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
  -- the two Gram minors of the dih_obtuse_mono instantiation
  have hu1 : 0 < upsX (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) (dist v2 v3 ^ 2) := by
    have h := (not_col_eq_upsX_pos_p21 v0 v3 v2).mp hncol032
    simpa only [dist_comm] using h
  have hu2 : 0 < upsX (dist v0 v3 ^ 2) (dist v0 v1 ^ 2) (dist v1 v3 ^ 2) := by
    have h := (not_col_eq_upsX_pos_p21 v0 v3 v1).mp hncol031
    simpa only [dist_comm] using h
  -- Cayley–Menger positivity, both slot orderings
  have hΔ1 : 0 < deltaX (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v0 v1 ^ 2)
      (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) (dist v2 v3 ^ 2) := by
    rw [← delta_delta_x]
    have h := (POS_EQ_NOT_COPLANANR v0 v2 v3 v1).2 (fun hc =>
      hnc (coplanar_eq_coplanar_alt.mpr (by
        rwa [show ({v0, v2, v3, v1} : Set V3) = ({v0, v1, v2, v3} : Set V3) from by
          ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at hc)))
    simpa only [dist_comm] using h
  have hΔ' : 0 < deltaX (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) (dist v0 v1 ^ 2)
      (dist v1 v2 ^ 2) (dist v1 v3 ^ 2) (dist v2 v3 ^ 2) := by
    rw [show deltaX (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) (dist v0 v1 ^ 2)
        (dist v1 v2 ^ 2) (dist v1 v3 ^ 2) (dist v2 v3 ^ 2)
        = deltaX (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v0 v1 ^ 2)
          (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) (dist v2 v3 ^ 2) from by
      simp only [deltaX]; ring]
    exact hΔ1
  -- the obtuse bridge and `dih_gt_pi2`
  have hbridge1 : dihV v0 v2 v3 v1 =
      dihXf (dist v0 v2 ^ 2) (dist v0 v3 ^ 2) (dist v0 v1 ^ 2)
        (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) (dist v2 v3 ^ 2) := by
    rw [DIHV_EQ_DIH_Y_4PT v0 v2 v3 v1 hncol023 hncol021]
    simp only [dihY, pow_two, dist_comm]
  have hz' : Real.pi / 2 < dihXf (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v0 v1 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) (dist v2 v3 ^ 2) := by
    rwa [hbridge1] at hz
  have h4neg := g_dih_gt_pi2 hx02 hΔ1 hz'
  have hΔ5 : deltaX5 (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) (dist v0 v1 ^ 2)
      (dist v1 v2 ^ 2) (dist v1 v3 ^ 2) (dist v2 v3 ^ 2) < 0 := by
    rw [← g_deltaX4_eq_deltaX5]
    exact h4neg
  -- the ε-window of `dih_obtuse_mono`
  obtain ⟨e', he', h'⟩ := dih_obtuse_mono_p21 (dist v0 v3 ^ 2) (dist v0 v2 ^ 2)
    (dist v0 v1 ^ 2) (dist v1 v2 ^ 2) (dist v1 v3 ^ 2) (dist v2 v3 ^ 2)
    hx03 hΔ' hu1 hu2 hΔ5
  -- `ups_x` continuity around the moving slot
  have hcont_ups : ContinuousAt
      (fun t : ℝ => upsX (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) ((dist v2 v3 + t) ^ 2)) 0 := by
    simp only [upsX]; fun_prop
  obtain ⟨eup, heup, hup⟩ := continuous_nbd_pos_p21 hcont_ups (by
    simpa only [add_zero, pow_two, dist_comm] using hu1)
  -- the `|2·d·t + t²|` window
  have hcont_abs : ContinuousAt
      (fun t : ℝ => e' - |2 * dist v2 v3 * t + t * t|) 0 := by
    have h : ContinuousAt (fun t : ℝ => 2 * dist v2 v3 * t + t * t) 0 := by fun_prop
    exact continuousAt_const.sub h.abs
  obtain ⟨eabs, heabs, habs⟩ := continuous_nbd_pos_p21 hcont_abs (by simpa using he')
  obtain ⟨E, hE, hEup, hEabs, hE2d⟩ := epsilon_triple_p21 eup eabs (2 * dist v2 v3)
    heup heabs (by positivity)
  refine ⟨E, hE, ?_⟩
  intro v2' t ht ht0 hd02 hd12 hd23
  -- the moving triples stay non-collinear
  have hupt : 0 < upsX (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) ((dist v2 v3 + t) ^ 2) :=
    hup t (by simpa using hEup t ht)
  have hncolv2' : ¬ Collinear ℝ ({v0, v3, v2'} : Set V3) := by
    refine (not_col_eq_upsX_pos_p21 v0 v3 v2').mpr ?_
    rw [hd02]
    have h3 : dist v3 v2' = dist v2 v3 + t := by rw [dist_comm v3 v2', hd23]
    rw [h3]
    exact hupt
  -- the ε-data at the actual `t`
  have hs_abs : |2 * dist v2 v3 * t + t * t| < e' := by
    have h := hEabs t ht
    have h2 := habs t (by simpa using h)
    linarith
  have ht2d : 0 ≤ t + 2 * dist v2 v3 := by
    have h := hE2d t ht
    linarith [neg_abs_le t]
  have hs_np : 2 * dist v2 v3 * t + t * t ≤ 0 :=
    square_add_neg_lemma_p21 (dist v2 v3) t ht0 ht2d
  have hkey := (h' (2 * dist v2 v3 * t + t * t) hs_abs hs_np).2
  -- bridge the two `dihV`s to `dih_x`
  have hb' : dihV v0 v3 v2' v1 =
      dihXf (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) (dist v0 v1 ^ 2)
        (dist v1 v2 ^ 2) (dist v1 v3 ^ 2) (dist v2' v3 ^ 2) := by
    rw [DIHV_EQ_DIH_Y_4PT v0 v3 v2' v1 hncolv2' hncol031]
    simp only [dihY, pow_two, hd02, hd12, dist_comm]
  have hbfix : dihV v0 v3 v2 v1 =
      dihXf (dist v0 v3 ^ 2) (dist v0 v2 ^ 2) (dist v0 v1 ^ 2)
        (dist v1 v2 ^ 2) (dist v1 v3 ^ 2) (dist v2 v3 ^ 2) := by
    rw [DIHV_EQ_DIH_Y_4PT v0 v3 v2 v1 hncol032 hncol031]
    simp only [dihY, pow_two, dist_comm]
  have hs_eq : dist v2' v3 ^ 2 =
      dist v2 v3 ^ 2 + (2 * dist v2 v3 * t + t * t) := by
    rw [hd23]; ring
  rw [hb', hbfix, hs_eq]
  exact hkey

/-- HOL `dihV_obtuse_mono_b` (CUXVZOZ.hl:3378): the opposite-handed half —
`dihV v0 v1 v2' v3` decreases under the same edge move. -/
theorem dihV_obtuse_mono_b_p21 (v0 v1 v2 v3 : V3)
    (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3)) :
    ∃ e, 0 < e ∧ ∀ v2' : V3, ∀ t : ℝ, |t| < e → t ≤ 0 →
      dist v0 v2' = dist v0 v2 → dist v1 v2' = dist v1 v2 →
      dist v2' v3 = dist v2 v3 + t →
      dihV v0 v1 v2' v3 ≤ dihV v0 v1 v2 v3 := by
  -- PROVED: HOL `DIHV_DIH_X` + `dih_obtuse_mono_b` + `square_add_neg_lemma`,
  -- with the moving bridge fed by `not_col_eq_upsX_pos_p21` and the
  -- distance constraints; epsilon_triple bookkeeping.
  obtain ⟨hv01, hv02, hv03, hv12, hv13, hv23⟩ := w2b_ncop_ne_all hnc
  have hd23pos : 0 < dist v2 v3 := dist_pos.mpr hv23
  have hx1 : 0 < dist v0 v1 ^ 2 := pow_pos (dist_pos.mpr hv01) 2
  -- the two fixed triples at `v0`
  have hncol012 : ¬ Collinear ℝ ({v0, v1, v2} : Set V3) :=
    fun hc => hnc (w2b_collinear_coplanar (z := v0) (w := v1) (w1 := v2) (w2 := v3) hc)
  have hncol013 : ¬ Collinear ℝ ({v0, v1, v3} : Set V3) := by
    intro hc
    apply hnc
    have h := w2b_collinear_coplanar (z := v0) (w := v1) (w1 := v3) (w2 := v2) hc
    rwa [show ({v0, v1, v3, v2} : Set V3) = ({v0, v1, v2, v3} : Set V3) from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto] at h
  have hu1 : 0 < upsX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v1 v2 ^ 2) :=
    (not_col_eq_upsX_pos_p21 v0 v1 v2).mp hncol012
  have hu2 : 0 < upsX (dist v0 v1 ^ 2) (dist v0 v3 ^ 2) (dist v1 v3 ^ 2) :=
    (not_col_eq_upsX_pos_p21 v0 v1 v3).mp hncol013
  -- Cayley–Menger positivity of the base tetrahedron
  have hΔ : 0 < deltaX (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
      (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
    rw [← delta_delta_x]
    exact (POS_EQ_NOT_COPLANANR v0 v1 v2 v3).2
      (fun hc => hnc (coplanar_eq_coplanar_alt.mpr hc))
  -- the fixed bridge
  have hb : dihV v0 v1 v2 v3 =
      dihXf (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
    rw [DIHV_EQ_DIH_Y_4PT v0 v1 v2 v3 hncol012 hncol013]
    simp only [dihY, pow_two]
  -- the ε-window of `dih_obtuse_mono_b`
  obtain ⟨e', he', h'⟩ := dih_obtuse_mono_b_p21 (dist v0 v1 ^ 2) (dist v0 v2 ^ 2)
    (dist v0 v3 ^ 2) (dist v2 v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2)
    hx1 hΔ hu1 hu2
  -- the `|2·d·t + t²|` window
  have hcont_abs : ContinuousAt
      (fun t : ℝ => e' - |2 * dist v2 v3 * t + t * t|) 0 := by
    have h : ContinuousAt (fun t : ℝ => 2 * dist v2 v3 * t + t * t) 0 := by fun_prop
    exact continuousAt_const.sub h.abs
  obtain ⟨eabs, heabs, habs⟩ := continuous_nbd_pos_p21 hcont_abs (by simpa using he')
  obtain ⟨E, hE, hEabs, hE2d⟩ := epsilon_pair_p21 eabs (2 * dist v2 v3) heabs (by positivity)
  refine ⟨E, hE, ?_⟩
  intro v2' t ht ht0 hd02 hd12 hd23
  -- non-collinearity of the moving triple from the fixed Gram minor
  have hncolv2' : ¬ Collinear ℝ ({v0, v1, v2'} : Set V3) := by
    refine (not_col_eq_upsX_pos_p21 v0 v1 v2').mpr ?_
    rw [hd02, hd12]
    exact hu1
  have hs_abs : |2 * dist v2 v3 * t + t * t| < e' := by
    have h := hEabs t ht
    have h2 := habs t (by simpa using h)
    linarith
  have ht2d : 0 ≤ t + 2 * dist v2 v3 := by
    have h := hE2d t ht
    linarith [neg_abs_le t]
  have hs_np : 2 * dist v2 v3 * t + t * t ≤ 0 :=
    square_add_neg_lemma_p21 (dist v2 v3) t ht0 ht2d
  have hkey := h' (2 * dist v2 v3 * t + t * t) hs_abs hs_np
  -- bridge the two `dihV`s to `dih_x`
  have hb' : dihV v0 v1 v2' v3 =
      dihXf (dist v0 v1 ^ 2) (dist v0 v2 ^ 2) (dist v0 v3 ^ 2)
        (dist v2' v3 ^ 2) (dist v1 v3 ^ 2) (dist v1 v2 ^ 2) := by
    rw [DIHV_EQ_DIH_Y_4PT v0 v1 v2' v3 hncolv2' hncol013]
    simp only [dihY, pow_two, hd02, hd12]
  have hs_eq : dist v2' v3 ^ 2 =
      dist v2 v3 ^ 2 + (2 * dist v2 v3 * t + t * t) := by
    rw [hd23]; ring
  rw [hb', hb, hs_eq]
  exact hkey

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
  -- PROVED 2026-11-12: HOL CUXVZOZ.hl:3549. `BBprime_v39` supplies the
  -- minimality `taustar_v39 s v ≤ taustar_v39 s w`; `3 < k` puts both sides in
  -- the `tau_fun` branch, `tau_fun_azim` (LA38:2422) rewrites it to the
  -- `rho_fun * azim` sum minus `(pi + sol0) * (k - 2)`, and `scs_basic_v39`'s
  -- `J = fun _ _ => False` makes `dsv_v39` the constant `s.d` (`dsv_J_empty`).
  have hv' : BBsV39 s v ∧
      (∀ ww, BBsV39 s ww → taustarV39 s v ≤ taustarV39 s ww) ∧
      taustarV39 s v < 0 := hv
  obtain ⟨hBBv, hminv, -⟩ := hv'
  obtain ⟨-, hJ⟩ := hbasic
  have hJf : s.J = fun _ _ => False := funext fun i => funext fun j => hJ i j
  have hkgt : ¬ s.k ≤ 3 := by rw [hk]; exact not_le.mpr hk3
  have hle : taustarV39 s v ≤ taustarV39 s w := hminv w hw
  have hper : ∀ u : ℕ → V3, BBsV39 s u → Periodic u k := by
    intro u hu i
    have h := hu.2.1 i
    rwa [hk] at h
  have hinj : ∀ u : ℕ → V3, BBsV39 s u →
      ∀ i j : ℕ, i < k ∧ j < k ∧ u i = u j → i = j := by
    intro u hu i j h
    exact BBs_inj_p21 s u k hs hk hu i j h.1 h.2.1 h.2.2
  have htv := tau_fun_azim v k (hper v hBBv) (le_of_lt hk3) (hinj v hBBv)
  have htw := tau_fun_azim w k (hper w hw) (le_of_lt hk3) (hinj w hw)
  have hdsv : dsvV39 s v = dsvV39 s w := by
    rw [dsv_J_empty s v hJf, dsv_J_empty s w hJf]
  simp only [taustarV39, if_neg hkgt] at hle
  rw [htv, htw, hdsv] at hle
  linarith

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

/-! ## W3 kit (`g482w3_*`): generic helpers for `general_482_deformation_p21`

Everything here is `private`-free so the block can be spliced into
`LocalAuto21.lean` immediately above the target theorem. -/

/-- Cyclic symmetry of `taum` (from `taum_sym2`). -/
theorem g482w3_taum_cyc (a b c x y z : ℝ) : taum a b c x y z = taum b c a y z x := by
  rw [(taum_sym2 a b c x y z).1, (taum_sym2 b a c y x z).2]

theorem g482w3_taum_swap12 (a b c x y z : ℝ) : taum a b c x y z = taum b a c y x z :=
  (taum_sym2 a b c x y z).1

/-- Determinant positivity from an azimuth in `(0, π)` (HOL `JBDNJJB`). -/
theorem g482w3_cross_det_pos {x y z : V3} (h1 : ¬ Collinear3 0 x y) (h2 : ¬ Collinear3 0 x z)
    (hpos : 0 < azim 0 x y z) (hlt : azim 0 x y z < Real.pi) :
    0 < crossProduct x.ofLp y.ofLp ⬝ᵥ z.ofLp := by
  obtain ⟨s, hs, hseq⟩ := JBDNJJB (u := x) (v := y) (w := z) h1 h2
  have hsin : 0 < Real.sin (azim 0 x y z) := (sin_azim_pos_p21 0 x y z).mpr ⟨hpos, hlt⟩
  rw [hseq] at hsin
  nlinarith [hs, hsin]

theorem g482w3_cross_det_cyc (a b c : V3) :
    crossProduct a.ofLp b.ofLp ⬝ᵥ c.ofLp = crossProduct b.ofLp c.ofLp ⬝ᵥ a.ofLp := by
  rw [dotProduct_comm, triple_product_permutation c a b, dotProduct_comm]

theorem g482w3_cross_det_cyc2 (a b c : V3) :
    crossProduct a.ofLp b.ofLp ⬝ᵥ c.ofLp = crossProduct c.ofLp a.ofLp ⬝ᵥ b.ofLp := by
  rw [g482w3_cross_det_cyc a b c, g482w3_cross_det_cyc b c a]

/-- Azim-cycle: one azimuth in `(0, π)` gives the other two. -/
theorem g482w3_azim_cycle {x y z : V3} (h1 : ¬ Collinear3 0 x y)
    (h2 : ¬ Collinear3 0 x z)
    (hpos : 0 < azim 0 x y z) (hlt : azim 0 x y z < Real.pi) :
    (0 < azim 0 y z x ∧ azim 0 y z x < Real.pi) ∧
      (0 < azim 0 z x y ∧ azim 0 z x y < Real.pi) := by
  have hdet : 0 < crossProduct x.ofLp y.ofLp ⬝ᵥ z.ofLp := g482w3_cross_det_pos h1 h2 hpos hlt
  have hyzx : 0 < (cross3 y z).ofLp ⬝ᵥ x.ofLp := by
    rw [cross3, WithLp.ofLp_toLp]
    rw [← g482w3_cross_det_cyc x y z]
    exact hdet
  have hzxy : 0 < (cross3 z x).ofLp ⬝ᵥ y.ofLp := by
    rw [cross3, WithLp.ofLp_toLp]
    rw [← g482w3_cross_det_cyc2 x y z]
    exact hdet
  exact ⟨(azim_lt_pi_cross_p14 y z x).mpr hyzx, (azim_lt_pi_cross_p14 z x y).mpr hzxy⟩

/-- `0 < upsX` bridge from non-collinearity. -/
theorem g482w3_upsX_pos_of_not_col {a b c : V3} (hnc : ¬ Collinear3 a b c) :
    0 < upsX (dist a b * dist a b) (dist a c * dist a c) (dist b c * dist b c) := by
  have h := (not_col_eq_upsX_pos_p21 a b c).mp hnc
  simpa [pow_two] using h

/-- `0 < deltaY` bridge from non-coplanarity. -/
theorem g482w3_deltaY_pos {u0 u1 u2 u3 : V3} (hnc : ¬ Coplanar ({u0, u1, u2, u3} : Set V3)) :
    0 < deltaY (dist u0 u1) (dist u0 u2) (dist u0 u3) (dist u2 u3) (dist u1 u3) (dist u1 u2) := by
  have hnn : 0 ≤ deltaY (dist u0 u1) (dist u0 u2) (dist u0 u3) (dist u2 u3)
      (dist u1 u3) (dist u1 u2) := DELTA_Y_POS_4POINTS_B u0 u1 u2 u3
  refine lt_of_le_of_ne hnn ?_
  intro hz
  exact hnc ((coplanar_delta_y_zero_p18 u0 u1 u2 u3).mpr hz.symm)

/-- Re-indexing of the four-point `taum` by the pair equality
`{p0, p2} = {b, c}` (HOL `general_482_deformation`, `taum_sym2` block). -/
theorem g482w3_taum4 (w b c p0 p2 : V3) (hne : b ≠ c)
    (h : ({p0, p2} : Set V3) = {b, c}) :
    taum ‖w‖ ‖b‖ ‖c‖ (dist b c) (dist w c) (dist w b)
      = taum ‖p0‖ ‖p2‖ ‖w‖ (dist w p2) (dist p0 w) (dist p0 p2) := by
  have hcases : (p0 = b ∧ p2 = c) ∨ (p0 = c ∧ p2 = b) := by
    have hm0 : p0 ∈ ({b, c} : Set V3) := by rw [← h]; simp
    have hc : c ∈ ({p0, p2} : Set V3) := by rw [h]; simp
    have hb : b ∈ ({p0, p2} : Set V3) := by rw [h]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm0 hc hb
    rcases hm0 with hm0 | hm0
    · subst hm0
      rcases hc with hc | hc
      · exact absurd hc.symm hne
      · exact Or.inl ⟨rfl, hc.symm⟩
    · subst hm0
      rcases hb with hb | hb
      · exact absurd hb hne
      · exact Or.inr ⟨rfl, hb.symm⟩
  rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
  · rw [hp0, hp2]
    rw [g482w3_taum_cyc, dist_comm b w]
  · rw [hp0, hp2]
    rw [g482w3_taum_cyc, g482w3_taum_swap12, dist_comm c w, dist_comm c b]

/-- `setSum` over `{i | i < k}` is `Finset.range` summation. -/
theorem g482w3_setSum_range (f : ℕ → ℝ) (k : ℕ) :
    setSum {i | i < k} f = ∑ i ∈ Finset.range k, f i := by
  have hfin : ({i : ℕ | i < k} : Set ℕ).Finite := Set.finite_Iio k
  have key : setSum ({i : ℕ | i < k} : Set ℕ) f = ∑ w ∈ hfin.toFinset, f w := by
    unfold setSum
    exact dif_pos hfin
  rw [key]
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, Finset.mem_range]
  rfl

/-- Periodicity of `v` transported across a shifted reduced index:
`v (i % k + c) = v (i + c)`. -/
theorem g482w3_periodic_add {v : ℕ → V3} {k : ℕ} (hper : Periodic v k) (_hk : k ≠ 0)
    (i c : ℕ) : v ((i % k) + c) = v (i + c) := by
  have h1 : v ((i % k) + c) = v (((i % k) + c) % k) := (periodic_mod_p18 hper _).symm
  have h2 : ((i % k) + c) % k = (i + c) % k := by
    rw [Nat.add_mod (i % k) c k, Nat.add_mod i c k, Nat.mod_mod]
  rw [h1, h2, periodic_mod_p18 hper]

/-- The three residues `p1, p1+1, p1+k-1` are pairwise distinct mod `k`. -/
theorem g482w3_res_three_distinct {k p1 : ℕ} (hk3 : 3 < k) :
    (p1 + 1) % k ≠ p1 % k ∧ (p1 + (k - 1)) % k ≠ p1 % k ∧
      (p1 + (k - 1)) % k ≠ (p1 + 1) % k := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hdvd : k ∣ (p1 + 1) - p1 :=
      (Nat.modEq_iff_dvd' (by omega : p1 ≤ p1 + 1)).mp he.symm
    have h1 : (p1 + 1) - p1 = 1 := by omega
    rw [h1] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · intro he
    have hdvd : k ∣ (p1 + (k - 1)) - p1 :=
      (Nat.modEq_iff_dvd' (by omega : p1 ≤ p1 + (k - 1))).mp he.symm
    have h1 : (p1 + (k - 1)) - p1 = k - 1 := by omega
    rw [h1] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · intro he
    have hdvd : k ∣ (p1 + (k - 1)) - (p1 + 1) :=
      (Nat.modEq_iff_dvd' (by omega : p1 + 1 ≤ p1 + (k - 1))).mp he.symm
    have h1 : (p1 + (k - 1)) - (p1 + 1) = k - 2 := by omega
    rw [h1] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

/-- Expansion of the three-point sum at `t = 0` (HOL `general_482_deformation`,
the `sum {p1 MOD k, ...}` block). -/
theorem g482w3_sum_T_G (v : ℕ → V3) {k p1 : ℕ} (hk3 : 3 < k) (hper : Periodic v k) :
    ∑ i ∈ ({p1 % k, (p1 + 1) % k, (p1 + (k - 1)) % k} : Finset ℕ),
        rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + (k - 1)))
      = rhoFun ‖v p1‖ * azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1)))
        + rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + 2)) (v p1)
        + rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + (k - 2))) := by
  obtain ⟨hA, hB, hC⟩ := g482w3_res_three_distinct (k := k) (p1 := p1) hk3
  have hk0 : k ≠ 0 := by omega
  have hnot1 : p1 % k ∉ ({((p1 + 1) % k), ((p1 + (k - 1)) % k)} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hA, Ne.symm hB⟩
  have hnot2 : ((p1 + 1) % k) ∉ ({(p1 + (k - 1)) % k} : Finset ℕ) := by
    simpa using (Ne.symm hC)
  rw [Finset.sum_insert hnot1, Finset.sum_insert hnot2, Finset.sum_singleton]
  have e1 : rhoFun ‖v (p1 % k)‖ * azim 0 (v (p1 % k)) (v (p1 % k + 1)) (v (p1 % k + (k - 1)))
      = rhoFun ‖v p1‖ * azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) := by
    rw [periodic_mod_p18 hper, g482w3_periodic_add hper hk0 p1 1,
      g482w3_periodic_add hper hk0 p1 (k - 1)]
  have e2 : rhoFun ‖v ((p1 + 1) % k)‖ * azim 0 (v ((p1 + 1) % k))
        (v ((p1 + 1) % k + 1)) (v ((p1 + 1) % k + (k - 1)))
      = rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + 2)) (v p1) := by
    rw [periodic_mod_p18 hper, g482w3_periodic_add hper hk0 (p1 + 1) 1,
      g482w3_periodic_add hper hk0 (p1 + 1) (k - 1),
      show (p1 + 1) + (k - 1) = p1 + k by omega, hper p1]
  have e3 : rhoFun ‖v ((p1 + (k - 1)) % k)‖ * azim 0 (v ((p1 + (k - 1)) % k))
        (v ((p1 + (k - 1)) % k + 1)) (v ((p1 + (k - 1)) % k + (k - 1)))
      = rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + (k - 2))) := by
    rw [periodic_mod_p18 hper, g482w3_periodic_add hper hk0 (p1 + (k - 1)) 1,
      g482w3_periodic_add hper hk0 (p1 + (k - 1)) (k - 1),
      show (p1 + (k - 1)) + 1 = p1 + k by omega, hper p1,
      show (p1 + (k - 1)) + (k - 1) = (p1 + (k - 2)) + k by omega, hper (p1 + (k - 2))]
  rw [e1, e2, e3]
  ring

/-- Expansion of the three-point sum at time `t`, using the four frozen values
(HOL `general_482_deformation`, `A3`-`A6` frozen-azimuth block). -/
theorem g482w3_sum_T_H (f : V3 → ℝ → V3) (v : ℕ → V3) {k p1 : ℕ} (t : ℝ) (hk3 : 3 < k)
    (hper : Periodic v k)
    (hf1 : f (v (p1 + 1)) t = v (p1 + 1)) (hf2 : f (v (p1 + 2)) t = v (p1 + 2))
    (hf3 : f (v (p1 + (k - 1))) t = v (p1 + (k - 1)))
    (hf4 : f (v (p1 + (k - 2))) t = v (p1 + (k - 2))) :
    ∑ i ∈ ({p1 % k, (p1 + 1) % k, (p1 + (k - 1)) % k} : Finset ℕ),
        rhoFun ‖f (v i) t‖ * azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t)
      = rhoFun ‖f (v p1) t‖ * azim 0 (f (v p1) t) (v (p1 + 1)) (v (p1 + (k - 1)))
        + rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + 2)) (f (v p1) t)
        + rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + (k - 2))) := by
  obtain ⟨hA, hB, hC⟩ := g482w3_res_three_distinct (k := k) (p1 := p1) hk3
  have hk0 : k ≠ 0 := by omega
  have hnot1 : p1 % k ∉ ({((p1 + 1) % k), ((p1 + (k - 1)) % k)} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hA, Ne.symm hB⟩
  have hnot2 : ((p1 + 1) % k) ∉ ({(p1 + (k - 1)) % k} : Finset ℕ) := by
    simpa using (Ne.symm hC)
  rw [Finset.sum_insert hnot1, Finset.sum_insert hnot2, Finset.sum_singleton]
  have e1 : rhoFun ‖f (v (p1 % k)) t‖ * azim 0 (f (v (p1 % k)) t)
        (f (v (p1 % k + 1)) t) (f (v (p1 % k + (k - 1))) t)
      = rhoFun ‖f (v p1) t‖ * azim 0 (f (v p1) t) (v (p1 + 1)) (v (p1 + (k - 1))) := by
    rw [periodic_mod_p18 hper, g482w3_periodic_add hper hk0 p1 1,
      g482w3_periodic_add hper hk0 p1 (k - 1), hf1, hf3]
  have e2 : rhoFun ‖f (v ((p1 + 1) % k)) t‖ * azim 0 (f (v ((p1 + 1) % k)) t)
        (f (v ((p1 + 1) % k + 1)) t) (f (v ((p1 + 1) % k + (k - 1))) t)
      = rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + 2)) (f (v p1) t) := by
    rw [periodic_mod_p18 hper, g482w3_periodic_add hper hk0 (p1 + 1) 1,
      g482w3_periodic_add hper hk0 (p1 + 1) (k - 1),
      show (p1 + 1) + (k - 1) = p1 + k by omega, hper p1, hf1, hf2]
  have e3 : rhoFun ‖f (v ((p1 + (k - 1)) % k)) t‖ * azim 0 (f (v ((p1 + (k - 1)) % k)) t)
        (f (v ((p1 + (k - 1)) % k + 1)) t) (f (v ((p1 + (k - 1)) % k + (k - 1))) t)
      = rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + (k - 2))) := by
    rw [periodic_mod_p18 hper, g482w3_periodic_add hper hk0 (p1 + (k - 1)) 1,
      g482w3_periodic_add hper hk0 (p1 + (k - 1)) (k - 1),
      show (p1 + (k - 1)) + 1 = p1 + k by omega, hper p1,
      show (p1 + (k - 1)) + (k - 1) = (p1 + (k - 2)) + k by omega, hper (p1 + (k - 2)),
      hf3, hf4]
  rw [e1, e2, e3]
  ring

/-- `psort` is symmetric in its pair argument (HOL `Terminal.psort_sym`). -/
theorem g482w3_psort_swap (k a b : ℕ) : psort k (a, b) = psort k (b, a) := by
  simp only [psort]
  by_cases h1 : a % k ≤ b % k <;> by_cases h2 : b % k ≤ a % k <;>
    simp [h1, h2] <;> omega

/-- Nested-epsilon intersection: a single `e` below six given positive bounds. -/
theorem g482w3_eps6 (e1 e2 e3 e4 e5 e6 : ℝ) (h1 : 0 < e1) (h2 : 0 < e2) (h3 : 0 < e3)
    (h4 : 0 < e4) (h5 : 0 < e5) (h6 : 0 < e6) :
    ∃ e, 0 < e ∧ (∀ t, |t| < e → |t| < e1) ∧ (∀ t, |t| < e → |t| < e2) ∧
      (∀ t, |t| < e → |t| < e3) ∧ (∀ t, |t| < e → |t| < e4) ∧
      (∀ t, |t| < e → |t| < e5) ∧ (∀ t, |t| < e → |t| < e6) := by
  refine ⟨min e1 (min e2 (min e3 (min e4 (min e5 e6)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · intro t ht; exact lt_of_lt_of_le ht (min_le_left _ _)
  · intro t ht
    exact lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_left _ _))
  · intro t ht
    exact lt_of_lt_of_le ht
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  · intro t ht
    exact lt_of_lt_of_le ht (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  · intro t ht
    exact lt_of_lt_of_le ht (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  · intro t ht
    exact lt_of_lt_of_le ht (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))))

/-- Nested-epsilon intersection, four bounds. -/
theorem g482w3_eps4 (e1 e2 e3 e4 : ℝ) (h1 : 0 < e1) (h2 : 0 < e2) (h3 : 0 < e3)
    (h4 : 0 < e4) :
    ∃ e, 0 < e ∧ (∀ t, |t| < e → |t| < e1) ∧ (∀ t, |t| < e → |t| < e2) ∧
      (∀ t, |t| < e → |t| < e3) ∧ (∀ t, |t| < e → |t| < e4) := by
  obtain ⟨e, he, h1', h2', h3', h4', -, -⟩ := g482w3_eps6 e1 e2 e3 e4 e1 e2 h1 h2 h3 h4 h1 h2
  exact ⟨e, he, h1', h2', h3', h4'⟩

/-- Algebra of the final three-point comparison (HOL `general_482_deformation`,
`MATCH_MP_TAC (arith ...)` closing step): the two sums differ only in the
`r1*a1 + r2*a2 + r3*b2` bracket once the `(A1)`/`(A2)` splits are substituted. -/
theorem g482w3_T_lt_alg (r1 r2 r3 A1 A1' X X' Y Y' C2 C3 G H : ℝ)
    (hG : G = r1 * A1 + r2 * (C2 + Y) + r3 * (X + C3))
    (hH : H = r1 * A1' + r2 * (C2 + Y') + r3 * (X' + C3))
    (hlt : r1 * A1' + r2 * Y' + r3 * X' < r1 * A1 + r2 * Y + r3 * X) : H < G := by
  rw [hG, hH]; linarith

/-- Interface of the `LEMMA_4828966562` monotonicity witness at a decreased
`y4`: the only obligations are the two `Ioo` memberships and the strict drop. -/
theorem g482w3_taum_lt (y1 y2 y3 y4 y4a y5 y6 a b : ℝ)
    (hmem : y4 ∈ Set.Ioo a b)
    (hmono : ∀ p q, p ∈ Set.Ioo a b → q ∈ Set.Ioo a b → p < q →
      taum y1 y2 y3 p y5 y6 < taum y1 y2 y3 q y5 y6)
    (hlt : y4a < y4) (hlo : a < y4a) (hhi : y4a < b) :
    taum y1 y2 y3 y4a y5 y6 < taum y1 y2 y3 y4 y5 y6 :=
  hmono y4a y4 ⟨hlo, hhi⟩ hmem hlt

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
  -- ## A. basic facts
  have hk0 : k ≠ 0 := by omega
  have hnk : ¬ k ≤ 3 := by omega
  simp only [MMsV39, Set.mem_setOf_eq] at hMMs
  obtain ⟨hvBB2, -, -, -, -, -⟩ := hMMs
  simp only [BBprime2V39, Set.mem_setOf_eq] at hvBB2
  obtain ⟨hvBBp, -⟩ := hvBB2
  simp only [BBprimeV39, Set.mem_setOf_eq] at hvBBp
  obtain ⟨hvBB, hvmin, hvneg⟩ := hvBBp
  obtain ⟨hann, hperS, hbnd, hconv⟩ := hvBB
  have hvBBs : BBsV39 s v := ⟨hann, hperS, hbnd, hconv⟩
  have hperv : Periodic v k := by
    intro i
    have := hperS i
    rwa [← hk] at this
  have hmod : ∀ i : ℕ, v (i % k) = v i := periodic_mod_p18 hperv
  -- ## B. fan structure
  set V : Set V3 := Set.range v with hV
  set E : Set (Set V3) := Set.range fun i => ({v i, v (i + 1)} : Set V3) with hE
  have hclf : ConvexLocalFan V E FF := by
    rcases hconv with hle | hcl
    · exfalso; omega
    · simpa only [hV, hE, hFF] using hcl
  have hlf : LocalFan V E FF := hclf.1
  have hvmem : ∀ i : ℕ, v i ∈ V := fun i => by rw [hV]; exact Set.mem_range_self i
  -- ## C. base interior angle: positivity and azim form
  have hpos : 0 < interiorAngle1 0 FF (v p1) := by
    have hlf2 : localFan_p2 V E FF := w5cC_lf2_of_LocalFan hlf
    have h := INTERIOR_ANGLE1_POS (V := V) (E := E) (FF := FF) hlf2 (hvmem p1)
    simpa only [interiorAngle1, interiorAngle1_p2, rhoNode1, rhoNode1_p2,
      ivsRhoNode1, ivsRhoNode1_p2] using h
  have hrho : rhoNode1 FF (v p1) = v (p1 + 1) := by
    have hp := VV_SUC_EQ_RHO_NODE_PRIME_p35 s k p1 p1 0 (v p1) V E FF v
      hk.symm rfl hV.symm hE.symm hFF.symm hs hnk hvBBs 1
    simp only [Function.iterate_one] at hp
    simpa [Nat.add_comm] using hp
  have hivs : ivsRhoNode1 FF (v p1) = v (p1 + (k - 1)) :=
    VV_SUC_EQ_IVS_RHO_NODE_PRIME_p21 V E FF s v (v p1) k p1
      hk.symm rfl hV.symm hE.symm hFF.symm hs hnk hvBBs
  have hazim_base : interiorAngle1 0 FF (v p1) = azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) := by
    rw [interior_angle1_azim_p21 V E FF (v p1) hlf (hvmem p1), hrho, hivs]
  -- ## D. non-collinearity of the two base spokes
  have hdisj : v (p1 + (k - 1)) ≠ v (p1 + 1) := by
    intro he
    have hlb := scs_lb_2_p22 s v (p1 + 1) (p1 + (k - 1)) hs hvBBs ?_
    · rw [he, dist_self] at hlb; linarith
    · intro hc
      have hc' : (p1 + 1) % k = (p1 + (k - 1)) % k := by rw [← hk] at hc; exact hc
      have hle : p1 + 1 ≤ p1 + (k - 1) := by omega
      have hdvd : k ∣ (p1 + (k - 1)) - (p1 + 1) := (Nat.modEq_iff_dvd' hle).mp hc'
      have hval : (p1 + (k - 1)) - (p1 + 1) = k - 2 := by omega
      rw [hval] at hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  have hnc_col : ¬ Collinear ℝ ({0, v (p1 + 1), v (p1 + (k - 1))} : Set V3) := by
    have hp14 := PROPERTIES_GENERIC_LOCAL_FAN_ALT_p14 V E FF (v (p1 + (k - 1))) (v (p1 + 1))
      hlf (hvmem _) (hvmem _) hdisj (by simpa only [scsGeneric, ← hV, ← hE] using hgen)
    have hsetpair : ({0, v (p1 + 1), v (p1 + (k - 1))} : Set V3) =
        {0, v (p1 + (k - 1)), v (p1 + 1)} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hsetpair]; exact hp14
  -- ## E. non-coplanarity of the base tetrahedron
  have hncop : ¬ Coplanar ({0, v p1, v (p1 + 1), v (p1 + (k - 1))} : Set V3) := by
    intro hc
    have hd := (AZIM_COND_FOR_COPLANAR 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1)))).mpr hc
    rw [← hazim_base] at hd
    rcases hd with h0 | hpi
    · linarith
    · linarith
  -- ## F. contradiction setup
  by_contra hne
  -- ## G. base azim facts
  have hposA : 0 < azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) := by
    rw [← hazim_base]; exact hpos
  have hltA : azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) < Real.pi := by
    rw [← hazim_base]; exact hang
  have hncfan := notcoplanar_imp_notcollinear_fan (x := (0:V3)) (v := v p1)
    (u := v (p1 + 1)) (w := v (p1 + (k - 1))) hncop
  -- cyclic partners of the base azimuth
  have hB_base : 0 < azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1) ∧
      azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1) < Real.pi := by
    exact (g482w3_azim_cycle (x := v p1) (y := v (p1 + 1)) (z := v (p1 + (k - 1)))
      hncfan.2.1 hncfan.2.2 hposA hltA).1

  -- ## H. the deforming family
  have hups : 0 < (v p1).ofLp ⬝ᵥ (cross3 (v (p1 + 1)) (v (p1 + (k - 1)))).ofLp := by
    have hcyc := (azim_lt_pi_cross_p14 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1)).mp hB_base
    simpa only [dotProduct_comm] using hcyc
  have hncop4 : ¬ Coplanar ({0, v (p1 + (k - 1)), v p1, v (p1 + 1)} : Set V3) := by
    intro hc
    apply hncop
    have hset : ({0, v (p1 + (k - 1)), v p1, v (p1 + 1)} : Set V3) =
        {0, v p1, v (p1 + 1), v (p1 + (k - 1))} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [hset] at hc
  -- `v (p1+1) ≠ v p1` and `v (p1+k-1) ≠ v p1`
  have hmod_ne_succ : (p1 + 1) % k ≠ p1 % k := by
    intro he
    have hle : p1 ≤ p1 + 1 := by omega
    have hdvd : k ∣ (p1 + 1) - p1 := (Nat.modEq_iff_dvd' hle).mp he.symm
    have hval : (p1 + 1) - p1 = 1 := by omega
    rw [hval] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hmod_ne_pred : (p1 + (k - 1)) % k ≠ p1 % k := by
    intro he
    have hle : p1 ≤ p1 + (k - 1) := by omega
    have hdvd : k ∣ (p1 + (k - 1)) - p1 := (Nat.modEq_iff_dvd' hle).mp he.symm
    have hval : (p1 + (k - 1)) - p1 = k - 1 := by omega
    rw [hval] at hdvd
    have hk1 : 0 < k - 1 := by omega
    have := Nat.le_of_dvd hk1 hdvd
    omega
  have hne_succ : v (p1 + 1) ≠ v p1 := by
    intro he
    have := scs_lb_2_p22 s v p1 (p1 + 1) hs hvBBs (by rw [← hk]; exact Ne.symm hmod_ne_succ)
    rw [he, dist_self] at this
    linarith
  have hne_pred : v (p1 + (k - 1)) ≠ v p1 := by
    intro he
    have := scs_lb_2_p22 s v p1 (p1 + (k - 1)) hs hvBBs (by rw [← hk]; exact Ne.symm hmod_ne_pred)
    rw [he, dist_self] at this
    linarith
  -- pair-expansion of `hpair`
  have hcases : (v p0 = v (p1 + 1) ∧ v p2 = v (p1 + (k - 1))) ∨
      (v p0 = v (p1 + (k - 1)) ∧ v p2 = v (p1 + 1)) := by
    have h1 : v p0 ∈ ({v (p1 + 1), v (p1 + (k - 1))} : Set V3) := by
      rw [← hpair]; simp
    have h2 : v p2 ∈ ({v (p1 + 1), v (p1 + (k - 1))} : Set V3) := by
      rw [← hpair]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      have h3 : v (p1 + (k - 1)) ∈ ({v p0, v p2} : Set V3) := by rw [hpair]; simp
      have h3' : v (p1 + (k - 1)) = v (p1 + 1) := by
        have h := h3; rw [h1, h2] at h; simpa using h
      exact hdisj h3'
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exfalso
      have h3 : v (p1 + 1) ∈ ({v p0, v p2} : Set V3) := by rw [hpair]; simp
      have h3' : v (p1 + 1) = v (p1 + (k - 1)) := by
        have h := h3; rw [h1, h2] at h; simpa using h
      exact hdisj h3'.symm
  have hdeform : ∃ f : V3 → ℝ → V3, ∃ e' : ℝ, 0 < e' ∧ Deformation f V (-e') e' ∧
      (∀ w t, w ≠ v p1 → f w t = w) ∧
      (∀ t, |t| < e' → dist (v p0) (f (v p1) t) = dist (v p0) (v p1) ∧
        dist (v p2) (f (v p1) t) = dist (v p2) (v p1) - |t| ∧ ‖f (v p1) t‖ = ‖v p1‖) := by
    rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
    · obtain ⟨f, hf⟩ := deform_simplex_edge_exists_p21 V (fun t => -|t|) (fun _ => 0)
        (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) 1
      obtain ⟨e', he', hdef, hfix, hdist⟩ := hf hncop4 hups (by norm_num)
        (by fun_prop) (by fun_prop) (by simp) rfl
      refine ⟨f, e', he', hdef, hfix, ?_⟩
      intro t ht
      obtain ⟨hd1, hd2, hd3⟩ := hdist t ht
      refine ⟨?_, ?_, hd3⟩
      · rw [hp0]; simpa using hd2
      · rw [hp2]; simpa [sub_eq_add_neg] using hd1
    · obtain ⟨f, hf⟩ := deform_simplex_edge_exists_p21 V (fun _ => 0) (fun t => -|t|)
        (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) 1
      obtain ⟨e', he', hdef, hfix, hdist⟩ := hf hncop4 hups (by norm_num)
        (by fun_prop) (by fun_prop) rfl (by simp)
      refine ⟨f, e', he', hdef, hfix, ?_⟩
      intro t ht
      obtain ⟨hd1, hd2, hd3⟩ := hdist t ht
      refine ⟨?_, ?_, hd3⟩
      · rw [hp0]; simpa using hd1
      · rw [hp2]; simpa [sub_eq_add_neg] using hd2
  obtain ⟨f, e', he'pos, hdef, hfix, hdistf⟩ := hdeform
  have hfixb : ∀ t, f (v (p1 + 1)) t = v (p1 + 1) := fun t => hfix _ t hne_succ
  have hfixc : ∀ t, f (v (p1 + (k - 1))) t = v (p1 + (k - 1)) := fun t => hfix _ t hne_pred
  have hnormf : ∀ (i : ℕ) (t : ℝ), |t| < e' → ‖f (v i) t‖ = ‖v i‖ := by
    intro i t ht
    by_cases hi : v i = v p1
    · rw [hi]; exact (hdistf t ht).2.2
    · rw [hfix _ t hi]
  -- ## I. the moving azimuth stays in (0,π)
  have hdefsub : Deformation f ({v (p1 + (k - 1)), v p1, v (p1 + 1)} : Set V3) (-e') e' :=
    deformation_subset_p14 f _ V (-e') e' (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hvmem _
      · exact hvmem _
      · exact hvmem _) hdef
  obtain ⟨e1, he1, haz1⟩ := WNWSHJT_ALT_p21 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) f
    (-e') e' Real.pi hdefsub hncfan.2.1 hncfan.2.2 hposA hltA
  have haz1' : ∀ t, |t| < e1 → 0 < azim 0 (f (v p1) t) (v (p1 + 1)) (v (p1 + (k - 1))) ∧
      azim 0 (f (v p1) t) (v (p1 + 1)) (v (p1 + (k - 1))) < Real.pi := by
    intro t ht
    have h := haz1 t ht
    rwa [hfixb, hfixc] at h
  -- ═══ T0c: LEMMA_482 boxes, deltaY / upsX positivity, monotonicity witness
  have hk0pos : 0 < k := by omega
  have hnorm_lo : ∀ i : ℕ, 2 ≤ ‖v i‖ := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    linarith [h.1, h.2]
  have hnorm_hi : ∀ i : ℕ, ‖v i‖ ≤ 2 * h0 := by
    intro i
    have h := hann (Set.mem_range_self i)
    simp only [ballAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, not_lt] at h
    linarith [h.1, h.2]
  have hy4lo : 2 ≤ dist (v p1) (v p2) := by
    have h := (hbnd p1 p2).1
    rw [ha12] at h
    exact h
  have hy4hi : dist (v p1) (v p2) ≤ 2 * h0 := (hbnd p1 p2).2.trans hb12
  have hncop4' : ¬ Coplanar ({0, v p0, v p2, v p1} : Set V3) := by
    intro hc
    apply hncop
    rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
    · have hset : ({0, v p0, v p2, v p1} : Set V3) =
          {0, v p1, v (p1 + 1), v (p1 + (k - 1))} := by
        rw [hp0, hp2]
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at hc
    · have hset : ({0, v p0, v p2, v p1} : Set V3) =
          {0, v p1, v (p1 + 1), v (p1 + (k - 1))} := by
        rw [hp0, hp2]
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rwa [hset] at hc
  have hnc_412 : ¬ Coplanar ({0, v p0, v p1, v p2} : Set V3) := by
    intro hc
    apply hncop4'
    have hset : ({0, v p0, v p1, v p2} : Set V3) = {0, v p0, v p2, v p1} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [hset] at hc
  have hnc02 : ¬ Collinear3 0 (v p0) (v p2) :=
    (notcoplanar_imp_notcollinear_fan (x := (0 : V3)) (v := v p0) (u := v p2) (w := v p1)
      hncop4').2.1
  have hdYpos : 0 < deltaY ‖v p0‖ ‖v p2‖ ‖v p1‖ (dist (v p1) (v p2))
      (dist (v p0) (v p1)) (dist (v p0) (v p2)) := by
    have h := g482w3_deltaY_pos hncop4'
    rw [dist_comm (v p2) (v p1)] at h
    simpa [dist_eq_norm] using h
  have hu6 : 0 < upsX (‖v p0‖ * ‖v p0‖) (‖v p2‖ * ‖v p2‖)
      (dist (v p0) (v p2) * dist (v p0) (v p2)) := by
    have h := g482w3_upsX_pos_of_not_col hnc02
    simpa [dist_eq_norm, dist_comm] using h
  obtain ⟨aM, bM, hy4mem, hmono⟩ := LEMMA_4828966562_p22 h
    ‖v p0‖ ‖v p2‖ ‖v p1‖ (dist (v p1) (v p2)) (dist (v p0) (v p1)) (dist (v p0) (v p2))
    ⟨hnorm_lo p0, hnorm_hi p0⟩ ⟨hnorm_lo p2, hnorm_hi p2⟩ ⟨hnorm_lo p1, hnorm_hi p1⟩
    ⟨hy4lo, hy4hi⟩ ⟨h2, hdc⟩ h3 hdYpos hu6
  obtain ⟨haM, hbM⟩ := hy4mem

  -- ═══ T1: NONPLANAR_OPEN (coplanarity is open along the deformation)
  have hcont0 : ContinuousAt (fun t => f (v p1) t) 0 :=
    hdef.2.1 (v p1) (hvmem p1) 0 hdef.1
  obtain ⟨e2, he2, hnc2⟩ := NONPLANAR_OPEN_p14 (fun _ => (0 : V3))
    (fun t => f (v p1) t) (fun _ => v (p1 + (k - 1))) (fun _ => v (p1 + 1)) 0
    (by
      have hset : ({0, f (v p1) 0, v (p1 + (k - 1)), v (p1 + 1)} : Set V3) =
          {0, v p1, v (p1 + 1), v (p1 + (k - 1))} := by
        rw [hdef.2.2 (v p1) (hvmem p1)]
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset]; exact hncop)
    continuousAt_const hcont0 continuousAt_const continuousAt_const
  have hnc2' : ∀ t, |t| < e2 →
      ¬ Coplanar ({0, f (v p1) t, v (p1 + (k - 1)), v (p1 + 1)} : Set V3) := by
    intro t ht
    refine hnc2 t ?_
    simpa using ht


  -- ═══ mod-k bookkeeping helper
  have hmod_eq : ∀ {a b : ℕ}, v a = v b → a % k = b % k := by
    intro a b hab
    exact BBs_inj_p21 s v k hs hk.symm hvBBs (a % k) (b % k)
      (Nat.mod_lt _ hk0pos) (Nat.mod_lt _ hk0pos)
      (by rw [hmod a, hmod b, hab])
  -- ═══ T3a: dihV_obtuse_mono instantiated at the base tetrahedron
  obtain ⟨eM, heM, hM1full, hM2full⟩ :=
    dihV_obtuse_mono_p21 (0 : V3) (v p0) (v p1) (v p2) hnc_412
  have hposM : 0 < min (dist (v p1) (v p2) - aM) (bM - dist (v p1) (v p2)) :=
    lt_min (by linarith only [haM]) (by linarith only [hbM])
  -- ═══ T3: combined epsilon (haz / nonplanarity / deformation / dihV-mono / LEMMA_482 box)
  obtain ⟨e, he, hE1, hE2, hEe, hEM, hE5, hE6⟩ :=
    g482w3_eps6 e1 e2 e' eM
      (min (dist (v p1) (v p2) - aM) (bM - dist (v p1) (v p2)))
      (min (dist (v p1) (v p2) - aM) (bM - dist (v p1) (v p2)))
      he1 he2 he'pos heM hposM hposM
  -- the deformation restricted to the common radius
  have hdefe' : Deformation f (Set.range v) (-e') e' := by
    rw [← hV]; exact hdef
  have hde : Deformation f (Set.range v) (-e) e :=
    deformation_restrict_p21 e' f (Set.range v) e hdefe' he (fun t ht => hEe t ht)
  -- ═══ T2 preliminaries: base azim cycle partner, collinearity swap, azim→dihV bridges
  have hC_base : 0 < azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) ∧
      azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) < Real.pi :=
    (g482w3_azim_cycle (x := v p1) (y := v (p1 + 1)) (z := v (p1 + (k - 1)))
      hncfan.2.1 hncfan.2.2 hposA hltA).2
  have hcswap : ∀ {a b c : V3}, Collinear3 a b c → Collinear3 a c b := by
    intro a b c h
    unfold Collinear3 at *
    rw [show ({a, c, b} : Set V3) = {a, b, c} from by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact h
  have hbr1 : ∀ t, |t| < e → azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + 1)) =
      dihV 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + 1)) := by
    intro t ht
    have hnc := hnc2' t (hE2 t ht)
    have hnc' := notcoplanar_imp_notcollinear_fan hnc
    have hcyc := g482w3_azim_cycle (x := f (v p1) t) (y := v (p1 + 1))
      (z := v (p1 + (k - 1))) hnc'.2.2 hnc'.2.1
      (haz1' t (hE1 t ht)).1 (haz1' t (hE1 t ht)).2
    exact AZIM_DIHV_SAME_STRONG (fun h => hnc'.2.1 (hcswap h)) hnc'.1
      (le_of_lt hcyc.2.2)
  have hbr1b : azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) =
      dihV 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) :=
    AZIM_DIHV_SAME_STRONG (fun h => hncfan.2.2 (hcswap h))
      (fun h => hncfan.1 (hcswap h)) (le_of_lt hC_base.2)
  have hbr2 : ∀ t, |t| < e → azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t) =
      dihV 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t) := by
    intro t ht
    have hnc := hnc2' t (hE2 t ht)
    have hnc' := notcoplanar_imp_notcollinear_fan hnc
    have hcyc := g482w3_azim_cycle (x := f (v p1) t) (y := v (p1 + 1))
      (z := v (p1 + (k - 1))) hnc'.2.2 hnc'.2.1
      (haz1' t (hE1 t ht)).1 (haz1' t (hE1 t ht)).2
    exact AZIM_DIHV_SAME_STRONG hncfan.1 (fun h => hnc'.2.2 (hcswap h))
      (le_of_lt hcyc.1.2)
  have hbr2b : azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1) =
      dihV 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1) :=
    AZIM_DIHV_SAME_STRONG hncfan.1 (fun h => hncfan.2.1 (hcswap h))
      (le_of_lt hB_base.2)
  -- the two dihV monotonicity corollaries at `X = f (v p1) t`, `t = -|t|`
  have hM1t : Real.pi / 2 < dihV 0 (v p1) (v p2) (v p0) → ∀ t, |t| < e →
      dihV 0 (v p2) (f (v p1) t) (v p0) ≤ dihV 0 (v p2) (v p1) (v p0) := by
    intro hobtD t ht
    refine hM1full hobtD (f (v p1) t) (-|t|) (by simpa using hEM t ht)
      (by linarith only [abs_nonneg t]) ?_ ?_ ?_
    · simpa [dist_eq_norm] using hnormf p1 t (hEe t ht)
    · exact (hdistf t (hEe t ht)).1
    · rw [dist_comm (f (v p1) t) (v p2), (hdistf t (hEe t ht)).2.1,
        dist_comm (v p1) (v p2), sub_eq_add_neg]
  have hM2t : ∀ t, |t| < e →
      dihV 0 (v p0) (f (v p1) t) (v p2) ≤ dihV 0 (v p0) (v p1) (v p2) := by
    intro t ht
    refine hM2full (f (v p1) t) (-|t|) (by simpa using hEM t ht)
      (by linarith only [abs_nonneg t]) ?_ ?_ ?_
    · simpa [dist_eq_norm] using hnormf p1 t (hEe t ht)
    · exact (hdistf t (hEe t ht)).1
    · rw [dist_comm (f (v p1) t) (v p2), (hdistf t (hEe t ht)).2.1,
        dist_comm (v p1) (v p2), sub_eq_add_neg]
  -- the interior-angle form of the base azimuth at `v p2`
  have hrho2 : rhoNode1 FF (v p2) = v (p2 + 1) := by
    have hp := VV_SUC_EQ_RHO_NODE_PRIME_p35 s k p2 p2 0 (v p2) V E FF v
      hk.symm rfl hV.symm hE.symm hFF.symm hs hnk hvBBs 1
    simp only [Function.iterate_one] at hp
    simpa [Nat.add_comm] using hp
  have hivs2 : ivsRhoNode1 FF (v p2) = v (p2 + (k - 1)) :=
    VV_SUC_EQ_IVS_RHO_NODE_PRIME_p21 V E FF s v (v p2) k p2
      hk.symm rfl hV.symm hE.symm hFF.symm hs hnk hvBBs
  have hIA2 : interiorAngle1 0 FF (v p2) = azim 0 (v p2) (v (p2 + 1)) (v (p2 + (k - 1))) := by
    rw [interior_angle1_azim_p21 V E FF (v p2) hlf (hvmem p2), hrho2, hivs2]
  -- ═══ T2: the two azimuth-monotonicity disjunctions
  have hdisjM : (azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + (k - 2))) < Real.pi ∨
      ∃ eps, 0 < eps ∧ ∀ t, |t| < eps →
        azim 0 (v (p1 + (k - 1))) (f (v p1) t) (v (p1 + 1)) ≤
          azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1))) ∧
    (azim 0 (v (p1 + 1)) (v (p1 + 2)) (v p1) < Real.pi ∨
      ∃ eps, 0 < eps ∧ ∀ t, |t| < eps →
        azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t) ≤
          azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1)) := by
    by_cases hobt : Real.pi / 2 < interiorAngle1 0 FF (v p1)
    · -- obtuse branch: both monotone alternatives, via hM1/hM2
      have hobtD : Real.pi / 2 < dihV 0 (v p1) (v p2) (v p0) := by
        have h1 : azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) =
            dihV 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) :=
          AZIM_DIHV_SAME_STRONG hncfan.2.1 hncfan.2.2 (le_of_lt hltA)
        have h2 : Real.pi / 2 < dihV 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) := by
          have hh := hobt
          rw [hazim_base, h1] at hh
          exact hh
        have hpairdih : dihV 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) =
            dihV 0 (v p1) (v p2) (v p0) := by
          rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
          · rw [hp0, hp2]
            exact (DIHV_SYM_2 0 (v p1) (v (p1 + (k - 1))) (v (p1 + 1))).symm
          · rw [hp0, hp2]
        rw [← hpairdih]
        exact h2
      have hM1 := hM1t hobtD
      constructor
      · refine Or.inr ⟨e, he, fun t ht => ?_⟩
        rw [hbr1 t ht, hbr1b]
        rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
        · rw [← hp0, ← hp2]
          exact hM1 t ht
        · rw [← hp0, ← hp2]
          exact hM2t t ht
      · refine Or.inr ⟨e, he, fun t ht => ?_⟩
        rw [hbr2 t ht, hbr2b]
        rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
        · rw [← hp0, ← hp2, DIHV_SYM_2 0 (v p0) (v p2) (f (v p1) t),
            DIHV_SYM_2 0 (v p0) (v p2) (v p1)]
          exact hM2t t ht
        · rw [← hp0, ← hp2, DIHV_SYM_2 0 (v p2) (v p0) (f (v p1) t),
            DIHV_SYM_2 0 (v p2) (v p0) (v p1)]
          exact hM1 t ht
    · -- non-obtuse branch: one first disjunct (interior angle at `v p2`) + one monotone
      have hia2 : interiorAngle1 0 FF (v p2) < Real.pi := by
        rcases hcase with h | h
        · exact absurd h hobt
        · exact h
      constructor
      · rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
        · refine Or.inl ?_
          have hs1 : v (p2 + 1) = v p1 := by
            rw [← hmod (p2 + 1), ← hmod p1]
            congr 1
            rw [Nat.add_mod, hmod_eq hp2, ← Nat.add_mod,
              show p1 + (k - 1) + 1 = p1 + k by omega, Nat.add_mod_right]
          have hs2 : v (p2 + (k - 1)) = v (p1 + (k - 2)) := by
            rw [← hmod (p2 + (k - 1)), ← hmod (p1 + (k - 2))]
            congr 1
            rw [Nat.add_mod, hmod_eq hp2, ← Nat.add_mod,
              show p1 + (k - 1) + (k - 1) = (p1 + (k - 2)) + k by omega,
              Nat.add_mod_right]
          rw [hIA2, hp2, hs1, hs2] at hia2
          exact hia2
        · refine Or.inr ⟨e, he, fun t ht => ?_⟩
          rw [hbr1 t ht, hbr1b, ← hp0, ← hp2]
          exact hM2t t ht
      · rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
        · refine Or.inr ⟨e, he, fun t ht => ?_⟩
          rw [hbr2 t ht, hbr2b, ← hp0, ← hp2,
            DIHV_SYM_2 0 (v p0) (v p2) (f (v p1) t),
            DIHV_SYM_2 0 (v p0) (v p2) (v p1)]
          exact hM2t t ht
        · refine Or.inl ?_
          have hs1 : v (p2 + 1) = v (p1 + 2) := by
            rw [← hmod (p2 + 1), ← hmod (p1 + 2)]
            congr 1
            rw [Nat.add_mod, hmod_eq hp2, ← Nat.add_mod,
              show p1 + 1 + 1 = p1 + 2 by omega]
          have hs2 : v (p2 + (k - 1)) = v p1 := by
            rw [← hmod (p2 + (k - 1)), ← hmod p1]
            congr 1
            rw [Nat.add_mod, hmod_eq hp2, ← Nat.add_mod,
              show p1 + 1 + (k - 1) = p1 + k by omega, Nat.add_mod_right]
          rw [hIA2, hp2, hs1, hs2] at hia2
          exact hia2
  -- ═══ T4: the azimuth assumption reduction
  obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, ⟨eA8, heA8, hA8⟩, hA9⟩ :=
    azim_assumption_reduction_p21 s k p1 f v e hs hk.symm hvBBs hgen hk3 hncop hde
      hfix hltA hdisjM.1 hdisjM.2
  -- ═══ psort alignment for the a-reduction
  have hpsort_eq : psort k (p0, p2) = psort k (p1 + 1, p1 + (k - 1)) := by
    rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
    · have h1 : p0 % k = (p1 + 1) % k := hmod_eq hp0
      have h2 : p2 % k = (p1 + (k - 1)) % k := hmod_eq hp2
      rw [← psort_mod_p21 k p0 p2 hk0, ← psort_mod_p21 k (p1 + 1) (p1 + (k - 1)) hk0,
        h1, h2]
    · have h1 : p0 % k = (p1 + (k - 1)) % k := hmod_eq hp0
      have h2 : p2 % k = (p1 + 1) % k := hmod_eq hp2
      rw [← psort_mod_p21 k p0 p2 hk0, ← psort_mod_p21 k (p1 + 1) (p1 + (k - 1)) hk0,
        h1, h2, g482w3_psort_swap k ((p1 + (k - 1)) % k) ((p1 + 1) % k)]
  have hdiagA : ∀ i j, scsDiag k i j → psort k (i, j) ≠ psort k (p1 + 1, p1 + (k - 1)) →
      s.a i j < dist (v i) (v j) := by
    intro i j hd hps
    exact ha i j hd (by
      intro h
      rw [hpsort_eq] at h
      exact hps h)
  -- strictness on the moving edge (from `2 ≤ dist` and `dist ≠ 2`)
  have hy4gt2 : 2 < dist (v p1) (v p2) :=
    lt_of_le_of_ne hy4lo (fun h => hne h.symm)
  -- periodic transport of the a-table
  have hsK := hs
  obtain ⟨-, -, -, -, -, -, -, hpa0, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hsK
  have hpa : Periodic2 s.a k := by
    rw [← hk] at hpa0
    exact hpa0
  have hamod : ∀ i j, s.a i j = s.a (i % k) (j % k) :=
    fun i j => periodic2_MOD_p21 (a := s.a) (i := i) (j := j) (k := k) hk0 hpa
  -- ═══ T5: a/b skeletons
  have ha1 : ∃ eps, 0 < eps ∧ (s.a p1 (p1 + 1) = dist (v p1) (v (p1 + 1)) →
      ∀ t, |t| < eps →
        s.a p1 (p1 + 1) ≤ dist (f (v p1) t) (f (v (p1 + 1)) t)) := by
    rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
    · have hkey : ∀ t, |t| < e' → dist (f (v p1) t) (v (p1 + 1)) =
          dist (v p1) (v (p1 + 1)) := by
        intro t ht
        have hd := (hdistf t ht).1
        rw [← hp0, dist_comm (f (v p1) t) (v p0), hd, dist_comm (v p0) (v p1)]
      refine ⟨e, he, fun heq t ht => ?_⟩
      rw [hfixb t, hkey t (hEe t ht), heq]
    · have haeq : s.a p1 (p1 + 1) = s.a p1 p2 := by
        have hmk : (p1 + 1) % k = p2 % k := (hmod_eq hp2).symm
        rw [hamod p1 (p1 + 1), hamod p1 p2, hmk]
      have hlt2 : s.a p1 (p1 + 1) < dist (v p1) (v (p1 + 1)) := by
        rw [haeq, ha12, ← hp2]
        exact hy4gt2
      exact ⟨e, he, fun heq t ht => absurd heq (ne_of_lt hlt2)⟩
  have ha2 : ∃ eps, 0 < eps ∧ (s.a p1 (p1 + (k - 1)) = dist (v p1) (v (p1 + (k - 1))) →
      ∀ t, |t| < eps →
        s.a p1 (p1 + (k - 1)) ≤ dist (f (v p1) t) (f (v (p1 + (k - 1))) t)) := by
    rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
    · have haeq : s.a p1 (p1 + (k - 1)) = s.a p1 p2 := by
        have hmk : (p1 + (k - 1)) % k = p2 % k := (hmod_eq hp2).symm
        rw [hamod p1 (p1 + (k - 1)), hamod p1 p2, hmk]
      have hlt2 : s.a p1 (p1 + (k - 1)) < dist (v p1) (v (p1 + (k - 1))) := by
        rw [haeq, ha12, ← hp2]
        exact hy4gt2
      exact ⟨e, he, fun heq t ht => absurd heq (ne_of_lt hlt2)⟩
    · have hkey : ∀ t, |t| < e' → dist (f (v p1) t) (v (p1 + (k - 1))) =
          dist (v p1) (v (p1 + (k - 1))) := by
        intro t ht
        have hd := (hdistf t ht).1
        rw [← hp0, dist_comm (f (v p1) t) (v p0), hd, dist_comm (v p0) (v p1)]
      refine ⟨e, he, fun heq t ht => ?_⟩
      rw [hfixc t, hkey t (hEe t ht), heq]
  have hb1 : ∃ eps, 0 < eps ∧ (dist (v p1) (v (p1 + 1)) = s.b p1 (p1 + 1) →
      ∀ t, |t| < eps →
        dist (f (v p1) t) (f (v (p1 + 1)) t) ≤ s.b p1 (p1 + 1)) := by
    rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
    · have hkey : ∀ t, |t| < e' → dist (f (v p1) t) (v (p1 + 1)) =
          dist (v p1) (v (p1 + 1)) := by
        intro t ht
        have hd := (hdistf t ht).1
        rw [← hp0, dist_comm (f (v p1) t) (v p0), hd, dist_comm (v p0) (v p1)]
      refine ⟨e, he, fun heq t ht => ?_⟩
      rw [hfixb t, hkey t (hEe t ht), heq]
    · have hle : ∀ t, |t| < e' → dist (f (v p1) t) (v (p1 + 1)) ≤
          dist (v p1) (v (p1 + 1)) := by
        intro t ht
        rw [← hp2, dist_comm (f (v p1) t) (v p2), (hdistf t ht).2.1,
          dist_comm (v p1) (v p2)]
        linarith only [abs_nonneg t]
      refine ⟨e, he, fun heq t ht => ?_⟩
      rw [hfixb t]
      have h := hle t (hEe t ht)
      rw [heq] at h
      exact h
  have hb2 : ∃ eps, 0 < eps ∧ (dist (v p1) (v (p1 + (k - 1))) = s.b p1 (p1 + (k - 1)) →
      ∀ t, |t| < eps →
        dist (f (v p1) t) (f (v (p1 + (k - 1))) t) ≤ s.b p1 (p1 + (k - 1))) := by
    rcases hcases with ⟨hp0, hp2⟩ | ⟨hp0, hp2⟩
    · have hle : ∀ t, |t| < e' → dist (f (v p1) t) (v (p1 + (k - 1))) ≤
          dist (v p1) (v (p1 + (k - 1))) := by
        intro t ht
        rw [← hp2, dist_comm (f (v p1) t) (v p2), (hdistf t ht).2.1,
          dist_comm (v p1) (v p2)]
        linarith only [abs_nonneg t]
      refine ⟨e, he, fun heq t ht => ?_⟩
      rw [hfixc t]
      have h := hle t (hEe t ht)
      rw [heq] at h
      exact h
    · have hkey : ∀ t, |t| < e' → dist (f (v p1) t) (v (p1 + (k - 1))) =
          dist (v p1) (v (p1 + (k - 1))) := by
        intro t ht
        have hd := (hdistf t ht).1
        rw [← hp0, dist_comm (f (v p1) t) (v p0), hd, dist_comm (v p0) (v p1)]
      refine ⟨e, he, fun heq t ht => ?_⟩
      rw [hfixc t, hkey t (hEe t ht), heq]
  have haSkel := a_assumption_reduction_p21 s k p1 f v e hs hk.symm hvBBs hk3
    hdiagA hde hfix ha1 ha2
  have hbSkel := b_assumption_reduction_p21 s k p1 f v e hs hk.symm hvBBs hk3
    hb hde hfix hb1 hb2
  -- ═══ T6: the deformed configuration is again in BBs
  obtain ⟨eBB, heBB, hBBsALT⟩ := deformation_BBs_ALT_p21 s k f v e hs hk.symm hk3
    hvBBs hgen he hde hA7 (fun i t ht => hnormf i t (hEe t ht)) haSkel hbSkel
  -- ═══ T7: minimality of the tau sum
  have hvBP : v ∈ BBprimeV39 s := ⟨hvBBs, hvmin, hvneg⟩
  have hsum : ∀ t, |t| < eBB →
      setSum {i | i < k}
          (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + (k - 1)))) ≤
        setSum {i | i < k}
          (fun i => rhoFun ‖f (v i) t‖ * azim 0 (f (v i) t) (f (v (i + 1)) t)
            (f (v (i + (k - 1))) t)) := by
    intro t ht
    exact MMs_minimize_tau_fun_p21 s k v (fun i => f (v i) t) hs hbasic hk.symm hk3
      hvBP (hBBsALT t ht)
  -- ═══ T8: the finite-sum surgery at some small nonzero `t'`
  set eF : ℝ := min (min e eBB) eA8 with heFdef
  have heF : 0 < eF := lt_min (lt_min he heBB) heA8
  have heFe : eF ≤ e := le_trans (min_le_left _ _) (min_le_left _ _)
  have heFeBB : eF ≤ eBB := le_trans (min_le_left _ _) (min_le_right _ _)
  have heFeA8 : eF ≤ eA8 := min_le_right _ _
  obtain ⟨t', ht'F, ht'ne⟩ : ∃ t' : ℝ, |t'| < eF ∧ t' ≠ 0 := by
    refine ⟨eF / 2, ?_, ?_⟩
    · rw [abs_of_pos (by linarith only [heF])]
      linarith only [heF]
    · intro h
      linarith only [heF, h]
  have ht'e : |t'| < e := lt_of_lt_of_le ht'F heFe
  have ht'eBB : |t'| < eBB := lt_of_lt_of_le ht'F heFeBB
  have ht'A8 : |t'| < eA8 := lt_of_lt_of_le ht'F heFeA8
  have ht1' : |t'| < e1 := hE1 t' ht'e
  have ht2' : |t'| < e2 := hE2 t' ht'e
  have htabs : 0 < |t'| := abs_pos.mpr ht'ne
  have hA8t := hA8 t' ht'A8
  have hA8a := hA8t.1
  have hA8b := hA8t.2
  have hnr : ‖f (v p1) t'‖ = ‖v p1‖ := hnormf p1 t' (hEe t' ht'e)
  have hd1 : dist (f (v p1) t') (v p2) = dist (v p1) (v p2) - |t'| := by
    rw [dist_comm (f (v p1) t') (v p2), (hdistf t' (hEe t' ht'e)).2.1,
      dist_comm (v p1) (v p2)]
  have hd2 : dist (v p0) (f (v p1) t') = dist (v p0) (v p1) :=
    (hdistf t' (hEe t' ht'e)).1
  have hncM : ¬ Coplanar ({0, f (v p1) t', v (p1 + 1), v (p1 + (k - 1))} : Set V3) := by
    have h := hnc2' t' ht2'
    rw [show ({0, f (v p1) t', v (p1 + (k - 1)), v (p1 + 1)} : Set V3) =
        {0, f (v p1) t', v (p1 + 1), v (p1 + (k - 1))} from by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl | rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inr (Or.inr (Or.inl rfl))
      · rintro (rfl | rfl | rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inr (Or.inr (Or.inl rfl))] at h
    exact h
  have htau_m : tau3 (f (v p1) t') (v (p1 + 1)) (v (p1 + (k - 1))) =
      taum ‖v p0‖ ‖v p2‖ ‖v p1‖ (dist (v p1) (v p2) - |t'|)
        (dist (v p0) (v p1)) (dist (v p0) (v p2)) := by
    rw [tau3_taum_nonplanar_p21 _ _ _ hncM]
    rw [g482w3_taum4 (f (v p1) t') (v (p1 + 1)) (v (p1 + (k - 1))) (v p0) (v p2) hdisj.symm hpair,
      hnr, hd1, hd2]
  have htau_v : tau3 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) =
      taum ‖v p0‖ ‖v p2‖ ‖v p1‖ (dist (v p1) (v p2))
        (dist (v p0) (v p1)) (dist (v p0) (v p2)) := by
    rw [tau3_taum_nonplanar_p21 _ _ _ hncop]
    rw [g482w3_taum4 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) (v p0) (v p2) hdisj.symm hpair]
  -- the two `taum` reductions of the three-point sums
  have hred_v : rhoFun ‖v p1‖ * azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1)))
      + rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1)
      + rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1))
      = taum ‖v p0‖ ‖v p2‖ ‖v p1‖ (dist (v p1) (v p2))
          (dist (v p0) (v p1)) (dist (v p0) (v p2)) + (Real.pi + sol0) := by
    have h3a := tau3_azim_p21 (v p1) (v (p1 + 1)) (v (p1 + (k - 1))) hncop (le_of_lt hltA)
    rw [htau_v] at h3a
    rw [h3a]
    simp only [rho_rho_fun]
    ring
  have hred_m : rhoFun ‖v p1‖ * azim 0 (f (v p1) t') (v (p1 + 1)) (v (p1 + (k - 1)))
      + rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t')
      + rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (f (v p1) t') (v (p1 + 1))
      = taum ‖v p0‖ ‖v p2‖ ‖v p1‖ (dist (v p1) (v p2) - |t'|)
          (dist (v p0) (v p1)) (dist (v p0) (v p2)) + (Real.pi + sol0) := by
    have hazle : azim 0 (f (v p1) t') (v (p1 + 1)) (v (p1 + (k - 1))) ≤ Real.pi :=
      le_of_lt (haz1' t' ht1').2
    have h3a := tau3_azim_p21 (f (v p1) t') (v (p1 + 1)) (v (p1 + (k - 1))) hncM hazle
    rw [htau_m] at h3a
    rw [h3a]
    simp only [rho_rho_fun, hnr]
    ring
  -- the strict `taum` drop transported to the reduced sums
  have hlt : rhoFun ‖v p1‖ * azim 0 (f (v p1) t') (v (p1 + 1)) (v (p1 + (k - 1)))
      + rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (f (v p1) t')
      + rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (f (v p1) t') (v (p1 + 1))
      < rhoFun ‖v p1‖ * azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1)))
      + rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + (k - 1))) (v p1)
      + rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + 1)) := by
    have hτ : taum ‖v p0‖ ‖v p2‖ ‖v p1‖ (dist (v p1) (v p2) - |t'|)
          (dist (v p0) (v p1)) (dist (v p0) (v p2))
        < taum ‖v p0‖ ‖v p2‖ ‖v p1‖ (dist (v p1) (v p2))
          (dist (v p0) (v p1)) (dist (v p0) (v p2)) := by
      refine hmono (dist (v p1) (v p2) - |t'|) (dist (v p1) (v p2))
        ⟨?_, ?_⟩ ⟨haM, hbM⟩ ?_
      · have hlt5 := hE5 t' ht'e
        have hmin := lt_of_lt_of_le hlt5
          (min_le_left (dist (v p1) (v p2) - aM) (bM - dist (v p1) (v p2)))
        linarith only [hmin]
      · linarith only [hbM, abs_nonneg t']
      · linarith only [htabs]
    linarith only [hred_v, hred_m, hτ]
  -- the three-point sums
  set T : Finset ℕ := ({p1 % k, (p1 + 1) % k, (p1 + (k - 1)) % k} : Finset ℕ) with hTdef
  have hTsub : T ⊆ Finset.range k := by
    intro i hi
    rw [hTdef] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact Finset.mem_range.mpr (Nat.mod_lt _ hk0pos)
  have hthree_v : ∑ i ∈ T,
        rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + (k - 1)))
      = rhoFun ‖v p1‖ * azim 0 (v p1) (v (p1 + 1)) (v (p1 + (k - 1)))
        + rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + 2)) (v p1)
        + rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (v p1) (v (p1 + (k - 2))) := by
    rw [hTdef]
    exact g482w3_sum_T_G v hk3 hperv
  have hthree_f : ∑ i ∈ T,
        rhoFun ‖f (v i) t'‖ * azim 0 (f (v i) t') (f (v (i + 1)) t')
          (f (v (i + (k - 1))) t')
      = rhoFun ‖f (v p1) t'‖ * azim 0 (f (v p1) t') (v (p1 + 1)) (v (p1 + (k - 1)))
        + rhoFun ‖v (p1 + 1)‖ * azim 0 (v (p1 + 1)) (v (p1 + 2)) (f (v p1) t')
        + rhoFun ‖v (p1 + (k - 1))‖ * azim 0 (v (p1 + (k - 1))) (f (v p1) t') (v (p1 + (k - 2))) := by
    rw [hTdef]
    exact g482w3_sum_T_H f v t' hk3 hperv (hA9 t').1 (hA9 t').2.2.2
      (hA9 t').2.1 (hA9 t').2.2.1
  have hS_v : setSum {i | i < k}
        (fun i => rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + (k - 1))))
      = ∑ i ∈ (Finset.range k \ T),
          rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + (k - 1)))
        + ∑ i ∈ T, rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) := by
    rw [g482w3_setSum_range]
    exact (Finset.sum_sdiff hTsub).symm
  have hS_f : setSum {i | i < k}
        (fun i => rhoFun ‖f (v i) t'‖ * azim 0 (f (v i) t') (f (v (i + 1)) t')
          (f (v (i + (k - 1))) t'))
      = ∑ i ∈ (Finset.range k \ T),
          rhoFun ‖f (v i) t'‖ * azim 0 (f (v i) t') (f (v (i + 1)) t')
            (f (v (i + (k - 1))) t')
        + ∑ i ∈ T, rhoFun ‖f (v i) t'‖ * azim 0 (f (v i) t') (f (v (i + 1)) t')
            (f (v (i + (k - 1))) t') := by
    rw [g482w3_setSum_range]
    exact (Finset.sum_sdiff hTsub).symm
  -- the complement sum is frozen
  have hSc : ∑ i ∈ (Finset.range k \ T),
        rhoFun ‖f (v i) t'‖ * azim 0 (f (v i) t') (f (v (i + 1)) t')
          (f (v (i + (k - 1))) t')
      = ∑ i ∈ (Finset.range k \ T),
        rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_sdiff, Finset.mem_range] at hi
    rw [hTdef] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    obtain ⟨hiT, h1i, h2i, h3i⟩ := hi
    have hmod1 : p1 % k ≠ i % k := by
      intro hh
      exact h1i (by rw [← Nat.mod_eq_of_lt hiT]; exact hh.symm)
    have hmod2 : p1 % k ≠ (i + 1) % k := by
      intro hh
      have hm : i = (p1 + (k - 1)) % k := by
        have hcalc : (p1 + (k - 1)) % k = ((i + 1) + (k - 1)) % k := by
          rw [Nat.add_mod p1 (k - 1) k, hh, ← Nat.add_mod (i + 1) (k - 1) k]
        rw [hcalc, show i + 1 + (k - 1) = i + k by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hiT]
      exact h3i hm
    have hmod3 : p1 % k ≠ (i + (k - 1)) % k := by
      intro hh
      have hm : i = (p1 + 1) % k := by
        have hcalc : (p1 + 1) % k = ((i + (k - 1)) + 1) % k := by
          rw [Nat.add_mod p1 1 k, hh, ← Nat.add_mod (i + (k - 1)) 1 k]
        rw [hcalc, show i + (k - 1) + 1 = i + k by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hiT]
      exact h2i hm
    have hvi : v i ≠ v p1 := fun hv => hmod1 (hmod_eq hv).symm
    rw [hA3 i t' hmod1 hmod2 hmod3, hfix (v i) t' hvi]
  -- the strict drop on the three-point block
  have hSt : ∑ i ∈ T,
        rhoFun ‖f (v i) t'‖ * azim 0 (f (v i) t') (f (v (i + 1)) t')
          (f (v (i + (k - 1))) t')
      < ∑ i ∈ T, rhoFun ‖v i‖ * azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) := by
    have hnr' : rhoFun ‖f (v p1) t'‖ = rhoFun ‖v p1‖ := by rw [hnr]
    rw [hthree_f, hnr', hA8b, hA8a, hthree_v, hA2, hA1]
    linarith only [hlt]
  -- close: minimality contradicts the strict drop
  have hsum_t := hsum t' ht'eBB
  rw [hS_v, hS_f, hSc] at hsum_t
  linarith only [hsum_t, hSt]

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
