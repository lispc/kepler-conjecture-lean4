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
    (proved), `simplex_unique_p21` (sorry), `re_eqvl_pos_pos_p21` (proved),
    `mk_simplex_uniq_p21` (sorry).
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
  Section E (BBs/fan transport): `VV_SUC_EQ_IVS_RHO_NODE_PRIME_p21` (sorry),
    `vv_azim_le_alt_p21`, `vv_split_azim_alt_p21` (sorry),
    `interior_angle1_azim_p21`, `LOFA_IMP_INANGLE_EQ_AZIM_IVS_p21`
    (proved, definitional), `BBs_inj_p21` (proved), `IMAGE_FF_p21` (proved),
    `interior_angle1_azim_scs_p21` (sorry), `deformation_BBs_p21`,
    `deformation_BBs_ALT_p21` (sorry giants).
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
    `tau3_taum_nonplanar_p21`, `tau3_azim_p21` (sorry),
    `general_482_deformation_p21` (sorry giant), `CUXVZOZ_p21` and
    `CJBDXXN_p21` (each from `general_482_deformation_p21` by instantiating
    `p0`/`p2` — the HOL proofs are exactly these substitutions).

ENCODING NOTES
  - Import discipline: this file sits on the LocalAuto1/`PackingAuto18` side
    of the fatal `atn2` duplication. LocalAuto2/PackingAuto20 and everything
    importing them (LocalAuto9/LocalAuto11, hence `mkSimplex1_p11`,
    `taum_p11` and the PQCSXWG/`delta_x_sym` kit) must NOT be imported; the
    LocalAuto1-side twins `mkSimplex1`, `mkPlanar2`, `deltaX4`, `deltaX5`
    (LocalAuto1) and `upsX`/`deltaX` (PackingAuto18) are used instead.
    Same-wave lanes LocalAuto19/20/22-27 are NOT imported.
  - HOL `real^3` ↔ `V3` (Kepler.Geom); `vec 0` ↔ `0`; `a cross b` ↔
    `cross3 a b` (PackingAuto18:86); `dot` ↔ `⬝ᵥ`; `%` ↔ `•`; `dist (a,b)`
    ↔ `dist a b`; `norm` ↔ `‖·‖`; `pow 2` ↔ `^ 2`; `collinear {a,b,c}` ↔
    `Collinear ℝ {a,b,c}`; `coplanar s` ↔ `Coplanar s` (Geom.Coplanar,
    "⊂ affineSpan of three points").
  - `dih_x` ↔ `dihXf_p16`, `dih_y` ↔ `dihY_p16`, `taum` ↔ `taum_p16`
    (LocalAuto16 `_p16` sphere-kit copies; LocalAuto16 imports LocalAuto1 so
    it is on this side of the `atn2` split). `delta_x` ↔ `deltaX`
    (PackingAuto18). `delta_x5`/`delta_x6` are carried as verbatim `_p21`
    copies below: `deltaX5_p21` follows `Nonlin_def.delta_x5`
    (nonlin_def.hl:435) which is the form `delta_x5_delta_x6` rewrites with;
    NOTE the existing LocalAuto1 `deltaX5` drops the `- x1 * x3 + x1 * x4`
    terms — NEEDS: reconcile at merge. `delta_x6` (sphere.hl:114) was not
    ported before.
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
    `mainNonlinearTerminalV11_p21 := ∀ y, MainNonlinearTerminalV11 y`
    (anchor below; twin of LocalAuto18's `_p18` rendering). NEEDS: merge.
  - The HOL source's `let assumptions = ...` (CUXVZOZ.hl:2391) is a term
    abbreviation, not a theorem — not ported. The `//`-commented azim
    assumption inside `deformation_BBs` is dropped as in the source.
  - No `native_decide` anywhere; `sorry` bodies carry `-- DISCHARGES:`
    markers naming the missing HOL inputs.
-/

import Kepler.Text.LocalAuto1
import Kepler.Text.LocalAuto16
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Section 0: `_p21` copies and anchors -/

/-- HOL `delta_x5` (nonlin_def.hl:435, `Nonlin_def.delta_x5`): partial
derivative of `delta_x` at `x5`. Verbatim copy; NOTE LocalAuto1's `deltaX5`
omits the `- x1 * x3 + x1 * x4` summands. NEEDS: merge/reconcile. -/
noncomputable def deltaX5_p21 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x1 * x3 + x1 * x4 - x2 * x5 + x3 * x6 - x4 * x6 +
    x2 * (x1 - x2 + x3 + x4 - x5 + x6)

/-- HOL `delta_x6` (sphere.hl:114): partial derivative of `delta_x` at
`x6`; not previously ported. NEEDS: merge. -/
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

/-- HOL `main_nonlinear_terminal_v11` (terminal.hl:37, bare Prop); rendered
as the closed conjunction over the `MainNonlinearTerminalV11_p21` anchor box.
Twin of LocalAuto18's `mainNonlinearTerminalV11_p18`. NEEDS: merge. -/
def mainNonlinearTerminalV11_p21 : Prop := ∀ y : Fin 6 → ℝ, MainNonlinearTerminalV11_p21 y

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
  -- DISCHARGES: HOL Pqcsxwg.PQCSXWG1 and Merge_ineq.delta_x_sym — the
  -- PQCSXWG lane lives on the LocalAuto11/LocalAuto2 side of the `atn2`
  -- split and is not importable here. NEEDS: merge with that lane.
  sorry

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
  -- DISCHARGES: HOL proof over Trigonometry2.NONCOPLANAR_3_BASIS,
  -- Local_lemmas.NOT_COLL_IMP_COPL, `homog_2x2` and the Pythagorean
  -- decomposition `NORM_ADD_PYTHAGOREAN`; geometry engine absent here.
  -- NEEDS: port the basis-expansion argument on the LocalAuto1 side.
  sorry

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
  -- DISCHARGES: HOL Pqcsxwg.PQCSXWG1 + Oxlzlez.coplanar_delta_y
  -- (`delta_y > 0` off non-coplanarity) + `re_eqvl_pos_pos`; the coplanar
  -- delta_y criterion is not on this side of the `atn2` split.
  -- NEEDS: merge with the PQCSXWG/Oxlzlez lanes.
  sorry

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
  -- DISCHARGES: HOL `deform_simplex_decrease_edge23`, the 170-line
  -- continuity + PQCSXWG2_ATREAL + Zlzthic.NONPLANAR_OPEN argument.
  -- NEEDS: the PQCSXWG lane (LocalAuto11 side) and NONPLANAR_OPEN.
  sorry

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
  -- DISCHARGES: HOL `deform_simplex_684_pent` (270 lines): two stacked
  -- `mk_simplex1` decreases plus coplanarity/continuity management.
  -- NEEDS: same PQCSXWG/NONPLANAR_OPEN kit as the edge23 giant.
  sorry

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

/-- HOL `mk_planar_unique` (CUXVZOZ.hl:839): a planar completion is
uniquely determined by distances and the cross-product ray. -/
theorem mk_planar_unique_p21 (v0 v1 v2 v3 v3' : V3)
    (hnc : ¬ Collinear ℝ ({v0, v1, v2} : Set V3))
    (d0 : dist v0 v3 = dist v0 v3') (d1 : dist v1 v3 = dist v1 v3')
    (cp : Coplanar ({v0, v1, v2, v3} : Set V3))
    (cp' : Coplanar ({v0, v1, v2, v3'} : Set V3))
    (hcr : ∃ t : ℝ, 0 < t ∧ t • cross3 (v3 - v0) (v1 - v0) =
      cross3 (v3' - v0) (v1 - v0)) : v3 = v3' := by
  -- DISCHARGES: HOL `mk_planar_unique` (basis `v1, v1 cross v2, n`
  -- expansion over Trigonometry2.NONCOPLANAR_3_BASIS and
  -- Zlzthic.coplanar_in_affine_hull); affine-hull engine absent here.
  -- NEEDS: port of the planar basis-expansion argument.
  sorry

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
  -- DISCHARGES: continuity of `cross_product` on `real^3`
  -- (Xbjrphc.CONTINUOUS_CROSS) and the sqrt composition
  -- (Pqcsxwg.REAL_CONTINUOUS_ATREAL_SQRT_COMPOSE); the cross-continuity
  -- lemma is not on this side. NEEDS: port of the cross kit.
  sorry

/-- HOL `collinear_expand` (CUXVZOZ.hl:1004): a vector coplanar with the
plane spanned off the origin expands over the two non-collinear vectors. -/
theorem collinear_expand_p21 (v1 v2 v3 : V3)
    (hnc : ¬ Collinear ℝ ({0, v1, v2} : Set V3))
    (hc : Coplanar ({0, v1, v2, v3} : Set V3)) :
    ∃ t1 t2 : ℝ, v3 = t1 • v1 + t2 • v2 := by
  -- DISCHARGES: HOL Counting_spheres.NOT_COLLINEAR_AFF_DIM_2 +
  -- Leaf_cell.COPLANAR_IMP_AFF_DIM + AFF_DIM_EQ_AFFINE_HULL +
  -- Marchal_cells_2_new.IN_AFFINE_KY_LEMMA1 (affDim bookkeeping).
  -- NEEDS: the affDim kit over `affDim` (Polytope) or Mathlib equivalents.
  sorry

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
  have he0 : 0 ≤ e := h0.2
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
  -- DISCHARGES: HOL Fan.sum3_azim_fan (the split identity on a fan) +
  -- Local_lemmas.AZIM_RANGE bookkeeping; the sum3 fan kit is not on this
  -- side. NEEDS: merge with the Fan azimuth-addition lane.
  sorry

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
  -- DISCHARGES: HOL uses Appendix.BBs_v39 (fan data off BBs), the
  -- hypermap-free `local_fan` fact CVX_LO_IMP_LO, LOCAL_FAN_IVS_IN_V,
  -- Polar_fan.RHO_NODE1_INJECTIVE, LOCAL_FAN_RHO_NODE_IVS and
  -- Qknvmlb.VV_SUC_EQ_RHO_NODE_PRIME; none of the polar-fan kit is ported
  -- on this side. NEEDS: merge with the polar-fan lane.
  sorry

/-- HOL `vv_azim_le_alt` (CUXVZOZ.hl:2056): the successor azimuth dominates
over the convex local fan. -/
theorem vv_azim_le_alt_p21 (vv : ℕ → V3) (k i j : ℕ) (hper : Periodic vv k)
    (hk3 : 3 ≤ k)
    (hcf : ConvexLocalFan (Set.range vv) (Set.range fun i => {vv i, vv (i + 1)})
      (Set.range fun i => (vv i, vv (i + 1))))
    (hinj : ∀ i j, i < k → j < k → vv i = vv j → i = j) :
    azim 0 (vv i) (vv (i + 1)) (vv j) ≤ azim 0 (vv i) (vv (i + 1)) (vv (i + k - 1)) := by
  -- DISCHARGES: HOL Terminal.PRIOR_TO_LESS_THAN_PI_LEMMA_ALT +
  -- Terminal.vv_rho_node1 + Terminal.EE_vv +
  -- Local_lemmas.AZIM_CYCLE_TWO_POINT_SET; the hypermap azimuth-cycle kit
  -- is not on this side. NEEDS: merge with the Terminal lane.
  sorry

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
  -- DISCHARGES: HOL Fan.sum4_azim_fan applied over vv_azim_le_alt; the
  -- sum4 azimuth-addition kit is not on this side.
  -- NEEDS: merge with the Terminal/Fan azimuth-addition lane.
  sorry

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
  -- DISCHARGES: HOL Lunar_deform.XRECQNS_UPDATE (the deformed dart set is
  -- again a local fan) + Zlzthic.deformation_rho_node1_equivariant1 /
  -- deformation_ivs_rho_node1_equivariant1 + BBs_inj + Terminal.vv_rho_node1
  -- + VV_SUC_EQ_IVS_RHO_NODE_PRIME. The equivariance kit is not ported on
  -- this side. NEEDS: merge with the deformation-equivariance lane.
  sorry

/-- HOL `deformation_BBs` (CUXVZOZ.hl:1883; the `//`-commented azim skolem
assumption of the source is dropped): a deformation that is rigid on the
sphere, keeps flat `interior_angle1`s under π and preserves the tight a/b
edges stays in `BBs_v39` for small `t`. -/
theorem deformation_BBs_p21 (s : ScsV39) (k : ℕ) (f : V3 → ℝ → V3) (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = k) (hBB : BBsV39 s v) (hg : scsGeneric v)
    (he : 0 < e) (hd : Deformation f (Set.range v) (-e) e)
    (hflat : ∀ i t, t ∈ Ioo (-e) e →
      interiorAngle1 0 (Set.range fun j => (v j, v (j + 1))) (v i) = Real.pi →
        interiorAngle1 0
            (Set.image (fun p : V3 × V3 => (f p.1 t, f p.2 t))
              (Set.range fun j => (v j, v (j + 1)))) (f (v i) t) ≤ Real.pi)
    (hn : ∀ i t, |t| < e → ‖f (v i) t‖ = ‖v i‖)
    (ha : ∀ i j, ∃ e1, 0 < e1 ∧ s.a i j = dist (v i) (v j) →
      ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))
    (hb : ∀ i j, ∃ e2, 0 < e2 ∧ dist (v i) (v j) = s.b i j →
      ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j) :
    ∃ e', 0 < e' ∧ ∀ t, |t| < e' → BBsV39 s (fun i => f (v i) t) := by
  -- DISCHARGES: HOL `deformation_BBs` (170 lines): the SKOLEM_PERIODIC2
  -- reduction, the convex_local_fan transport under deformation, and the
  -- generic-position azimuth machinery; the fan-transport lemmas
  -- (deformation convex_local_fan) are not ported on this side.
  -- NEEDS: merge with the deformation-transport lane.
  sorry

/-- HOL `deformation_BBs_ALT` (CUXVZOZ.hl:2249): the azim-skolem variant —
the flat-angle hypothesis is replaced by the azimuth `≤ π` skolem chain via
`interior_angle1_azim_scs` + `SKOLEM_PERIODIC`. -/
theorem deformation_BBs_ALT_p21 (s : ScsV39) (k : ℕ) (f : V3 → ℝ → V3) (v : ℕ → V3) (e : ℝ)
    (hs : isScsV39 s) (hk : s.k = k) (hk3 : 3 < k) (hBB : BBsV39 s v) (hg : scsGeneric v)
    (he : 0 < e) (hd : Deformation f (Set.range v) (-e) e)
    (haz : ∀ i, ∃ e0, 0 < e0 ∧
      azim 0 (v i) (v (i + 1)) (v (i + (k - 1))) = Real.pi →
      ∀ t, |t| < e0 →
        azim 0 (f (v i) t) (f (v (i + 1)) t) (f (v (i + (k - 1))) t) ≤ Real.pi)
    (hn : ∀ i t, |t| < e → ‖f (v i) t‖ = ‖v i‖)
    (ha : ∀ i j, ∃ e1, 0 < e1 ∧ s.a i j = dist (v i) (v j) →
      ∀ t, |t| < e1 → s.a i j ≤ dist (f (v i) t) (f (v j) t))
    (hb : ∀ i j, ∃ e2, 0 < e2 ∧ dist (v i) (v j) = s.b i j →
      ∀ t, |t| < e2 → dist (f (v i) t) (f (v j) t) ≤ s.b i j) :
    ∃ e', 0 < e' ∧ ∀ t, |t| < e' → BBsV39 s (fun i => f (v i) t) := by
  -- DISCHARGES: HOL `deformation_BBs_ALT` (90 lines): applies
  -- deformation_BBs over the SKOLEM_PERIODIC + interior_angle1_azim_scs
  -- uniformisation; depends on the same missing fan-transport kit.
  -- NEEDS: merge with the deformation-transport lane.
  sorry

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
      dihXf_p16 x1 x2 x3 x4 (x5 + t) x6 ≤ dihXf_p16 x1 x2 x3 x4 x5 x6 := by
  -- DISCHARGES: HOL Ocbicby.derived_form_dih_x_wrt_x5 (the ∂dih_x/∂x5
  -- derivative form `--sqrt x1 * delta_x6 / (ups_x x1 x3 * sqrt delta_x)`)
  -- + REAL_MVT_VERY_SIMPLE + epsilon_triple bookkeeping; the derivative
  -- kit is not ported on this side. NEEDS: merge with the Ocbicby lane.
  sorry

/-- HOL `delta_x5_delta_x6` (CUXVZOZ.hl:3173): `delta_x6` is `delta_x5`
under the `(x2,x3)`/`(x5,x6)` swap; a pure ring identity. -/
theorem delta_x5_delta_x6_p21 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX6_p21 x1 x3 x2 x4 x6 x5 = deltaX5_p21 x1 x2 x3 x4 x5 x6 := by
  unfold deltaX6_p21 deltaX5_p21
  ring

/-- HOL `dih_obtuse_mono` (CUXVZOZ.hl:3182): under a negative `delta_x5`
both `dih_x` at `x4+t` and at `x6+t` decrease. -/
theorem dih_obtuse_mono_p21 (x1 x2 x3 x4 x5 x6 : ℝ) (hx1 : 0 < x1)
    (hΔ : 0 < deltaX x1 x2 x3 x4 x5 x6) (hu1 : 0 < upsX x1 x2 x6)
    (hu2 : 0 < upsX x1 x3 x5) (hΔ5 : deltaX5_p21 x1 x2 x3 x4 x5 x6 < 0) :
    ∃ e, 0 < e ∧ ∀ t, |t| < e → t ≤ 0 →
      dihXf_p16 x1 x2 x3 (x4 + t) x5 x6 ≤ dihXf_p16 x1 x2 x3 x4 x5 x6 ∧
      dihXf_p16 x1 x2 x3 x4 x5 (x6 + t) ≤ dihXf_p16 x1 x2 x3 x4 x5 x6 := by
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
      dihXf_p16 x1 x2 x3 (x4 + t) x5 x6 ≤ dihXf_p16 x1 x2 x3 x4 x5 x6 := by
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
      taum_p16 ‖v0‖ ‖v1‖ ‖v2‖ (dist v1 v2) (dist v0 v2) (dist v0 v1) := by
  -- DISCHARGES: HOL Nonlinear_lemma.taum_123, Sphere.rhazim/rhazim2/rhazim3,
  -- node2_y/node3_y, sol0_const1 and Merge_ineq.DIHV_EQ_DIH_Y (dihV = dih_y
  -- off the coplanar locus); the dih_y bridge is not on this side.
  -- NEEDS: the body of `taum` (Terminal lane; LocalAuto16's `taum_p16` is a
  -- registry signature) plus the DIHV_EQ_DIH_Y bridge.
  sorry

/-- HOL `tau3_azim` (CUXVZOZ.hl:3629): the azimuth rendering of `tau3`. -/
theorem tau3_azim_p21 (v0 v1 v2 : V3)
    (hnc : ¬ Coplanar ({0, v0, v1, v2} : Set V3))
    (haz : azim 0 v0 v1 v2 ≤ Real.pi) :
    tau3 v0 v1 v2 = rho ‖v0‖ * azim 0 v0 v1 v2 +
        rho ‖v1‖ * azim 0 v1 v2 v0 + rho ‖v2‖ * azim 0 v2 v0 v1 -
        (Real.pi + sol0) := by
  -- DISCHARGES: HOL Polar_fan.AZIM_DIHV_SAME_STRONG (azim = dihV on the
  -- rhazim slots, strong form) + Xivphks.FSQKWKK (azim range on non-collinear
  -- triples); not ported on this side.
  -- NEEDS: merge with the Polar_fan lane.
  sorry

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
