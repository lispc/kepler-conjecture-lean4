/-
PackingAuto20: port of `scripts/packing/TSKAJXY1.hl` (Flyspeck chapter
"TSKAJXY", Vu Khac Ky 2012, 5668 lines).

FILE MAP (TSKAJXY hub role)
  TSKAJXY1 is the HUB of the TSKAJXY special-case chain 1 -> 2 -> 3: it
  carries (a) the analytic toolkit that reduces `mcell` invariants
  (`dihX`, `sol`, `volume.real`, `gammaX`) to the 6-argument nonlinear
  functions `dih_y/sol_y/vol_y/gamma4fgcy/gamma3f` on the edge-length
  six-tuple `y1..y6`, and (b) the raw numeric bound `HJKDESR1a_1cell`
  feeding the TSKAJXY inequality.  The later chain links (TSKAJXY2/3)
  consume exactly these six theorems; the small bank below
  (SET_RULE-style set algebra + `KY_COPLANAR_3`,
  `NEGLIGIBLE_MEASURE_UNION_klema`) is re-exported-style support shared
  by the whole chain, mirroring the file's restored SET_TAC preamble
  ("Changed by Vu Khac Ky - 15 Nov 2012").

  Source layout: no `new_definition` at all (0 defs in .hl).  Two tactic
  shims (`SET_TAC` restored, `SET_RULE tm = prove(tm,SET_TAC[])`), three
  small lemmas, six giant `prove_by_refinement` theorems whose bodies
  inline ~206 SET_RULE facts (97 distinct instances, ~25 generic
  patterns) -- those instances are lifted here into a generic private
  support-lemma bank (all `p20_*`, proved; they are the mechanical
  set-algebra core the giants rewrite through).

ENCODING NOTES
  - HOL `dih_y/sol_y/vol_y/gamma4fgcy/gamma3f` (sphere.hl:159-582): the
    `delta_x4/dih_x/dih_y/sol_y` half of this payload now resolves to
    Kepler.Text.SphereKit (atn2-merge, plan §5.2); the vol/gamma family (`vol_x/vol_y/vol4f/
    gamma4fgcy/vol3r/vol3f/gamma3f`) stays here (its only duplicate was
    PackingAuto21's verbatim copy, deleted in wave 2).  The hub's
    `deltaXf`/`deltaX4f` names survive as compatibility aliases of
    SphereKit `deltaX`/`deltaX4` until the wave-3 renames.
  - HOL `real^3` <-> `V3` (Kepler.Geom); `dist (u,v)` <-> `dist u v`;
    `NULLSET X` <-> `nullSet X` (`volume X = 0`); `vol X` (real volume)
    <-> `volume.real X`, matching the convention inside `gammaX`;
    `coplanar` <-> `Coplanar ℝ`; `convex hull` <-> `convexHull ℝ`;
    `aff_ge` <-> `affGe` (Kepler.Geom.Aff); `sqrt2` <-> `Real.sqrt 2`.
  - HOL hypothesis lists `a = dihV ... /\ ...` become explicit
    hypotheses; free HOL variables are universally closed.
  - DISCHARGES: none.  No `pack_concl` interface matches these
    conclusions: they are upstream support FOR the chain -- the chain's
    concl `TSKAJXY_statement` (PackingAuto2.lean:845,
    `criticalEdgeX`-based) is discharged by TSKAJXY2/3, not here.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto11
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto13
import Kepler.Text.PackingAuto15
import Kepler.Text.PackingAuto17
import Kepler.Text.LocalAuto38Bridge
import Kepler.Text.SphereKit
import Kepler.Text.Polytope
import Kepler.Text.PlanarityAuto12
import Kepler.Geom.SimplexVolume
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## Definitional payload: the sphere.hl nonlinear toolkit

Single-sourced in `Kepler.Text.SphereKit` (atn2-merge, docs/atn2-merge-plan.md
§5.2); that module declares the kit in this same `Kepler.Text` namespace, so
deleting the hub's local defs keeps every plain name resolving for the whole
TSKAJXY chain (and the LocalAuto2 lane).  The hub's historical
`deltaXf`/`deltaX4f` names survive as compatibility alias defs (bodies kept
VERBATIM, definitionally equal to SphereKit `deltaX`/`deltaX4`: the
LocalAuto2-lane proofs close goals by `simp only [deltaXf, …]` + `ring`,
which needs the alias to unfold all the way to the arithmetic body).  Wave 3
renames their users (plan §4) and removes them. -/

/-- Compatibility alias for the hub's historical `delta_x` name (verbatim
body = SphereKit `deltaX` = the old PackingAuto20.lean:73 def); removed in
wave 3 together with the `deltaXf → deltaX` user renames. -/
def deltaXf (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6) +
    x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6) +
    x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6) -
    x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

/-- Compatibility alias for the historical `delta_x4` name (verbatim body =
SphereKit `deltaX4` = the old PackingAuto20.lean:80 def); removed in wave 3
together with `deltaXf`. -/
noncomputable def deltaX4f (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6 +
    x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

/-- HOL `vol_x` (sphere.hl:251): simplex volume from squared lengths. -/
noncomputable def volXf (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt (deltaX x1 x2 x3 x4 x5 x6) / 12

/-- HOL `vol_y` (sphere.hl:547, `y_of_x vol_x`). -/
noncomputable def volY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  volXf (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6)

/-- HOL `vol4f` (sphere.hl:568): fake 4-cell volume. -/
noncomputable def vol4f (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (solY y1 y2 y3 y4 y5 y6 + solY y1 y5 y6 y4 y2 y3 +
      solY y4 y5 y3 y1 y2 y6 + solY y4 y2 y6 y1 y5 y3) -
    (8 * mm2 / Real.pi) *
    (f (y1 / 2) * dihY y1 y2 y3 y4 y5 y6 +
      f (y2 / 2) * dihY y2 y3 y1 y5 y6 y4 +
      f (y3 / 2) * dihY y3 y1 y2 y6 y4 y5 +
      f (y4 / 2) * dihY y4 y3 y5 y1 y6 y2 +
      f (y5 / 2) * dihY y5 y1 y6 y2 y4 y3 +
      f (y6 / 2) * dihY y6 y1 y5 y3 y4 y2)

/-- HOL `gamma4f` (sphere.hl:574) and `gamma4fgcy` (sphere.hl:566, its
definitionally equal alias kept as a separate name for the TSKAJXY
statement surface). -/
noncomputable def gamma4fgcy (y1 y2 y3 y4 y5 y6 : ℝ) (f : ℝ → ℝ) : ℝ :=
  volY y1 y2 y3 y4 y5 y6 - vol4f y1 y2 y3 y4 y5 y6 f

/-- HOL `vol3r` (sphere.hl:578): real 3-cell volume. -/
noncomputable def vol3r (y1 y2 y3 r : ℝ) : ℝ := volY r r r y1 y2 y3

/-- HOL `vol3f` (sphere.hl:580): fake 3-cell volume. -/
noncomputable def vol3f (y1 y2 y3 r : ℝ) (f : ℝ → ℝ) : ℝ :=
  (2 * mm1 / Real.pi) *
    (solY y1 y2 r r r y3 + solY y2 y3 r r r y1 + solY y3 y1 r r r y2) -
    (8 * mm2 / Real.pi) *
    (f (y1 / 2) * dihY y1 y2 r r r y3 +
      f (y2 / 2) * dihY y2 y3 r r r y1 +
      f (y3 / 2) * dihY y3 y1 r r r y2)

/-- HOL `gamma3f` (sphere.hl:582). -/
noncomputable def gamma3f (y1 y2 y3 r : ℝ) (f : ℝ → ℝ) : ℝ :=
  vol3r y1 y2 y3 r - vol3f y1 y2 y3 r f

/-! ## Small caps of the hub -/

/-- HOL `KY_COPLANAR_3` (TSKAJXY1.hl:88): any three points are coplanar. -/
theorem KY_COPLANAR_3 (a b c : V3) : Coplanar ({a, b, c} : Set V3) :=
  Kepler.Geom.coplanar_triple a b c

/-- HOL `NEGLIGIBLE_MEASURE_UNION_klema` (TSKAJXY1.hl:96). -/
theorem NEGLIGIBLE_MEASURE_UNION_klema {s t : Set V3} (_hs : MeasurableSet s)
    (_ht : MeasurableSet t) (hnt : nullSet t) :
    volume.real (s ∪ t) = volume.real s := by
  have h1 : volume (s ∪ t) ≤ volume s := by
    refine le_trans (measure_union_le s t) ?_
    rw [show volume t = 0 from hnt, add_zero]
  have h2 : volume s ≤ volume (s ∪ t) :=
    measure_mono (Set.subset_union_left (s := s) (t := t))
  exact congrArg ENNReal.toReal (le_antisymm h1 h2)

/-! ## The six ALL-CAPS theorems

`SOL_SOLID_TRIANGLE`, `DIHX_DIH_Y_lemma`, `SOL_SOL_Y_EXPLICIT` and
`HJKDESR1a_1cell` are FULLY PROVED below (2026-10-08, the kit-下移波:
the `cell_params_d` uniqueness kit moved up from the file tail unlocked
the four mcell-reduction giants). `gammaX_gamm4fgcy` is PROVED too
(2026-10-08, SimplexVolume 消费波: the tetra-volume bridge via
`volume_real_convexHull_tetra` + the edgeX six-pair epsilon kit closed
both halves); `gammaX_gamma3f` remains `sorry` (the k = 3 apex-form
dispatch) — see their docstrings. -/

/- HOL `AFF_GE_1_3` (TSKAJXY1.hl:75, proof `AFF_TAC`): explicit cone
formula for `aff_ge` of a point-triple disjoint from the apex.
DISCHARGES: identical interface already ported AND proved as
`PlanarityAuto11.AFF_GE_1_3` (PlanarityAuto11.lean:1136, same
statement modulo variable renaming); the hub's re-derivation is not
re-declared here. -/
/-- HOL `SOL_SOLID_TRIANGLE` (TSKAJXY1.hl:111): the solid angle of a
vertex of a (non-coplanar) tetrahedron is the spherical excess.

FULLY PROVED (2026-10-08): the hull sector inside the half-face-distance
ball is radial and has the same volume as the open-face cone `affGt {v0}
{v1,v2,v3}` (cone points near the apex lie in the hull by the face-distance
minimality; hull points near the apex are cone points or sit in one of the
three edge planes, all null); `volume_solid_triangle` (Geom.SolidAngle) +
`sol_spec` (Geom.Volume) then identify `sol` with the spherical excess. -/
private theorem sst_mem_hull3 (v1 v2 v3 : V3) {c1 c2 c3 : ℝ}
    (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (hs : c1 + c2 + c3 = 1) :
    c1 • v1 + c2 • v2 + c3 • v3 ∈ convexHull ℝ ({v1, v2, v3} : Set V3) := by
  have h4 : ({v1, v2, v3, v3} : Set V3) = {v1, v2, v3} := by
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hCH := CONVEX_HULL_4 v1 v2 v3 v3
  rw [h4] at hCH
  rw [hCH]
  exact ⟨c1, c2, c3, 0, h1, h2, h3, by linarith, by linarith, by module⟩

/-- Cone weights vs distance to the face minimizer. -/
private theorem sst_sigma_norm (v0 v1 v2 v3 y0 : V3)
    (hmin : ∀ z ∈ convexHull ℝ ({v1, v2, v3} : Set V3), dist v0 y0 ≤ dist v0 z)
    {t2 t3 t4 : ℝ} (h2 : 0 ≤ t2) (h3 : 0 ≤ t3) (h4 : 0 ≤ t4)
    {z : V3} (hsub : z - v0 = t2 • (v1 - v0) + t3 • (v2 - v0) + t4 • (v3 - v0)) :
    (t2 + t3 + t4) * dist v0 y0 ≤ dist z v0 := by
  by_cases hσ : t2 + t3 + t4 ≤ 0
  · have hσz : t2 + t3 + t4 = 0 := le_antisymm hσ (by linarith)
    rw [hσz, zero_mul]
    exact dist_nonneg
  · have hσp : 0 < t2 + t3 + t4 := not_le.mp hσ
    set y' := (t2 / (t2 + t3 + t4)) • v1 + (t3 / (t2 + t3 + t4)) • v2 +
      (t4 / (t2 + t3 + t4)) • v3 with hy'def
    have hy'F : y' ∈ convexHull ℝ ({v1, v2, v3} : Set V3) := by
      refine sst_mem_hull3 v1 v2 v3 ?_ ?_ ?_ ?_
      · exact div_nonneg h2 (le_of_lt hσp)
      · exact div_nonneg h3 (le_of_lt hσp)
      · exact div_nonneg h4 (le_of_lt hσp)
      · field_simp
    have hσy' : (t2 + t3 + t4) • y' = t2 • v1 + t3 • v2 + t4 • v3 := by
      rw [hy'def, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
      field_simp
    have hexp : (t2 + t3 + t4) • (y' - v0)
        = t2 • (v1 - v0) + t3 • (v2 - v0) + t4 • (v3 - v0) := by
      rw [smul_sub, hσy']
      module
    have hr1 : dist z v0 = ‖z - v0‖ := dist_eq_norm z v0
    have hr2 : ‖z - v0‖ = ‖(t2 + t3 + t4) • (y' - v0)‖ := by rw [hsub, ← hexp]
    have hr3 : ‖(t2 + t3 + t4) • (y' - v0)‖
        = (t2 + t3 + t4) * ‖y' - v0‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσp]
    have hr4 : (t2 + t3 + t4) * ‖y' - v0‖ = (t2 + t3 + t4) * dist y' v0 := by
      rw [dist_eq_norm]
    have hdle : dist v0 y0 ≤ dist y' v0 := by
      rw [dist_comm y' v0]
      exact hmin y' hy'F
    calc (t2 + t3 + t4) * dist v0 y0
        ≤ (t2 + t3 + t4) * dist y' v0 :=
          mul_le_mul_of_nonneg_left hdle (le_of_lt hσp)
      _ = dist z v0 := by rw [hr1, hr2, hr3, hr4]

open Module in
private theorem sst_span_pair_ne_top (p q : V3) :
    Submodule.span ℝ ({p, q} : Set V3) ≠ ⊤ := by
  intro h
  have hle : finrank ℝ (Submodule.span ℝ ({p, q} : Set V3)) ≤ 2 := by
    have hh := finrank_span_finset_le_card (R := ℝ) ({p, q} : Finset V3)
    unfold Set.finrank at hh
    rw [show (({p, q} : Finset V3) : Set V3) = ({p, q} : Set V3) from by simp] at hh
    have h2 : ({p, q} : Finset V3).card ≤ 2 := by
      calc ({p, q} : Finset V3).card ≤ ({q} : Finset V3).card + 1 :=
          Finset.card_insert_le p {q}
        _ = 2 := by simp
    omega
  rw [h, finrank_top] at hle
  have h3 : finrank ℝ V3 = 3 := by
    simp [V3, finrank_euclideanSpace_fin]
  omega

private theorem sst_plane_null (v0 p q : V3) :
    volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({p, q} : Set V3))) = 0 := by
  have hpre : (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({p, q} : Set V3))
      = (fun z : V3 => -v0 + z) ⁻¹' (Submodule.span ℝ ({p, q} : Set V3)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro h
      exact ⟨-v0 + z, by simpa using h, by abel⟩
  rw [hpre, measure_preimage_add]
  exact MeasureTheory.Measure.addHaar_submodule volume _ (sst_span_pair_ne_top p q)

theorem SOL_SOLID_TRIANGLE {a b c : ℝ} (v0 v1 v2 v3 : V3)
    (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3))
    (ha : a = dihV v0 v1 v2 v3) (hb : b = dihV v0 v2 v3 v1)
    (hc : c = dihV v0 v3 v1 v2) :
    sol v0 (convexHull ℝ ({v0, v1, v2, v3} : Set V3)) = a + b + c - Real.pi := by
  subst ha
  subst hb
  subst hc
  -- apex distinct from face vertices
  have hv01 : v0 ≠ v1 := by
    intro h
    apply hnc
    have he : ({v0, v1, v2, v3} : Set V3) = {v1, v2, v3} := by
      rw [h]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [he]
    exact coplanar_triple v1 v2 v3
  have hv02 : v0 ≠ v2 := by
    intro h
    apply hnc
    have he : ({v0, v1, v2, v3} : Set V3) = {v1, v2, v3} := by
      rw [h]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [he]
    exact coplanar_triple v1 v2 v3
  have hv03 : v0 ≠ v3 := by
    intro h
    apply hnc
    have he : ({v0, v1, v2, v3} : Set V3) = {v1, v2, v3} := by
      rw [h]
      ext p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [he]
    exact coplanar_triple v1 v2 v3
  have hdis : Disjoint ({v0} : Set V3) {v1, v2, v3} := by
    rw [Set.disjoint_singleton_left]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hv01, hv02, hv03⟩
  -- face hull and its distance minimizer
  have hFne : (convexHull ℝ ({v1, v2, v3} : Set V3)).Nonempty :=
    ⟨v1, subset_convexHull ℝ _ (by simp)⟩
  have hFcp : IsCompact (convexHull ℝ ({v1, v2, v3} : Set V3)) :=
    Set.Finite.isCompact_convexHull ℝ (Set.toFinite ({v1, v2, v3} : Set V3))
  obtain ⟨y0, hy0, hdmin⟩ := hFcp.exists_isMinOn hFne
    (Continuous.continuousOn (Continuous.dist continuous_const continuous_id))
  simp only [IsMinOn, IsMinFilter, Filter.eventually_principal] at hdmin
  -- v0 outside the face affine hull
  have hv0span : v0 ∉ (affineSpan ℝ ({v1, v2, v3} : Set V3) : Set V3) := by
    intro h
    apply hnc
    refine ⟨v1, v2, v3, ?_⟩
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact h
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
  have hFsub : convexHull ℝ ({v1, v2, v3} : Set V3) ⊆
      (affineSpan ℝ ({v1, v2, v3} : Set V3) : Set V3) :=
    convexHull_subset_affineSpan _
  have hvy0 : v0 ∉ convexHull ℝ ({v1, v2, v3} : Set V3) := fun hmem =>
    hv0span (hFsub hmem)
  have hd : 0 < dist v0 y0 := dist_pos.2 fun h => hvy0 (by
    rw [h]
    exact hy0)
  set r : ℝ := dist v0 y0 / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  -- the tetrahedron hull is closed/measurable
  have hKclosed : IsClosed (convexHull ℝ ({v0, v1, v2, v3} : Set V3)) :=
    CLOSED_CONVEX_HULL_FINITE _ (Set.toFinite ({v0, v1, v2, v3} : Set V3))
  have hKmeas : MeasurableSet (convexHull ℝ ({v0, v1, v2, v3} : Set V3) ∩
      Metric.ball v0 r) :=
    hKclosed.measurableSet.inter Metric.isOpen_ball.measurableSet
  -- affine characterizations
  have hAFF := AFF_GT_1_3 v0 v1 v2 v3 hdis
  have hCH4 := CONVEX_HULL_4 v0 v1 v2 v3
  -- radiality of the hull inside the half-distance ball
  have hrad : radialNorm r v0 (convexHull ℝ ({v0, v1, v2, v3} : Set V3) ∩
      Metric.ball v0 r) := by
    refine ⟨Set.inter_subset_right, ?_⟩
    intro u hu t ht hlt
    have hball' : v0 + t • u ∈ Metric.ball v0 r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht]
      linarith
    have hKmem : v0 + t • u ∈ convexHull ℝ ({v0, v1, v2, v3} : Set V3) := by
      obtain ⟨huK, -⟩ := hu
      rw [hCH4] at huK
      obtain ⟨t1, t2, t3, t4, h1, h2, h3, h4, hsum, hz⟩ := huK
      rw [hCH4]
      have ht1 : t1 = 1 - (t2 + t3 + t4) := by linarith
      have hu' : u = t2 • (v1 - v0) + t3 • (v2 - v0) + t4 • (v3 - v0) := by
        have huEq : u = (v0 : V3) + u - v0 := by rw [add_sub_cancel_left]
        rw [huEq, hz, ht1]
        module
      have hsub' : (v0 : V3) + t • u - v0
          = (t * t2) • (v1 - v0) + (t * t3) • (v2 - v0) + (t * t4) • (v3 - v0) := by
        rw [add_sub_cancel_left, hu']
        module
      have hball'' : dist (v0 + t • u) v0 < dist v0 y0 / 2 := by
        rw [Metric.mem_ball] at hball'
        rwa [hrdef] at hball'
      have hσb := sst_sigma_norm v0 v1 v2 v3 y0 hdmin
        (mul_nonneg ht.le h2) (mul_nonneg ht.le h3) (mul_nonneg ht.le h4) hsub'
      have hd' : dist (v0 + t • u) v0 = t * ‖u‖ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht]
      rw [hd'] at hσb
      have hmid : (t * t2 + t * t3 + t * t4) * dist v0 y0
          < (1 / 2) * dist v0 y0 := by
        linarith [hσb, hlt, hrdef]
      have hlt2 : t * t2 + t * t3 + t * t4 < 1 / 2 := by
        by_contra hge
        push_neg at hge
        nlinarith [hσb, hlt, hrdef, hd, hge]
      refine ⟨1 - (t * t2 + t * t3 + t * t4), t * t2, t * t3, t * t4,
        by linarith [hlt2], mul_nonneg ht.le h2, mul_nonneg ht.le h3,
        mul_nonneg ht.le h4, by linarith [hlt2], ?_⟩
      rw [show (v0 : V3) + t • u
          = v0 + t • (t2 • (v1 - v0) + t3 • (v2 - v0) + t4 • (v3 - v0)) from by rw [hu']]
      module
    exact ⟨hKmem, hball'⟩
  -- the sol value
  have hsol := sol_spec hr hKmeas hrad
  -- cone points near the apex lie in the hull
  have hincA : (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ⊆
      convexHull ℝ ({v0, v1, v2, v3} : Set V3) ∩ Metric.ball v0 r := by
    intro z hz
    obtain ⟨hzG, hzB⟩ := hz
    have hbz : dist z v0 < r := Metric.mem_ball.1 hzB
    refine ⟨?_, hzB⟩
    rw [hAFF] at hzG
    obtain ⟨t1, t2, t3, t4, h2, h3, h4, hsum, hz'⟩ := hzG
    rw [hz']
    have ht1 : t1 = 1 - (t2 + t3 + t4) := by linarith
    have hsub' : z - v0 = t2 • (v1 - v0) + t3 • (v2 - v0) + t4 • (v3 - v0) := by
      rw [hz', ht1]
      module
    have hσb := sst_sigma_norm v0 v1 v2 v3 y0 hdmin h2.le h3.le h4.le hsub'
    have hmid : (t2 + t3 + t4) * dist v0 y0 < (1 / 2) * dist v0 y0 := by
      linarith [hσb, hbz, hrdef]
    have hσlt : t2 + t3 + t4 < 1 / 2 := by
      by_contra hge
      push_neg at hge
      nlinarith [hσb, hbz, hrdef, hd, hge]
    rw [hCH4]
    refine ⟨1 - (t2 + t3 + t4), t2, t3, t4, by linarith, h2.le, h3.le, h4.le,
      by linarith, ?_⟩
    have ht1 : t1 = 1 - (t2 + t3 + t4) := by linarith
    rw [ht1]
  -- hull points near the apex are cone points or sit in an edge plane
  have hincB : convexHull ℝ ({v0, v1, v2, v3} : Set V3) ∩ Metric.ball v0 r ⊆
      (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
        (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
        (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)) ∪
        (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)) := by
    rintro z ⟨hzK, hzball⟩
    rw [hCH4] at hzK
    obtain ⟨t1, t2, t3, t4, h1, h2, h3, h4, hsum, hz⟩ := hzK
    have ht1 : t1 = 1 - (t2 + t3 + t4) := by linarith
    have hsub : z - v0 = t2 • (v1 - v0) + t3 • (v2 - v0) + t4 • (v3 - v0) := by
      rw [hz, ht1]
      module
    by_cases h2p : 0 < t2
    · by_cases h3p : 0 < t3
      · by_cases h4p : 0 < t4
        · have hzX : z ∈ affGt ({v0} : Set V3) {v1, v2, v3} := by
            rw [hAFF]
            exact ⟨t1, t2, t3, t4, h2p, h3p, h4p, hsum, hz⟩
          have hzU : z ∈ (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
              (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
              (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)) ∪
              (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)) :=
            Set.mem_union_left (b := (fun z : V3 => v0 + z) ''
                (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)))
              (Set.mem_union_left (b := (fun z : V3 => v0 + z) ''
                  (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)))
                (Set.mem_union_left (b := (fun z : V3 => v0 + z) ''
                    (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)))
                  (Set.mem_inter hzX hzball)))
          exact hzU
        · have h4z : t4 = 0 := le_antisymm (not_lt.mp h4p) h4
          have hzW : z - v0 ∈ Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3) := by
            rw [hsub, h4z, zero_smul, add_zero]
            exact Submodule.add_mem _
              (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
              (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          have hzU : z ∈ (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
              (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
              (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)) ∪
              (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)) :=
            Set.mem_union_left (b := (fun z : V3 => v0 + z) ''
                (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)))
              (Set.mem_union_left (b := (fun z : V3 => v0 + z) ''
                  (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)))
                (Set.mem_union_right (a := (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r)
                  (b := (fun z : V3 => v0 + z) ''
                    (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)))
                  ⟨z - v0, hzW, by abel⟩))
          exact hzU
      · have h3z : t3 = 0 := le_antisymm (not_lt.mp h3p) h3
        have hzW : z - v0 ∈ Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3) := by
          rw [hsub, h3z, zero_smul, add_zero]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        have hzU : z ∈ (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
            (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
            (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)) ∪
            (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)) :=
          Set.mem_union_left (b := (fun z : V3 => v0 + z) ''
              (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)))
            (Set.mem_union_right (a := (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
                (fun z : V3 => v0 + z) ''
                  (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)))
              (b := (fun z : V3 => v0 + z) ''
                (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)))
              ⟨z - v0, hzW, by abel⟩)
        exact hzU
    · have h2z : t2 = 0 := le_antisymm (not_lt.mp h2p) h2
      have hzW : z - v0 ∈ Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3) := by
        rw [hsub, h2z, zero_smul, zero_add]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have hzU : z ∈ (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)) ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)) :=
        Set.mem_union_right (a := (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
            (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)))
          (b := (fun z : V3 => v0 + z) ''
            (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)))
          ⟨z - v0, hzW, by abel⟩
      exact hzU
  -- a genuine interior point of the cone sector (positive volume)
  have hXge : 0 ≤ ‖v1 + v2 + v3 - 3 • v0‖ := norm_nonneg _
  set c : ℝ := min (r / (4 + ‖v1 + v2 + v3 - 3 • v0‖)) (1 / 4) with hcdef
  have h4p : 0 < 4 + ‖v1 + v2 + v3 - 3 • v0‖ := by linarith
  have hcpos : 0 < c := by
    rw [hcdef]
    apply lt_min
    · exact div_pos hr h4p
    · norm_num
  have hcr : c ≤ r / (4 + ‖v1 + v2 + v3 - 3 • v0‖) := min_le_left _ _
  have hc3 : 3 * c < 1 := by
    have hq : c ≤ 1 / 4 := min_le_right _ _
    linarith
  have hcw : c * ‖v1 + v2 + v3 - 3 • v0‖ < r := by
    have hstep : c * ‖v1 + v2 + v3 - 3 • v0‖
        ≤ (r / (4 + ‖v1 + v2 + v3 - 3 • v0‖)) * ‖v1 + v2 + v3 - 3 • v0‖ := by
      nlinarith [hcr, hXge]
    rw [div_mul_eq_mul_div] at hstep
    have hlt' : r * ‖v1 + v2 + v3 - 3 • v0‖
        / (4 + ‖v1 + v2 + v3 - 3 • v0‖) < r := by
      rw [div_lt_iff₀ h4p]
      linarith [hr]
    linarith
  have hpt : (1 - 3 * c) • v0 + c • v1 + c • v2 + c • v3
      ∈ (affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r := by
    refine ⟨?_, ?_⟩
    · rw [hAFF]
      exact ⟨1 - 3 * c, c, c, c, by linarith, hcpos, hcpos, by ring, rfl⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsubp : (1 - 3 * c) • v0 + c • v1 + c • v2 + c • v3 - v0
          = c • (v1 + v2 + v3 - 3 • v0) := by module
      rw [hsubp, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
      exact hcw
  have hpos : 0 < volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r) := by
    have hne2 : (Metric.ball v0 r ∩ (affGt ({v0} : Set V3) {v1, v2, v3})).Nonempty :=
      ⟨_, hpt.2, hpt.1⟩
    have hp := (Metric.isOpen_ball.inter
      (OPEN_AFF_GT_1_3 v0 v1 v2 v3 hnc)).measure_pos volume hne2
    rwa [Set.inter_comm] at hp
  -- volume transfer through the null planes
  have hB0 : volume ((fun z : V3 => v0 + z) ''
      (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3))) = 0 :=
    sst_plane_null v0 (v1 - v0) (v2 - v0)
  have hC0 : volume ((fun z : V3 => v0 + z) ''
      (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3))) = 0 :=
    sst_plane_null v0 (v1 - v0) (v3 - v0)
  have hD0 : volume ((fun z : V3 => v0 + z) ''
      (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3))) = 0 :=
    sst_plane_null v0 (v2 - v0) (v3 - v0)
  have hle1 : volume (convexHull ℝ ({v0, v1, v2, v3} : Set V3) ∩ Metric.ball v0 r)
      ≤ volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r) := by
    have h2 := measure_mono (μ := volume) hincB
    have s1 : volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
        (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
      (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)) ∪
      (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3))) ≤
        volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
        (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3))) +
        volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3))) :=
      measure_union_le ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
        (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)))
        ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3)))
    have s2 : volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
        (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3))) ≤
        volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r) +
        volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3))) :=
      measure_union_le (affGt ({v0} : Set V3) {v1, v2, v3} ∩ Metric.ball v0 r)
        ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)))
    have s3 : volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
        (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
      (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3))) ≤
        volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3))) +
        volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3))) :=
      measure_union_le ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
        (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)))
        ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)))
    calc volume (convexHull ℝ ({v0, v1, v2, v3} : Set V3) ∩ Metric.ball v0 r)
        ≤ volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
            (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)) ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3))) := h2
      _ ≤ volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
            (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)) ∪
          (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3))) +
        volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3))) := s1
      _ ≤ (volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r ∪
            (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3))) +
          volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)))) +
        volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3))) :=
          add_le_add_left s3 (volume ((fun z : V3 => v0 + z) ''
            (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3))))
      _ ≤ ((volume (affGt ({v0} : Set V3) {v1, v2, v3} ∩ Metric.ball v0 r) +
            volume ((fun z : V3 => v0 + z) ''
              (Submodule.span ℝ ({v1 - v0, v2 - v0} : Set V3)))) +
          volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3)))) +
        volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({v2 - v0, v3 - v0} : Set V3))) :=
          add_le_add (add_le_add_left s2 (volume ((fun z : V3 => v0 + z) ''
            (Submodule.span ℝ ({v1 - v0, v3 - v0} : Set V3))))) le_rfl
      _ ≤ volume (affGt ({v0} : Set V3) {v1, v2, v3} ∩ Metric.ball v0 r) := by
          rw [hB0, hC0, hD0]
          simp
  have hvolEq : volume (convexHull ℝ ({v0, v1, v2, v3} : Set V3) ∩ Metric.ball v0 r)
      = volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r) :=
    le_antisymm hle1 (measure_mono (μ := volume) hincA)
  -- real-valued volumes
  have hfin1 : volume (convexHull ℝ ({v0, v1, v2, v3} : Set V3) ∩ Metric.ball v0 r)
      < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (measure_ball_lt_top (x := v0) (r := r))
  have hfin2 : volume ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r)
      < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (measure_ball_lt_top (x := v0) (r := r))
  have hreal : volume.real (convexHull ℝ ({v0, v1, v2, v3} : Set V3) ∩ Metric.ball v0 r)
      = volume.real ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r) := by
    rw [Measure.real_def, Measure.real_def]
    have h1 := (ENNReal.toReal_le_toReal hfin1.ne hfin2.ne).2
      (le_of_eq hvolEq)
    have h2 := (ENNReal.toReal_le_toReal hfin2.ne hfin1.ne).2
      (le_of_eq hvolEq.symm)
    exact le_antisymm h1 h2
  -- the dihedral sum exceeds π
  have hXsc : 0 ≤ (dihV v0 v1 v2 v3 + dihV v0 v2 v3 v1 + dihV v0 v3 v1 v2
      - Real.pi) * r ^ 3 / 3 := by
    by_contra hcon
    push_neg at hcon
    have hst := volume_solid_triangle (v0 := v0) (v1 := v1) (v2 := v2) (v3 := v3)
      (r := r) hr hnc
    rw [Set.inter_comm] at hst
    rw [hst] at hpos
    rw [ENNReal.ofReal_eq_zero.mpr hcon.le] at hpos
    exact absurd hpos (by norm_num)
  have hreal2 : volume.real ((affGt ({v0} : Set V3) {v1, v2, v3}) ∩ Metric.ball v0 r)
      = (dihV v0 v1 v2 v3 + dihV v0 v2 v3 v1 + dihV v0 v3 v1 v2 - Real.pi)
          * r ^ 3 / 3 := by
    have hst := volume_solid_triangle (v0 := v0) (v1 := v1) (v2 := v2) (v3 := v3)
      (r := r) hr hnc
    rw [Set.inter_comm] at hst
    rw [Measure.real_def, hst, ENNReal.toReal_ofReal hXsc]
  rw [hsol, hreal, hreal2]
  field_simp

/-! ## cell_params_d uniqueness kit and the k = 4 dispatch kit (moved up
from the file tail; the four TSKAJXY1 giants below are proved through it) -/

private theorem p20k_ne_empty {X : Set V3} (hn : ¬ nullSet X) : X ≠ ∅ := by
  intro h
  apply hn
  rw [h]
  exact measure_empty

private theorem p20k_mcell_ge4 {i : ℕ} {V : Set V3} {ul : List V3} (hi : 4 ≤ i) :
    mcell i V ul = mcell 4 V ul := by
  show (if i = 0 then mcell0 V ul else if i = 1 then mcell1 V ul
    else if i = 2 then mcell2 V ul else if i = 3 then mcell3 V ul
    else mcell4 V ul) = mcell4 V ul
  split_ifs with h1 h2 h3 h4
  · exact absurd h1 (by omega)
  · exact absurd h2 (by omega)
  · exact absurd h3 (by omega)
  · exact absurd h4 (by omega)
  · rfl

private theorem p20k_mcell4_hlt {V : Set V3} {ul : List V3} (hne : mcell 4 V ul ≠ ∅) :
    hl ul < Real.sqrt 2 := by
  have hexp : mcell 4 V ul =
      if hl ul < Real.sqrt 2 then convexHull ℝ (setOfList ul) else (∅ : Set V3) := rfl
  rw [hexp] at hne
  split_ifs at hne with h
  · exact h
  · exact absurd rfl hne

private theorem p20k_mcell4_hull {V : Set V3} {ul : List V3} (hne : mcell 4 V ul ≠ ∅) :
    mcell 4 V ul = convexHull ℝ (setOfList ul) := by
  have hexp : mcell 4 V ul =
      if hl ul < Real.sqrt 2 then convexHull ℝ (setOfList ul) else (∅ : Set V3) := rfl
  rw [hexp] at hne ⊢
  split_ifs at hne ⊢ with h
  · rfl
  · exact absurd rfl hne

private theorem p20k_vn_contra {V : Set V3} {ul vm : List V3}
    (h1 : voronoiNondg V ul) (h2 : voronoiNondg V vm)
    (hset : setOfList ul = setOfList vm) (hlen : ul.length = vm.length + 1) : False := by
  have e1 := h1.2.2
  have e2 := h2.2.2
  simp only [voronoiList] at e1 e2
  rw [hset, hlen] at e1
  omega

private theorem p20k_barV_distinct {V : Set V3} {x0 x1 x2 x3 : V3}
    (hb : barV V 3 [x0, x1, x2, x3]) :
    x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x3 ∧ x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3 := by
  have hv1 : voronoiNondg V [x0, x1] := hb.2 [x0, x1] ⟨⟨[x2, x3], rfl⟩, by simp⟩
  have hv0 : voronoiNondg V [x0] := hb.2 [x0] ⟨⟨[x1, x2, x3], rfl⟩, by simp⟩
  have hv2 : voronoiNondg V [x0, x1, x2] := hb.2 [x0, x1, x2] ⟨⟨[x3], rfl⟩, by simp⟩
  have hv3 : voronoiNondg V [x0, x1, x2, x3] := hb.2 _ ⟨⟨[], rfl⟩, by simp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- x0 ≠ x1
    intro h
    refine p20k_vn_contra hv1 hv0 ?_ ?_
    · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
    · simp
  · -- x0 ≠ x2
    intro h
    refine p20k_vn_contra hv2 hv1 ?_ ?_
    · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
    · simp
  · -- x0 ≠ x3
    intro h
    refine p20k_vn_contra hv3 hv2 ?_ ?_
    · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
    · simp
  · -- x1 ≠ x2
    intro h
    refine p20k_vn_contra hv2 hv1 ?_ ?_
    · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
    · simp
  · -- x1 ≠ x3
    intro h
    refine p20k_vn_contra hv3 hv2 ?_ ?_
    · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
    · simp
  · -- x2 ≠ x3
    intro h
    refine p20k_vn_contra hv3 hv2 ?_ ?_
    · rw [← h]; ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq]; tauto
    · simp

/-- general k=4 vertex-set lemma: `VX` of a non-null `mcell 4` is exactly
the witness list's point set. -/
private theorem p20k_VX_m4 (V : Set V3) (wl : List V3)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 wl)
    (hnull : ¬ nullSet (mcell 4 V wl)) :
    VX V (mcell 4 V wl) = setOfList wl := by
  have hne : mcell 4 V wl ≠ ∅ := by
    intro h0
    exact hnull (by rw [h0]; exact measure_empty)
  have h1 : VX V (mcell 4 V wl) = V ∩ mcell 4 V wl :=
    HDTFNFZ (v := 0) hs hp hb rfl hnull
  rw [h1, LEPJBDJ V wl 4 hs hp hb (by omega) (by omega) hne]
  have hts : truncateSimplex (4 - 1) wl = wl := by
    have htsE : truncateSimplex (4 - 1) wl =
        Classical.epsilon (fun vl : List V3 => vl.length = 3 + 1 ∧ initialSublist vl wl) := rfl
    have hspec := Classical.epsilon_spec (p := fun vl : List V3 =>
      vl.length = 3 + 1 ∧ initialSublist vl wl)
      ⟨wl, hb.1, ⟨[], by simp⟩⟩
    obtain ⟨yl, hy⟩ := hspec.2
    have hyl : yl = [] := by
      have h := congrArg List.length hy
      rw [List.length_append, hspec.1, hb.1] at h
      simp at h
      omega
    rw [htsE]
    conv_rhs => rw [hy]
    rw [hyl, List.append_nil]
  rw [hts]

/-- permutation witness: `barV` and `mcell` invariance under a permutation
whose head values and tail-fixedness are given. -/
private theorem p20k_perm_wit (V : Set V3) (u0 u1 u2 u3 : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 [u0, u1, u2, u3])
    (hne : mcell 4 V [u0, u1, u2, u3] ≠ ∅)
    (a b c d : V3) (p : Equiv.Perm ℕ)
    (hp0 : p 0 = s0) (hp1 : p 1 = s1) (hp2 : p 2 = s2) (hp3 : p 3 = s3)
    (htv : s0 < 4 ∧ s1 < 4 ∧ s2 < 4 ∧ s3 < 4)
    (hfixp : ∀ j : ℕ, 4 ≤ j → p j = j)
    (hla : [a, b, c, d] = leftActionList p [u0, u1, u2, u3]) :
    barV V 3 [a, b, c, d] ∧ mcell 4 V [a, b, c, d] = mcell 4 V [u0, u1, u2, u3] := by
  have hperm : permutes p (Set.Icc 0 3) := by
    intro x
    rcases Nat.lt_or_ge x 4 with hx | hx
    · have hx0 : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
      rcases hx0 with hx0 | hx0 | hx0 | hx0
      · rw [hx0] at *
        refine ⟨?_, by simp⟩
        intro _
        show (0:ℕ) ≤ p 0 ∧ p 0 ≤ 3
        rw [hp0]
        exact ⟨by omega, by omega⟩
      · rw [hx0] at *
        refine ⟨?_, by simp⟩
        intro _
        show (0:ℕ) ≤ p 1 ∧ p 1 ≤ 3
        rw [hp1]
        exact ⟨by omega, by omega⟩
      · rw [hx0] at *
        refine ⟨?_, by simp⟩
        intro _
        show (0:ℕ) ≤ p 2 ∧ p 2 ≤ 3
        rw [hp2]
        exact ⟨by omega, by omega⟩
      · rw [hx0] at *
        refine ⟨?_, by simp⟩
        intro _
        show (0:ℕ) ≤ p 3 ∧ p 3 ≤ 3
        rw [hp3]
        exact ⟨by omega, by omega⟩
    · have hx' : ¬ (x ∈ Set.Icc 0 3) := by simp only [Set.mem_Icc]; omega
      have hx2 : ¬ (p x ∈ Set.Icc 0 3) := by rw [hfixp x hx]; exact hx'
      exact ⟨fun h => absurd h hx', fun h => absurd h hx2⟩
  refine ⟨QZKSYKG1 hs hp hb (by simp) hne hperm hfixp hla, ?_⟩
  rw [hla]
  exact RVFXZBU (by simp) hs hp hb hperm hfixp


/-- collinear triple forces the 4-point set coplanar. -/
private theorem p20k_col_coplanar {p q r w : V3} (hpq : p ≠ q)
    (hcol : Collinear ℝ ({p, q, r} : Set V3)) :
    Coplanar ({p, q, r, w} : Set V3) := by
  refine ⟨p, q, w, ?_⟩
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz | hz | hz
  · rw [hz]; exact subset_affineSpan ℝ ({p, q, w} : Set V3) (by simp)
  · rw [hz]; exact subset_affineSpan ℝ ({p, q, w} : Set V3) (by simp)
  · rw [hz]
    exact SetLike.mem_coe.mpr ((affineSpan_mono ℝ
      (show ({p, q} : Set V3) ⊆ ({p, q, w} : Set V3) by
        intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))
      (hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq))
  · rw [hz]; exact subset_affineSpan ℝ ({p, q, w} : Set V3) (by simp)

/-! ## cell_params_d uniqueness kit (verbatim from PackingAuto20 tail) -/

theorem MCELL_CELL_PARAMETERS_D_EXIST (V : Set V3) (ul vl : List V3) (k : ℕ) (X : Set V3)
    (hk : k ≤ 4) (hp : Packing V) (hs : saturated V) (hX : X = mcell k V ul)
    (hb : barV V 3 ul) (his : initialSublist vl ul) (hn : ¬nullSet X) :
    (cellParamsD V X vl).1 = k := by
  have hex : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧
      initialSublist vl p.2 := ⟨(k, ul), hk, hb, hX, his⟩
  have heps := Classical.epsilon_spec (p := fun p : ℕ × List V3 =>
    p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧ initialSublist vl p.2) hex
  have hb1 : barV V 3 (cellParamsD V X vl).2 := heps.2.1
  have hi1 : (cellParamsD V X vl).1 ≤ 4 := heps.1
  have hXw : X = mcell (cellParamsD V X vl).1 V (cellParamsD V X vl).2 := heps.2.2.1
  have hAj := AJRIPQN V (cellParamsD V X vl).2 ul (cellParamsD V X vl).1 k hs hp hb1 hb
    (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)
    (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)
    (by rw [← hXw, ← hX, Set.inter_self]; exact hn)
  exact hAj.1

theorem MCELL_PARAM_D_UL (V : Set V3) (ul ul' vl : List V3) (X : Set V3) (k : ℕ)
    (hk : k ≤ 4) (hp : Packing V) (hs : saturated V) (hX : X = mcell k V ul)
    (hb : barV V 3 ul) (hn : ¬nullSet X) (his : initialSublist ul' ul)
    (hvl : vl = (cellParamsD V X ul').2) :
    X = mcell k V vl ∧ barV V 3 vl ∧ initialSublist ul' vl := by
  have hex : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧
      initialSublist ul' p.2 := ⟨(k, ul), hk, hb, hX, his⟩
  have heps := Classical.epsilon_spec (p := fun p : ℕ × List V3 =>
    p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧ initialSublist ul' p.2) hex
  have hb1 : barV V 3 (cellParamsD V X ul').2 := heps.2.1
  have hi1 : (cellParamsD V X ul').1 ≤ 4 := heps.1
  have hXw : X = mcell (cellParamsD V X ul').1 V (cellParamsD V X ul').2 := heps.2.2.1
  have hvl' : vl = (cellParamsD V X ul').2 := hvl
  subst hvl'
  have hAj := AJRIPQN V ul (cellParamsD V X ul').2 k (cellParamsD V X ul').1 hs hp hb hb1
    (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)
    (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega)
    (by rw [← hXw, ← hX, Set.inter_self]; exact hn)
  rw [hvl, hAj.1, ← hAj.2, ← hX]
  refine ⟨rfl, hb1, heps.2.2.2⟩


/-- per-edge dispatch: `dihX` at edge `(a, b)` through the permuted witness
list `[a, b, c, d]` folds back to the plain tetrahedral dihedral. -/
private theorem p20k_dihX_m4 (V X : Set V3) (u0 u1 u2 u3 : V3)
    (hp : Packing V) (hs : saturated V) (hn : ¬ nullSet X)
    (hb : barV V 3 [u0, u1, u2, u3]) (hX : X = mcell 4 V [u0, u1, u2, u3])
    (hVX : VX V X = {u0, u1, u2, u3})
    (a b c d : V3) (hbarW : barV V 3 [a, b, c, d]) (hmW : mcell 4 V [a, b, c, d] = X) :
    dihX V X (a, b) = dihV a b c d := by
  have hsetW : setOfList [a, b, c, d] = ({a, b, c, d} : Set V3) := by
    ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]; tauto
  have hneW : mcell 4 V [a, b, c, d] ≠ ∅ := by
    intro h0; rw [hmW] at h0; exact p20k_ne_empty hn h0
  -- vertex set of the permuted witness
  have hcd : setOfList [a, b, c, d] = {u0, u1, u2, u3} := by
    have hVXw : VX V X = setOfList [a, b, c, d] := by
      have g1 : VX V (mcell 4 V [a, b, c, d]) = setOfList [a, b, c, d] :=
        p20k_VX_m4 V [a, b, c, d] hp hs hbarW (fun h0 => by rw [hmW] at h0; exact hn h0)
      exact congrArg (fun W : Set V3 => VX V W) hmW.symm ▸ g1
    rw [← hVXw, hVX]
  -- epsilon spec for the cellParamsD witness at [a, b]
  have hex : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧
      initialSublist [a, b] p.2 := ⟨(4, [a, b, c, d]), by omega, hbarW, hmW.symm, ⟨[c, d], rfl⟩⟩
  have heps := Classical.epsilon_spec (p := fun p : ℕ × List V3 =>
    p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 ∧ initialSublist [a, b] p.2) hex
  obtain ⟨hq0, hb2, hXw, hinit⟩ := heps
  have hb2' : barV V 3 (cellParamsD V X [a, b]).2 := hb2
  have hinit' : initialSublist [a, b] (cellParamsD V X [a, b]).2 := hinit
  have hXw' : X = mcell (cellParamsD V X [a, b]).1 V (cellParamsD V X [a, b]).2 := hXw
  clear hinit hXw
  have hq1 : (cellParamsD V X [a, b]).1 = 4 :=
    MCELL_CELL_PARAMETERS_D_EXIST V [a, b, c, d] [a, b] 4 X (by omega) hp hs hmW.symm hbarW
      ⟨[c, d], rfl⟩ hn
  rw [hq1] at hXw'
  have hne2 : mcell 4 V (cellParamsD V X [a, b]).2 ≠ ∅ := by
    intro h0; rw [← hXw'] at h0; exact p20k_ne_empty hn h0
  have hVX2 : VX V X = setOfList (cellParamsD V X [a, b]).2 := by
    have h1 : VX V X = V ∩ X := HDTFNFZ (v := u0) hs hp hb2' hXw' hn
    have h3 : V ∩ X = V ∩ mcell 4 V (cellParamsD V X [a, b]).2 :=
      congrArg (fun W : Set V3 => V ∩ W) hXw'
    have h4 : VX V (mcell 4 V (cellParamsD V X [a, b]).2)
        = V ∩ mcell 4 V (cellParamsD V X [a, b]).2 :=
      HDTFNFZ (v := u0) hs hp hb2' rfl
        (fun h0 => by rw [← hXw'] at h0; exact hn h0)
    have h5 : VX V (mcell 4 V (cellParamsD V X [a, b]).2)
        = setOfList (cellParamsD V X [a, b]).2 :=
      p20k_VX_m4 V (cellParamsD V X [a, b]).2 hp hs hb2'
        (fun h0 => by rw [← hXw'] at h0; exact hn h0)
    rw [h1, h3, ← h4, h5]
  have hseteq : setOfList (cellParamsD V X [a, b]).2 = {u0, u1, u2, u3} := by
    rw [← hVX2, hVX]
  -- unfold dihX to dihu4 of the witness
  rw [dihX, if_neg hn]
  show (if (cellParamsD V X [a, b]).1 = 2 then dihu2 V (cellParamsD V X [a, b]).2
    else if (cellParamsD V X [a, b]).1 = 3 then dihu3 V (cellParamsD V X [a, b]).2
    else if (cellParamsD V X [a, b]).1 = 4 then dihu4 (cellParamsD V X [a, b]).2
    else 0) = dihV a b c d
  rw [hq1]
  simp
  -- destructure the witness list
  obtain ⟨yl, hy⟩ := hinit'
  rcases yl with _ | ⟨v, yl'⟩
  · rw [hy] at hb2'; simp [barV] at hb2'
  rcases yl' with _ | ⟨w, yl''⟩
  · rw [hy] at hb2'; simp [barV] at hb2'
  rcases yl'' with _ | e
  · -- yl = [v, w]
    have hbarvw : barV V 3 [a, b, v, w] := by
      have hb2'' := hb2'
      rw [hy] at hb2''
      exact hb2''
    have hdistW := p20k_barV_distinct (x0 := a) (x1 := b) (x2 := v) (x3 := w) hbarvw
    rw [hy] at hseteq
    have hchain : setOfList ([a, b] ++ [v, w]) = ({a, b, c, d} : Set V3) := by
      rw [hseteq, ← hcd, hsetW]
    have hvin : v ∈ ({a, b, c, d} : Set V3) := by
      rw [← hchain]; simp [setOfList]
    have hwin : w ∈ ({a, b, c, d} : Set V3) := by
      rw [← hchain]; simp [setOfList]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvin hwin
    have hvcd : v = c ∨ v = d := by
      rcases hvin with h | h | h | h
      · exact absurd h.symm hdistW.2.1
      · exact absurd h.symm hdistW.2.2.2.1
      · exact Or.inl h
      · exact Or.inr h
    have hwcd : w = c ∨ w = d := by
      rcases hwin with h | h | h | h
      · exact absurd h.symm hdistW.2.2.1
      · exact absurd h.symm hdistW.2.2.2.2.1
      · exact Or.inl h
      · exact Or.inr h
    rcases hvcd with rfl | rfl <;> rcases hwcd with rfl | rfl
    any_goals exact absurd rfl hdistW.2.2.2.2.2
    all_goals
      rw [hy]
      first
      | rfl
      | exact (DIHV_SYM_2 _ _ _ _).symm
      | exact DIHV_SYM_2 _ _ _ _
  · rw [hy] at hb2'
    exfalso
    have hl := hb2'.1
    simp only [List.length_append, List.length_cons] at hl
    omega



/-! ### gammaX-side kit: pair algebra, dihX pair-swap, edge-term collapse -/

/-- two-point sets with distinct first pair: unordered-pair equality case
split. -/
private theorem p20k_pair_eq_pair {u v w z : V3} (huv : u ≠ v)
    (h : ({u, v} : Set V3) = {w, z}) :
    (u = w ∧ v = z) ∨ (u = z ∧ v = w) := by
  have hwz : w ≠ z := by
    intro h0
    rw [h0] at h
    have h1 : u ∈ ({u, v} : Set V3) := Set.mem_insert _ _
    have h2 : v ∈ ({u, v} : Set V3) := Set.mem_insert_of_mem _ (Set.mem_singleton _)
    rw [h] at h1 h2
    simp at h1 h2
    rw [h1, h2] at huv
    exact huv rfl
  have hu : u ∈ ({w, z} : Set V3) := by rw [← h]; simp
  have hv : v ∈ ({w, z} : Set V3) := by rw [← h]; simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with hu | hu
  · rcases hv with hv | hv
    · exact absurd (hu.trans hv.symm) huv
    · exact Or.inl ⟨hu, hv⟩
  · rcases hv with hv | hv
    · exact Or.inr ⟨hu, hv⟩
    · exact absurd (hu.trans hv.symm) huv

/-- shared-first-point two-point sets differ. -/
private theorem p20k_pair_ne_sh1 {u v w : V3} (huv : u ≠ v) (huw : u ≠ w) (h : v ≠ w) :
    ({u, v} : Set V3) ≠ ({u, w} : Set V3) := by
  intro hEq
  rcases p20k_pair_eq_pair huv hEq with ⟨_, e⟩ | ⟨e, _⟩
  · exact h e
  · exact huw e

/-- generic two-point sets differ (first component of each case kills). -/
private theorem p20k_pair_ne_gen {u v w z : V3} (huv : u ≠ v) (h1 : u ≠ w) (h2 : u ≠ z) :
    ({u, v} : Set V3) ≠ ({w, z} : Set V3) := by
  intro hEq
  rcases p20k_pair_eq_pair huv hEq with ⟨e, _⟩ | ⟨e, _⟩
  · exact h1 e
  · exact h2 e

/-- generic two-point sets differ (second component of each case kills). -/
private theorem p20k_pair_ne_gen2 {u v w z : V3} (huv : u ≠ v) (h3 : v ≠ w) (h4 : v ≠ z) :
    ({u, v} : Set V3) ≠ ({w, z} : Set V3) := by
  intro hEq
  rcases p20k_pair_eq_pair huv hEq with ⟨_, e⟩ | ⟨_, e⟩
  · exact h4 e
  · exact h3 e

/-- `dihX` across an edge is independent of the edge orientation. -/
private theorem p20k_dihX_swap (V X : Set V3) (a b c d : V3)
    (hp : Packing V) (hs : saturated V) (hn : ¬ nullSet X)
    (hb : barV V 3 [a, b, c, d]) (hX : X = mcell 4 V [a, b, c, d]) :
    dihX V X (b, a) = dihX V X (a, b) := by
  have hne : mcell 4 V [a, b, c, d] ≠ ∅ := by
    intro h0
    apply hn
    rw [hX, h0]
    exact measure_empty
  have hset4 : setOfList [a, b, c, d] = ({a, b, c, d} : Set V3) := by
    ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]; tauto
  have hnull : ¬ nullSet (mcell 4 V [a, b, c, d]) := by
    rw [← hX]
    exact hn
  have hVX : VX V X = {a, b, c, d} := by
    have g1 := p20k_VX_m4 V [a, b, c, d] hp hs hb hnull
    rw [hX, g1, hset4]
  have hfw := p20k_dihX_m4 V X a b c d hp hs hn hb hX hVX a b c d hb hX.symm
  obtain ⟨hbarR, hmR⟩ := p20k_perm_wit V a b c d hs hp hb hne b a c d
    (Equiv.symm (Equiv.swap 0 1))
    (show Equiv.symm (Equiv.swap 0 1) 0 = 1 by decide)
    (show Equiv.symm (Equiv.swap 0 1) 1 = 0 by decide)
    (show Equiv.symm (Equiv.swap 0 1) 2 = 2 by decide)
    (show Equiv.symm (Equiv.swap 0 1) 3 = 3 by decide)
    (by norm_num)
    (by
      intro j hj
      rw [Equiv.symm_apply_eq]
      exact (Equiv.swap_apply_of_ne_of_ne (show j ≠ 0 by omega) (show j ≠ 1 by omega)).symm)
    (by
      rw [leftActionList, Equiv.symm_symm]
      simp [List.range_succ, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne])
  have hrev := p20k_dihX_m4 V X a b c d hp hs hn hb hX hVX b a c d hbarR
    (by rw [hmR]; exact hX.symm)
  rw [hrev, hfw, DIHV_SYM a b c d]

/-- one edge term of the `gammaX` inner sum collapses to the canonical
orientation (epsilon pair after zeta/beta). -/
private theorem p20k_edge_term_eps {V X : Set V3} {u v : V3} (huv : u ≠ v) (f : ℝ → ℝ)
    (hsym : dihX V X (v, u) = dihX V X (u, v)) :
    dihX V X
        ((Classical.epsilon fun r : V3 × V3 => ({u, v} : Set V3) = {r.1, r.2}).1,
          (Classical.epsilon fun r : V3 × V3 => ({u, v} : Set V3) = {r.1, r.2}).2) *
      f (hl [(Classical.epsilon fun r : V3 × V3 => ({u, v} : Set V3) = {r.1, r.2}).1,
        (Classical.epsilon fun r : V3 × V3 => ({u, v} : Set V3) = {r.1, r.2}).2]) =
    dihX V X (u, v) * f (hl [u, v]) := by
  have hspec := Classical.epsilon_spec
    (p := fun r : V3 × V3 => ({u, v} : Set V3) = {r.1, r.2}) ⟨(u, v), rfl⟩
  have key : ∀ a b : V3, ({u, v} : Set V3) = {a, b} →
      dihX V X (a, b) * f (hl [a, b]) = dihX V X (u, v) * f (hl [u, v]) := by
    intro a b hab
    rcases p20k_pair_eq_pair huv hab with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [← e1, ← e2, hsym, HL_2, HL_2, dist_comm v u]
  exact key _ _ hspec

private theorem p20k_setSum_quad {α : Type*} {a b c d : α} (f : α → ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    setSum {a, b, c, d} f = f a + f b + f c + f d := by
  unfold setSum
  rw [dif_pos (Set.toFinite ({a, b, c, d} : Set α))]
  simp only [Set.Finite.toFinset_insert, Set.Finite.toFinset_singleton]
  simp [hab, hac, had, hbc, hbd, hcd, Finset.sum_insert]
  ring

private theorem p20k_setSum_sext {α : Type*} {a b c d e g : α} {f : α → ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hag : a ≠ g)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbg : b ≠ g)
    (hcd : c ≠ d) (hce : c ≠ e) (hcg : c ≠ g)
    (hde : d ≠ e) (hdg : d ≠ g) (heg : e ≠ g) :
    setSum {a, b, c, d, e, g} f
      = f a + f b + f c + f d + f e + f g := by
  unfold setSum
  rw [dif_pos (Set.toFinite ({a, b, c, d, e, g} : Set α))]
  simp only [Set.Finite.toFinset_insert, Set.Finite.toFinset_singleton]
  simp [hab, hac, had, hae, hag, hbc, hbd, hbe, hbg, hcd, hce, hcg, hde, hdg, heg,
    Finset.sum_insert]
  ring

/-! ### DIHX_DIH_Y_lemma -/

open Module in
private theorem p20k_span_pair_ne_top (p q : V3) :
    Submodule.span ℝ ({p, q} : Set V3) ≠ ⊤ := by
  intro h
  have hle : finrank ℝ (Submodule.span ℝ ({p, q} : Set V3)) ≤ 2 := by
    have hh := finrank_span_finset_le_card (R := ℝ) ({p, q} : Finset V3)
    unfold Set.finrank at hh
    rw [show (({p, q} : Finset V3) : Set V3) = ({p, q} : Set V3) from by simp] at hh
    have h2 : ({p, q} : Finset V3).card ≤ 2 := by
      calc ({p, q} : Finset V3).card ≤ ({q} : Finset V3).card + 1 :=
          Finset.card_insert_le p {q}
        _ = 2 := by simp
    omega
  rw [h, finrank_top] at hle
  have h3 : finrank ℝ V3 = 3 := by
    simp [V3, finrank_euclideanSpace_fin]
  omega

private theorem p20k_plane_null (v0 p q : V3) :
    volume ((fun z : V3 => v0 + z) '' (Submodule.span ℝ ({p, q} : Set V3))) = 0 := by
  have hpre : (fun z : V3 => v0 + z) '' (Submodule.span ℝ ({p, q} : Set V3))
      = (fun z : V3 => -v0 + z) ⁻¹' (Submodule.span ℝ ({p, q} : Set V3)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro h
      exact ⟨-v0 + z, by simpa using h, by abel⟩
  rw [hpre, measure_preimage_add]
  exact MeasureTheory.Measure.addHaar_submodule volume _ (p20k_span_pair_ne_top p q)

/-- a collinear triple among four points forces coplanarity of the 4-set
(general form: `s` is the 4-point set, `z`-test via membership). -/
private theorem p20k_cop_of_col {s : Set V3} {p q r w : V3} (hpq : p ≠ q)
    (hcol : Collinear ℝ ({p, q, r} : Set V3))
    (hmem : ∀ z : V3, z ∈ s → z ∈ ({p, q, r, w} : Set V3)) :
    Coplanar s := by
  obtain ⟨a, b, c, hsub⟩ := p20k_col_coplanar hpq hcol
  exact ⟨a, b, c, fun z hz => hsub (hmem z hz)⟩

private theorem p20k_swap_fix {a b : ℕ} (ha : a < 4) (hb : b < 4) (j : ℕ)
    (hj : 4 ≤ j) : Equiv.swap a b j = j :=
  Equiv.swap_apply_of_ne_of_ne (show j ≠ a by omega) (show j ≠ b by omega)


/-- HOL `DIHX_DIH_Y_lemma` (TSKAJXY1.hl:567): the six dihedral angles of
a saturated-packing 4-cell are the `dih_y` values of the edge-length
six-tuple (per the per-edge argument permutation).

PROVED (2026-10-08, kit-下移波): X reduces to mcell 4; `VX V X` is pinned
by HDTFNFZ + LEPJBDJ; non-coplanarity from the null-plane argument; each
edge dispatches through `cellParamsD` (the kit above) on the permuted
witness list `leftActionList p [u0;u1;u2;u3]` (QZKSYKG1 + RVFXZBU), and
the head `dihu4` folds to `dih_y` via DIHV_EQ_DIH_Y_4PT_B (the (u2,u3)
slot additionally through DIHV_SYM). -/
theorem DIHX_DIH_Y_lemma (V X : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3) (i : ℕ)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hi : 4 ≤ i) (hX : X = mcell i V ul) (hn : ¬ nullSet X)
    (hul : ul = [u0, u1, u2, u3]) (hy1 : dist u0 u1 = y1) (hy2 : dist u0 u2 = y2)
    (hy3 : dist u0 u3 = y3) (hy4 : dist u2 u3 = y4) (hy5 : dist u1 u3 = y5)
    (hy6 : dist u1 u2 = y6) :
    dihX V X (u0, u1) = dihY y1 y2 y3 y4 y5 y6 ∧
      dihX V X (u0, u2) = dihY y2 y3 y1 y5 y6 y4 ∧
      dihX V X (u0, u3) = dihY y3 y1 y2 y6 y4 y5 ∧
      dihX V X (u2, u3) = dihY y4 y3 y5 y1 y6 y2 ∧
      dihX V X (u1, u3) = dihY y5 y1 y6 y2 y4 y3 ∧
      dihX V X (u1, u2) = dihY y6 y1 y5 y3 y4 y2 := by

  subst hul
  have hd := p20k_barV_distinct hb
  have t10 : dist u1 u0 = y1 := by rw [dist_comm]; exact hy1
  have t20 : dist u2 u0 = y2 := by rw [dist_comm]; exact hy2
  have t30 : dist u3 u0 = y3 := by rw [dist_comm]; exact hy3
  have t32 : dist u3 u2 = y4 := by rw [dist_comm]; exact hy4
  have t31 : dist u3 u1 = y5 := by rw [dist_comm]; exact hy5
  have t21 : dist u2 u1 = y6 := by rw [dist_comm]; exact hy6
  have hX4 : X = mcell 4 V [u0, u1, u2, u3] := by rw [hX, p20k_mcell_ge4 hi]
  have hXne : X ≠ ∅ := p20k_ne_empty hn
  have hne4 : mcell 4 V [u0, u1, u2, u3] ≠ ∅ := by
    intro h0
    rw [← hX4] at h0
    exact hXne h0
  have hVX : VX V X = {u0, u1, u2, u3} := by
    have g1 := p20k_VX_m4 V [u0, u1, u2, u3] hp hs hb
      (fun h0 => by rw [← hX4] at h0; exact hn h0)
    rw [hX4, g1]
    ext z
    simp only [setOfList, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  -- the four points are not coplanar (else the cell is null)
  have hnc : ¬ Coplanar ({u0, u1, u2, u3} : Set V3) := by
    intro hcop
    obtain ⟨p, q, r, hsub⟩ := hcop
    have hsub2 : convexHull ℝ ({u0, u1, u2, u3} : Set V3)
        ⊆ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := by
      refine convexHull_min ?_ (affineSpan ℝ ({p, q, r} : Set V3)).convex
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz | hz
      · rw [hz]; exact hsub (by simp)
      · rw [hz]; exact hsub (by simp)
      · rw [hz]; exact hsub (by simp)
      · rw [hz]; exact hsub (by simp)
    have hspan : (affineSpan ℝ ({p, q, r} : Set V3) : Set V3)
        ⊆ (fun z : V3 => p + z) '' (Submodule.span ℝ ({q - p, r - p} : Set V3)) := by
      have hW : (affineSpan ℝ ({p, q, r} : Set V3))
          ≤ AffineSubspace.mk' p (Submodule.span ℝ ({q - p, r - p} : Set V3)) := by
        rw [affineSpan_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz | hz | hz
        · rw [hz]
          exact AffineSubspace.mem_mk'.mpr
            (by rw [vsub_self]; exact Submodule.zero_mem _)
        · rw [hz]
          exact AffineSubspace.mem_mk'.mpr
            (Submodule.subset_span (by simp [vsub_eq_sub]))
        · rw [hz]
          exact AffineSubspace.mem_mk'.mpr
            (Submodule.subset_span (by simp [vsub_eq_sub]))
      intro z hz
      have hz' := hW hz
      exact ⟨z -ᵥ p, AffineSubspace.mem_mk'.mp hz', by simp⟩
    have hvol0 : volume ((fun z : V3 => p + z) ''
        (Submodule.span ℝ ({q - p, r - p} : Set V3))) = 0 :=
      p20k_plane_null p (q - p) (r - p)
    have hvX : volume X ≤ 0 := by
      rw [hX4, p20k_mcell4_hull hne4,
        show setOfList [u0, u1, u2, u3] = ({u0, u1, u2, u3} : Set V3) from by
          ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq,
            Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
      calc volume (convexHull ℝ ({u0, u1, u2, u3} : Set V3))
          ≤ volume ((affineSpan ℝ ({p, q, r} : Set V3) : Set V3)) :=
            measure_mono hsub2
        _ ≤ volume ((fun z : V3 => p + z) ''
              (Submodule.span ℝ ({q - p, r - p} : Set V3))) := measure_mono hspan
        _ = 0 := hvol0
    exact absurd (le_antisymm hvX zero_le) hn
  -- the twelve face non-collinearities (via collinear-triple ⇒ coplanar)
  have hncf : ∀ (p q r w : V3), p ≠ q →
      (∀ z : V3, z ∈ ({u0, u1, u2, u3} : Set V3) → z ∈ ({p, q, r, w} : Set V3)) →
      ¬ Collinear ℝ ({p, q, r} : Set V3) := by
    intro p q r w hpq hmem hcol
    exact hnc (p20k_cop_of_col hpq hcol hmem)
  have hf012 := hncf u0 u1 u2 u3 hd.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf013 := hncf u0 u1 u3 u2 hd.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf023 := hncf u0 u2 u3 u1 hd.2.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf021 := hncf u0 u2 u1 u3 hd.2.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf031 := hncf u0 u3 u1 u2 hd.2.2.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf032 := hncf u0 u3 u2 u1 hd.2.2.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf320 := hncf u3 u2 u0 u1 (Ne.symm hd.2.2.2.2.2) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf321 := hncf u3 u2 u1 u0 (Ne.symm hd.2.2.2.2.2) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf130 := hncf u1 u3 u0 u2 hd.2.2.2.2.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf132 := hncf u1 u3 u2 u0 hd.2.2.2.2.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf120 := hncf u1 u2 u0 u3 hd.2.2.2.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hf123 := hncf u1 u2 u3 u0 hd.2.2.2.1 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- edge (u0, u1)
    have hE := p20k_dihX_m4 V X u0 u1 u2 u3 hp hs hn hb hX4 hVX u0 u1 u2 u3 hb hX4.symm
    rw [hE, DIHV_EQ_DIH_Y_4PT_B u0 u1 u2 u3 hf012 hf013, hy1, hy2, hy3, hy4, hy5, hy6]
  · -- edge (u0, u2) through the witness [u0 u2 u3 u1]
    have hw := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u0 u2 u3 u1
      (Equiv.symm ((Equiv.swap (1:ℕ) 2).trans (Equiv.swap (1:ℕ) 3)))
      (show Equiv.symm ((Equiv.swap (1:ℕ) 2).trans (Equiv.swap (1:ℕ) 3)) 0 = 0 by decide)
      (show Equiv.symm ((Equiv.swap (1:ℕ) 2).trans (Equiv.swap (1:ℕ) 3)) 1 = 3 by decide)
      (show Equiv.symm ((Equiv.swap (1:ℕ) 2).trans (Equiv.swap (1:ℕ) 3)) 2 = 1 by decide)
      (show Equiv.symm ((Equiv.swap (1:ℕ) 2).trans (Equiv.swap (1:ℕ) 3)) 3 = 2 by decide)
      (by norm_num)
      (by
        intro j hj
        rw [Equiv.symm_apply_eq, Equiv.trans_apply]
        show j = (Equiv.swap (1:ℕ) 3) ((Equiv.swap (1:ℕ) 2) j)
        have hA : (Equiv.swap (1:ℕ) 2) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (1:ℕ) by omega) (show j ≠ 2 by omega)
        have hB : (Equiv.swap (1:ℕ) 3) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (1:ℕ) by omega) (show j ≠ 3 by omega)
        rw [hA, hB])
      (by
        rw [leftActionList, Equiv.symm_symm]
        simp [List.range_succ, Equiv.trans_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne])
    have hE := p20k_dihX_m4 V X u0 u1 u2 u3 hp hs hn hb hX4 hVX u0 u2 u3 u1 hw.1
      (by rw [hw.2]; exact hX4.symm)
    rw [hE, DIHV_EQ_DIH_Y_4PT_B u0 u2 u3 u1 hf023 hf021, hy2, hy3, hy1, t31, t21, hy4]
  · -- edge (u0, u3) through the witness [u0 u3 u1 u2]
    have hw := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u0 u3 u1 u2
      (Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (1:ℕ) 2)))
      (show Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (1:ℕ) 2)) 0 = 0 by decide)
      (show Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (1:ℕ) 2)) 1 = 2 by decide)
      (show Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (1:ℕ) 2)) 2 = 3 by decide)
      (show Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (1:ℕ) 2)) 3 = 1 by decide)
      (by norm_num)
      (by
        intro j hj
        rw [Equiv.symm_apply_eq, Equiv.trans_apply]
        show j = (Equiv.swap (1:ℕ) 2) ((Equiv.swap (1:ℕ) 3) j)
        have hA : (Equiv.swap (1:ℕ) 3) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (1:ℕ) by omega) (show j ≠ 3 by omega)
        have hB : (Equiv.swap (1:ℕ) 2) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (1:ℕ) by omega) (show j ≠ 2 by omega)
        rw [hA, hB])
      (by
        rw [leftActionList, Equiv.symm_symm]
        simp [List.range_succ, Equiv.trans_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne])
    have hE := p20k_dihX_m4 V X u0 u1 u2 u3 hp hs hn hb hX4 hVX u0 u3 u1 u2 hw.1
      (by rw [hw.2]; exact hX4.symm)
    rw [hE, DIHV_EQ_DIH_Y_4PT_B u0 u3 u1 u2 hf031 hf032, hy3, hy1, hy2, hy6, t32, t31]
  · -- edge (u2, u3) through the witness [u2 u3 u0 u1]
    have hw := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u2 u3 u0 u1
      (Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (0:ℕ) 2)))
      (show Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (0:ℕ) 2)) 0 = 2 by decide)
      (show Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (0:ℕ) 2)) 1 = 3 by decide)
      (show Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (0:ℕ) 2)) 2 = 0 by decide)
      (show Equiv.symm ((Equiv.swap (1:ℕ) 3).trans (Equiv.swap (0:ℕ) 2)) 3 = 1 by decide)
      (by norm_num)
      (by
        intro j hj
        rw [Equiv.symm_apply_eq, Equiv.trans_apply]
        show j = (Equiv.swap (0:ℕ) 2) ((Equiv.swap (1:ℕ) 3) j)
        have hA : (Equiv.swap (1:ℕ) 3) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (1:ℕ) by omega) (show j ≠ 3 by omega)
        have hB : (Equiv.swap (0:ℕ) 2) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (0:ℕ) by omega) (show j ≠ 2 by omega)
        rw [hA, hB])
      (by
        rw [leftActionList, Equiv.symm_symm]
        simp [List.range_succ, Equiv.trans_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne])
    have hE := p20k_dihX_m4 V X u0 u1 u2 u3 hp hs hn hb hX4 hVX u2 u3 u0 u1 hw.1
      (by rw [hw.2]; exact hX4.symm)
    rw [hE, DIHV_SYM u2 u3 u0 u1,
      DIHV_EQ_DIH_Y_4PT_B u3 u2 u0 u1 hf320 hf321, t32, t30, t31, hy1, t21, t20]
  · -- edge (u1, u3) through the witness [u1 u3 u0 u2]
    have hw := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u1 u3 u0 u2
      (Equiv.symm ((Equiv.swap (0:ℕ) 1).trans ((Equiv.swap (0:ℕ) 3).trans (Equiv.swap (0:ℕ) 2))))
      (show Equiv.symm ((Equiv.swap (0:ℕ) 1).trans ((Equiv.swap (0:ℕ) 3).trans (Equiv.swap (0:ℕ) 2))) 0 = 2 by decide)
      (show Equiv.symm ((Equiv.swap (0:ℕ) 1).trans ((Equiv.swap (0:ℕ) 3).trans (Equiv.swap (0:ℕ) 2))) 1 = 0 by decide)
      (show Equiv.symm ((Equiv.swap (0:ℕ) 1).trans ((Equiv.swap (0:ℕ) 3).trans (Equiv.swap (0:ℕ) 2))) 2 = 3 by decide)
      (show Equiv.symm ((Equiv.swap (0:ℕ) 1).trans ((Equiv.swap (0:ℕ) 3).trans (Equiv.swap (0:ℕ) 2))) 3 = 1 by decide)
      (by norm_num)
      (by
        intro j hj
        rw [Equiv.symm_apply_eq, Equiv.trans_apply]
        show j = (Equiv.swap (0:ℕ) 2) ((Equiv.swap (0:ℕ) 3) ((Equiv.swap (0:ℕ) 1) j))
        have hA : (Equiv.swap (0:ℕ) 1) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (0:ℕ) by omega) (show j ≠ 1 by omega)
        have hB : (Equiv.swap (0:ℕ) 3) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (0:ℕ) by omega) (show j ≠ 3 by omega)
        have hC : (Equiv.swap (0:ℕ) 2) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (0:ℕ) by omega) (show j ≠ 2 by omega)
        rw [hA, hB, hC])
      (by
        rw [leftActionList, Equiv.symm_symm]
        simp [List.range_succ, Equiv.trans_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne])
    have hE := p20k_dihX_m4 V X u0 u1 u2 u3 hp hs hn hb hX4 hVX u1 u3 u0 u2 hw.1
      (by rw [hw.2]; exact hX4.symm)
    rw [hE, DIHV_EQ_DIH_Y_4PT_B u1 u3 u0 u2 hf130 hf132, hy5, t10, hy6, hy2, t32, t30]
  · -- edge (u1, u2) through the witness [u1 u2 u0 u3]
    have hw := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u1 u2 u0 u3
      (Equiv.symm ((Equiv.swap (0:ℕ) 1).trans (Equiv.swap (0:ℕ) 2)))
      (show Equiv.symm ((Equiv.swap (0:ℕ) 1).trans (Equiv.swap (0:ℕ) 2)) 0 = 2 by decide)
      (show Equiv.symm ((Equiv.swap (0:ℕ) 1).trans (Equiv.swap (0:ℕ) 2)) 1 = 0 by decide)
      (show Equiv.symm ((Equiv.swap (0:ℕ) 1).trans (Equiv.swap (0:ℕ) 2)) 2 = 1 by decide)
      (show Equiv.symm ((Equiv.swap (0:ℕ) 1).trans (Equiv.swap (0:ℕ) 2)) 3 = 3 by decide)
      (by norm_num)
      (by
        intro j hj
        rw [Equiv.symm_apply_eq, Equiv.trans_apply]
        show j = (Equiv.swap (0:ℕ) 2) ((Equiv.swap (0:ℕ) 1) j)
        have hA : (Equiv.swap (0:ℕ) 1) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (0:ℕ) by omega) (show j ≠ 1 by omega)
        have hB : (Equiv.swap (0:ℕ) 2) j = j :=
          Equiv.swap_apply_of_ne_of_ne (show j ≠ (0:ℕ) by omega) (show j ≠ 2 by omega)
        rw [hA, hB])
      (by
        rw [leftActionList, Equiv.symm_symm]
        simp [List.range_succ, Equiv.trans_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne])
    have hE := p20k_dihX_m4 V X u0 u1 u2 u3 hp hs hn hb hX4 hVX u1 u2 u0 u3 hw.1
      (by rw [hw.2]; exact hX4.symm)
    rw [hE, DIHV_EQ_DIH_Y_4PT_B u1 u2 u0 u3 hf120 hf123, hy6, t10, hy5, hy3, hy4, t20]



/-- PROBE-ONLY stub of the hub's SOL_SOLID_TRIANGLE (the real proved
theorem lives in PackingAuto20.lean:265; this probe validates only the
SOL_SOL_Y_EXPLICIT assembly). -/
axiom SOL_SOLID_TRIANGLE_probe {a b c : ℝ} (v0 v1 v2 v3 : V3)
    (hnc : ¬ Coplanar ({v0, v1, v2, v3} : Set V3))
    (ha : a = dihV v0 v1 v2 v3) (hb : b = dihV v0 v2 v3 v1)
    (hc : c = dihV v0 v3 v1 v2) :
    sol v0 (convexHull ℝ ({v0, v1, v2, v3} : Set V3)) = a + b + c - Real.pi

/-- HOL `SOL_SOL_Y_EXPLICIT` (TSKAJXY1.hl:2995): the four vertex solid
angles of a 4-cell are the `sol_y` values of the edge six-tuple.

PROVED (2026-10-08): SOL_SOLID_TRIANGLE at the four vertices with faces
(u1,u2,u3), (u0,u3,u2), (u1,u3,u0), (u2,u1,u0); every dihV term folds to
its dihY slot pattern through DIHV_EQ_DIH_Y_4PT_B (t-helpers absorb the
reversed `dist` arguments). -/
theorem SOL_SOL_Y_EXPLICIT (V X : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3) (i : ℕ)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hi : 4 ≤ i) (hX : X = mcell i V ul) (hn : ¬ nullSet X)
    (hul : ul = [u0, u1, u2, u3]) (hy1 : dist u0 u1 = y1) (hy2 : dist u0 u2 = y2)
    (hy3 : dist u0 u3 = y3) (hy4 : dist u2 u3 = y4) (hy5 : dist u1 u3 = y5)
    (hy6 : dist u1 u2 = y6) :
    sol u0 X = solY y1 y2 y3 y4 y5 y6 ∧
      sol u1 X = solY y1 y5 y6 y4 y2 y3 ∧
      sol u2 X = solY y4 y2 y6 y1 y5 y3 ∧
      sol u3 X = solY y4 y5 y3 y1 y2 y6 := by

  subst hul
  have hd := p20k_barV_distinct hb
  have t10 : dist u1 u0 = y1 := by rw [dist_comm]; exact hy1
  have t20 : dist u2 u0 = y2 := by rw [dist_comm]; exact hy2
  have t30 : dist u3 u0 = y3 := by rw [dist_comm]; exact hy3
  have t32 : dist u3 u2 = y4 := by rw [dist_comm]; exact hy4
  have t31 : dist u3 u1 = y5 := by rw [dist_comm]; exact hy5
  have t21 : dist u2 u1 = y6 := by rw [dist_comm]; exact hy6
  have hX4 : X = mcell 4 V [u0, u1, u2, u3] := by rw [hX, p20k_mcell_ge4 hi]
  have hXne : X ≠ ∅ := p20k_ne_empty hn
  have hne4 : mcell 4 V [u0, u1, u2, u3] ≠ ∅ := by
    intro h0
    rw [← hX4] at h0
    exact hXne h0
  have hVX : VX V X = {u0, u1, u2, u3} := by
    have g1 := p20k_VX_m4 V [u0, u1, u2, u3] hp hs hb
      (fun h0 => by rw [← hX4] at h0; exact hn h0)
    rw [hX4, g1]
    ext z
    simp only [setOfList, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  -- the four points are not coplanar (else the cell is null)
  have hnc : ¬ Coplanar ({u0, u1, u2, u3} : Set V3) := by
    intro hcop
    obtain ⟨p, q, r, hsub⟩ := hcop
    have hsub2 : convexHull ℝ ({u0, u1, u2, u3} : Set V3)
        ⊆ (affineSpan ℝ ({p, q, r} : Set V3) : Set V3) := by
      refine convexHull_min ?_ (affineSpan ℝ ({p, q, r} : Set V3)).convex
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz | hz
      · rw [hz]; exact hsub (by simp)
      · rw [hz]; exact hsub (by simp)
      · rw [hz]; exact hsub (by simp)
      · rw [hz]; exact hsub (by simp)
    have hspan : (affineSpan ℝ ({p, q, r} : Set V3) : Set V3)
        ⊆ (fun z : V3 => p + z) '' (Submodule.span ℝ ({q - p, r - p} : Set V3)) := by
      have hW : (affineSpan ℝ ({p, q, r} : Set V3))
          ≤ AffineSubspace.mk' p (Submodule.span ℝ ({q - p, r - p} : Set V3)) := by
        rw [affineSpan_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with hz | hz | hz
        · rw [hz]
          exact AffineSubspace.mem_mk'.mpr
            (by rw [vsub_self]; exact Submodule.zero_mem _)
        · rw [hz]
          exact AffineSubspace.mem_mk'.mpr
            (Submodule.subset_span (by simp [vsub_eq_sub]))
        · rw [hz]
          exact AffineSubspace.mem_mk'.mpr
            (Submodule.subset_span (by simp [vsub_eq_sub]))
      intro z hz
      have hz' := hW hz
      exact ⟨z -ᵥ p, AffineSubspace.mem_mk'.mp hz', by simp⟩
    have hvol0 : volume ((fun z : V3 => p + z) ''
        (Submodule.span ℝ ({q - p, r - p} : Set V3))) = 0 :=
      p20k_plane_null p (q - p) (r - p)
    have hvX : volume X ≤ 0 := by
      rw [hX4, p20k_mcell4_hull hne4,
        show setOfList [u0, u1, u2, u3] = ({u0, u1, u2, u3} : Set V3) from by
          ext z; simp only [setOfList, List.mem_cons, Set.mem_setOf_eq,
            Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
      calc volume (convexHull ℝ ({u0, u1, u2, u3} : Set V3))
          ≤ volume ((affineSpan ℝ ({p, q, r} : Set V3) : Set V3)) :=
            measure_mono hsub2
        _ ≤ volume ((fun z : V3 => p + z) ''
              (Submodule.span ℝ ({q - p, r - p} : Set V3))) := measure_mono hspan
        _ = 0 := hvol0
    exact absurd (le_antisymm hvX zero_le) hn

  -- the twelve face non-collinearities
  have hncf : ∀ (p q r w : V3), p ≠ q →
      (∀ z : V3, z ∈ ({u0, u1, u2, u3} : Set V3) → z ∈ ({p, q, r, w} : Set V3)) →
      ¬ Collinear ℝ ({p, q, r} : Set V3) := by
    intro p q r w hpq hmem hcol
    exact hnc (p20k_cop_of_col hpq hcol hmem)
  have hn01 : u0 ≠ u1 := hd.1
  have hn02 : u0 ≠ u2 := hd.2.1
  have hn03 : u0 ≠ u3 := hd.2.2.1
  have hn12 : u1 ≠ u2 := hd.2.2.2.1
  have hn13 : u1 ≠ u3 := hd.2.2.2.2.1
  have hn23 : u2 ≠ u3 := hd.2.2.2.2.2
  -- hull reordering: the canonical 4-point set equals each permuted face set
  have hp0123 : setOfList [u0, u1, u2, u3] = ({u0, u1, u2, u3} : Set V3) := by
    ext z
    simp only [setOfList, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have hperm1 : ({u0, u1, u2, u3} : Set V3) = ({u1, u0, u3, u2} : Set V3) := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hperm2 : ({u0, u1, u2, u3} : Set V3) = ({u2, u1, u3, u0} : Set V3) := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hperm3 : ({u0, u1, u2, u3} : Set V3) = ({u3, u2, u1, u0} : Set V3) := by
    ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- vertex u0, face (u1, u2, u3)
    have s0 := SOL_SOLID_TRIANGLE (a := dihV u0 u1 u2 u3) (b := dihV u0 u2 u3 u1)
      (c := dihV u0 u3 u1 u2) u0 u1 u2 u3 hnc rfl rfl rfl
    have f1 := DIHV_EQ_DIH_Y_4PT_B u0 u1 u2 u3
      (hncf u0 u1 u2 u3 hn01 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u0 u1 u3 u2 hn01 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    have f2 := DIHV_EQ_DIH_Y_4PT_B u0 u2 u3 u1
      (hncf u0 u2 u3 u1 hn02 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u0 u2 u1 u3 hn02 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    have f3 := DIHV_EQ_DIH_Y_4PT_B u0 u3 u1 u2
      (hncf u0 u3 u1 u2 hn03 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u0 u3 u2 u1 hn03 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    rw [hX4, p20k_mcell4_hull hne4, hp0123, s0, f1, f2, f3,
      hy1, hy2, hy3, hy4, hy5, hy6, t31, t21, t32]
    rfl
  · -- vertex u1, face (u0, u3, u2)
    have s1 := SOL_SOLID_TRIANGLE (a := dihV u1 u0 u3 u2) (b := dihV u1 u3 u2 u0)
      (c := dihV u1 u2 u0 u3) u1 u0 u3 u2
      (by intro hc; exact hnc (by rw [hperm1]; exact hc)) rfl rfl rfl
    have f1 := DIHV_EQ_DIH_Y_4PT_B u1 u0 u3 u2
      (hncf u1 u0 u3 u2 (Ne.symm hn01) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u1 u0 u2 u3 (Ne.symm hn01) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    have f2 := DIHV_EQ_DIH_Y_4PT_B u1 u3 u2 u0
      (hncf u1 u3 u2 u0 hn13 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u1 u3 u0 u2 hn13 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    have f3 := DIHV_EQ_DIH_Y_4PT_B u1 u2 u0 u3
      (hncf u1 u2 u0 u3 hn12 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u1 u2 u3 u0 hn12 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    rw [hX4, p20k_mcell4_hull hne4, hp0123, hperm1, s1, f1, f2, f3,
      t10, hy5, hy6, t32, hy2, hy3, t20, t30, hy4]
    rfl
  · -- vertex u2, face (u1, u3, u0)
    have s2 := SOL_SOLID_TRIANGLE (a := dihV u2 u1 u3 u0) (b := dihV u2 u3 u0 u1)
      (c := dihV u2 u0 u1 u3) u2 u1 u3 u0
      (by intro hc; exact hnc (by rw [hperm2]; exact hc)) rfl rfl rfl
    have f1 := DIHV_EQ_DIH_Y_4PT_B u2 u1 u3 u0
      (hncf u2 u1 u3 u0 (Ne.symm hn12) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u2 u1 u0 u3 (Ne.symm hn12) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    have f2 := DIHV_EQ_DIH_Y_4PT_B u2 u3 u0 u1
      (hncf u2 u3 u0 u1 hn23 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u2 u3 u1 u0 hn23 (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    have f3 := DIHV_EQ_DIH_Y_4PT_B u2 u0 u1 u3
      (hncf u2 u0 u1 u3 (Ne.symm hn02) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u2 u0 u3 u1 (Ne.symm hn02) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    rw [hX4, p20k_mcell4_hull hne4, hp0123, hperm2, s2, f1, f2, f3,
      t21, hy4, t20, t30, t10, hy5, hy1, t31, hy3]
    unfold solY
    abel
  · -- vertex u3, face (u2, u1, u0)
    have s3 := SOL_SOLID_TRIANGLE (a := dihV u3 u2 u1 u0) (b := dihV u3 u1 u0 u2)
      (c := dihV u3 u0 u2 u1) u3 u2 u1 u0
      (by intro hc; exact hnc (by rw [hperm3]; exact hc)) rfl rfl rfl
    have f1 := DIHV_EQ_DIH_Y_4PT_B u3 u2 u1 u0
      (hncf u3 u2 u1 u0 (Ne.symm hn23) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u3 u2 u0 u1 (Ne.symm hn23) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    have f2 := DIHV_EQ_DIH_Y_4PT_B u3 u1 u0 u2
      (hncf u3 u1 u0 u2 (Ne.symm hn13) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u3 u1 u2 u0 (Ne.symm hn13) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    have f3 := DIHV_EQ_DIH_Y_4PT_B u3 u0 u2 u1
      (hncf u3 u0 u2 u1 (Ne.symm hn03) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
      (hncf u3 u0 u1 u2 (Ne.symm hn03) (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    rw [hX4, p20k_mcell4_hull hne4, hp0123, hperm3, s3, f1, f2, f3,
      t32, t31, t30, t10, t20, t21, hy2, hy6, hy1]
    rfl

/-- HOL `gammaX_gamm4fgcy` (TSKAJXY1.hl:3508): volume and `gammaX` of a
4-cell are the analytic `vol_y` / `gamma4fgcy` of the edge six-tuple.

PROVED (2026-10-08, SimplexVolume 消费波): the volume half via the
SimplexVolume bridge `volume_real_convexHull_tetra` (X reduces to
`mcell 4` = `convexHull ℝ {u0,u1,u2,u3}` through `p20k_mcell4_hull`, then
`hy1..hy6` slot in verbatim); the gammaX half via SOL_SOL_Y_EXPLICIT
(four vertex sols = the four `sol_y` slots of `vol4f`),
DIHX_DIH_Y_lemma (six `dihX` values = the six `dih_y` slots), and the
new gammaX-side kit: `p20k_dihX_swap` (edge orientation independence,
via one generic position-swap perm + DIHV_SYM) and `p20k_edge_term_eps`
(the `Classical.epsilon` pattern-pair term collapses to the canonical
orientation, HL SUM_PAIR_2_SET rendered as the explicit six-pair setSum
expansion). sorryAx taint inherited from the PA5/PA6 omega-tower base
(HDTFNFZ/LEPJBDJ/QZKSYKG1/RVFXZBU), same as the DIHX/SOL giants above. -/
theorem gammaX_gamm4fgcy (V X : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3) (i : ℕ)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hi : 4 ≤ i) (hX : X = mcell i V ul) (hn : ¬ nullSet X)
    (hul : ul = [u0, u1, u2, u3]) (hy1 : dist u0 u1 = y1) (hy2 : dist u0 u2 = y2)
    (hy3 : dist u0 u3 = y3) (hy4 : dist u2 u3 = y4) (hy5 : dist u1 u3 = y5)
    (hy6 : dist u1 u2 = y6) :
    volume.real X = volY y1 y2 y3 y4 y5 y6 ∧
      gammaX V X lmfun = gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  subst hul
  have hd := p20k_barV_distinct hb
  have t10 : dist u1 u0 = y1 := by rw [dist_comm]; exact hy1
  have t20 : dist u2 u0 = y2 := by rw [dist_comm]; exact hy2
  have t30 : dist u3 u0 = y3 := by rw [dist_comm]; exact hy3
  have t32 : dist u3 u2 = y4 := by rw [dist_comm]; exact hy4
  have t31 : dist u3 u1 = y5 := by rw [dist_comm]; exact hy5
  have t21 : dist u2 u1 = y6 := by rw [dist_comm]; exact hy6
  have hX4 : X = mcell 4 V [u0, u1, u2, u3] := by rw [hX, p20k_mcell_ge4 hi]
  have hne4 : mcell 4 V [u0, u1, u2, u3] ≠ ∅ := by
    intro h0
    rw [← hX4] at h0
    exact p20k_ne_empty hn h0
  have hVX : VX V X = {u0, u1, u2, u3} := by
    have g1 := p20k_VX_m4 V [u0, u1, u2, u3] hp hs hb
      (fun h0 => by rw [← hX4] at h0; exact hn h0)
    rw [hX4, g1]
    ext z
    simp only [setOfList, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have hset4 : setOfList [u0, u1, u2, u3] = ({u0, u1, u2, u3} : Set V3) := by
    ext z
    simp only [setOfList, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  -- (a) volume half: the SimplexVolume bridge
  have hvol : volume.real X = volY y1 y2 y3 y4 y5 y6 := by
    rw [hX4, p20k_mcell4_hull hne4, hset4, volume_real_convexHull_tetra,
      hy1, hy2, hy3, hy4, hy5, hy6]
    unfold volY volXf
    simp only [pow_two]
  -- (b) sol side: the four vertex solid angles
  obtain ⟨hs0, hs1, hs2, hs3⟩ := SOL_SOL_Y_EXPLICIT V X [u0, u1, u2, u3] u0 u1 u2 u3 i
    y1 y2 y3 y4 y5 y6 hs hp hb hi hX hn rfl hy1 hy2 hy3 hy4 hy5 hy6
  have hts : totalSolid V X = sol u0 X + sol u1 X + sol u2 X + sol u3 X := by
    unfold totalSolid
    rw [hVX]
    exact p20k_setSum_quad _ hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2
  -- (c) the six dihedral slots + the pair-swap equalities
  obtain ⟨hd01, hd02, hd03, hd23, hd13, hd12⟩ :=
    DIHX_DIH_Y_lemma V X [u0, u1, u2, u3] u0 u1 u2 u3 i y1 y2 y3 y4 y5 y6 hs hp hb hi hX
      hn rfl hy1 hy2 hy3 hy4 hy5 hy6
  have sw01 := p20k_dihX_swap V X u0 u1 u2 u3 hp hs hn hb hX4
  -- reordered witnesses (barV + mcell) for the five other swap bases
  obtain ⟨hb02, hm02⟩ := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u0 u2 u1 u3
    (Equiv.symm (Equiv.swap 1 2))
    (show Equiv.symm (Equiv.swap 1 2) 0 = 0 by decide)
    (show Equiv.symm (Equiv.swap 1 2) 1 = 2 by decide)
    (show Equiv.symm (Equiv.swap 1 2) 2 = 1 by decide)
    (show Equiv.symm (Equiv.swap 1 2) 3 = 3 by decide)
    (by norm_num)
    (by
      intro j hj
      rw [Equiv.symm_apply_eq]
      exact (Equiv.swap_apply_of_ne_of_ne (show j ≠ 1 by omega) (show j ≠ 2 by omega)).symm)
    (by
      rw [leftActionList, Equiv.symm_symm]
      simp [List.range_succ, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne])
  have sw02 := p20k_dihX_swap V X u0 u2 u1 u3 hp hs hn hb02 (by rw [hm02]; exact hX4)
  obtain ⟨hb03, hm03⟩ := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u0 u3 u1 u2
    (Equiv.symm ((Equiv.swap 2 3).trans (Equiv.swap 1 3)))
    (show Equiv.symm ((Equiv.swap 2 3).trans (Equiv.swap 1 3)) 0 = 0 by decide)
    (show Equiv.symm ((Equiv.swap 2 3).trans (Equiv.swap 1 3)) 1 = 2 by decide)
    (show Equiv.symm ((Equiv.swap 2 3).trans (Equiv.swap 1 3)) 2 = 3 by decide)
    (show Equiv.symm ((Equiv.swap 2 3).trans (Equiv.swap 1 3)) 3 = 1 by decide)
    (by norm_num)
    (by
      intro j hj
      rw [Equiv.symm_apply_eq, Equiv.trans_apply]
      show j = (Equiv.swap 1 3) ((Equiv.swap 2 3) j)
      rw [Equiv.swap_apply_of_ne_of_ne (show j ≠ 2 by omega) (show j ≠ 3 by omega),
        Equiv.swap_apply_of_ne_of_ne (show j ≠ 1 by omega) (show j ≠ 3 by omega)])
    (by
      rw [leftActionList, Equiv.symm_symm]
      simp [List.range_succ, Equiv.trans_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne])
  have sw03 := p20k_dihX_swap V X u0 u3 u1 u2 hp hs hn hb03 (by rw [hm03]; exact hX4)
  obtain ⟨hb23, hm23⟩ := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u2 u3 u0 u1
    (Equiv.symm ((Equiv.swap 1 3).trans (Equiv.swap 0 2)))
    (show Equiv.symm ((Equiv.swap 1 3).trans (Equiv.swap 0 2)) 0 = 2 by decide)
    (show Equiv.symm ((Equiv.swap 1 3).trans (Equiv.swap 0 2)) 1 = 3 by decide)
    (show Equiv.symm ((Equiv.swap 1 3).trans (Equiv.swap 0 2)) 2 = 0 by decide)
    (show Equiv.symm ((Equiv.swap 1 3).trans (Equiv.swap 0 2)) 3 = 1 by decide)
    (by norm_num)
    (by
      intro j hj
      rw [Equiv.symm_apply_eq, Equiv.trans_apply]
      show j = (Equiv.swap 0 2) ((Equiv.swap 1 3) j)
      rw [Equiv.swap_apply_of_ne_of_ne (show j ≠ 1 by omega) (show j ≠ 3 by omega),
        Equiv.swap_apply_of_ne_of_ne (show j ≠ 0 by omega) (show j ≠ 2 by omega)])
    (by
      rw [leftActionList, Equiv.symm_symm]
      simp [List.range_succ, Equiv.trans_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne])
  have sw23 := p20k_dihX_swap V X u2 u3 u0 u1 hp hs hn hb23 (by rw [hm23]; exact hX4)
  obtain ⟨hb13, hm13⟩ := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u1 u3 u0 u2
    (Equiv.symm ((Equiv.swap 0 2).trans ((Equiv.swap 1 3).trans (Equiv.swap 1 2))))
    (show Equiv.symm ((Equiv.swap 0 2).trans ((Equiv.swap 1 3).trans (Equiv.swap 1 2))) 0 = 2 by decide)
    (show Equiv.symm ((Equiv.swap 0 2).trans ((Equiv.swap 1 3).trans (Equiv.swap 1 2))) 1 = 0 by decide)
    (show Equiv.symm ((Equiv.swap 0 2).trans ((Equiv.swap 1 3).trans (Equiv.swap 1 2))) 2 = 3 by decide)
    (show Equiv.symm ((Equiv.swap 0 2).trans ((Equiv.swap 1 3).trans (Equiv.swap 1 2))) 3 = 1 by decide)
    (by norm_num)
    (by
      intro j hj
      rw [Equiv.symm_apply_eq]
      simp only [Equiv.trans_apply]
      show j = (Equiv.swap 1 2) ((Equiv.swap 1 3) ((Equiv.swap 0 2) j))
      rw [Equiv.swap_apply_of_ne_of_ne (show j ≠ 0 by omega) (show j ≠ 2 by omega),
        Equiv.swap_apply_of_ne_of_ne (show j ≠ 1 by omega) (show j ≠ 3 by omega),
        Equiv.swap_apply_of_ne_of_ne (show j ≠ 1 by omega) (show j ≠ 2 by omega)])
    (by
      rw [leftActionList, Equiv.symm_symm]
      simp [List.range_succ, Equiv.trans_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne])
  have sw13 := p20k_dihX_swap V X u1 u3 u0 u2 hp hs hn hb13 (by rw [hm13]; exact hX4)
  obtain ⟨hb12, hm12⟩ := p20k_perm_wit V u0 u1 u2 u3 hs hp hb hne4 u1 u2 u0 u3
    (Equiv.symm ((Equiv.swap 1 2).trans (Equiv.swap 0 1)))
    (show Equiv.symm ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) 0 = 2 by decide)
    (show Equiv.symm ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) 1 = 0 by decide)
    (show Equiv.symm ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) 2 = 1 by decide)
    (show Equiv.symm ((Equiv.swap 1 2).trans (Equiv.swap 0 1)) 3 = 3 by decide)
    (by norm_num)
    (by
      intro j hj
      rw [Equiv.symm_apply_eq, Equiv.trans_apply]
      show j = (Equiv.swap 0 1) ((Equiv.swap 1 2) j)
      rw [Equiv.swap_apply_of_ne_of_ne (show j ≠ 1 by omega) (show j ≠ 2 by omega),
        Equiv.swap_apply_of_ne_of_ne (show j ≠ 0 by omega) (show j ≠ 1 by omega)])
    (by
      rw [leftActionList, Equiv.symm_symm]
      simp [List.range_succ, Equiv.trans_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne])
  have sw12 := p20k_dihX_swap V X u1 u2 u0 u3 hp hs hn hb12 (by rw [hm12]; exact hX4)
  -- (d) edgeX is the six-pair set (vol4f slot order)
  have pEq : ∀ (p q : V3), ({p, q} : Set V3) = {q, p} := by
    intro p q
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hedges : edgeX V X =
      insert ({u0, u1} : Set V3) (insert ({u0, u2} : Set V3) (insert ({u0, u3} : Set V3)
        (insert ({u2, u3} : Set V3) (insert ({u1, u3} : Set V3)
          (insert ({u1, u2} : Set V3) (∅ : Set (Set V3))))))) := by
    ext e
    simp only [edgeX, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b, rfl, ha, hbv, hab⟩
      have ha4 : a ∈ ({u0, u1, u2, u3} : Set V3) := by
        have h1 : a ∈ VX V X := ha
        rw [hVX] at h1
        exact h1
      have hb4 : b ∈ ({u0, u1, u2, u3} : Set V3) := by
        have h1 : b ∈ VX V X := hbv
        rw [hVX] at h1
        exact h1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha4 hb4
      rcases ha4 with ha4 | ha4 | ha4 | ha4 <;>
        rcases hb4 with hb4 | hb4 | hb4 | hb4
      · exact absurd (ha4.trans hb4.symm) hab
      · exact Or.inl (by rw [ha4, hb4])
      · exact Or.inr (Or.inl (by rw [ha4, hb4]))
      · exact Or.inr (Or.inr (Or.inl (by rw [ha4, hb4])))
      · exact Or.inl (by rw [ha4, hb4]; exact (pEq u0 u1).symm)
      · exact absurd (ha4.trans hb4.symm) hab
      · rw [ha4, hb4]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Set.mem_insert _ _)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [ha4, hb4])))))
      · exact Or.inr (Or.inl (by rw [ha4, hb4]; exact (pEq u0 u2).symm))
      · rw [ha4, hb4]
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
        exact Set.mem_insert_iff.mpr (Or.inl (pEq u2 u1))
      · exact absurd (ha4.trans hb4.symm) hab
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [ha4, hb4]))))
      · exact Or.inr (Or.inr (Or.inl (by rw [ha4, hb4]; exact (pEq u0 u3).symm)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [ha4, hb4]; exact (pEq u1 u3).symm)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [ha4, hb4]; exact (pEq u2 u3).symm))))
      · exact absurd (ha4.trans hb4.symm) hab
    · rintro (rfl | rfl | rfl | rfl | rfl | h6)
      · exact ⟨u0, u1, rfl, by rw [hVX]; simp, by rw [hVX]; simp, hd.1⟩
      · exact ⟨u0, u2, rfl, by rw [hVX]; simp, by rw [hVX]; simp, hd.2.1⟩
      · exact ⟨u0, u3, rfl, by rw [hVX]; simp, by rw [hVX]; simp, hd.2.2.1⟩
      · exact ⟨u2, u3, rfl, by rw [hVX]; simp, by rw [hVX]; simp, hd.2.2.2.2.2⟩
      · exact ⟨u1, u3, rfl, by rw [hVX]; simp, by rw [hVX]; simp, hd.2.2.2.2.1⟩
      · rw [Set.mem_insert_iff] at h6
        rcases h6 with h6 | h6
        · subst h6
          exact ⟨u1, u2, rfl, by rw [hVX]; simp, by rw [hVX]; simp, hd.2.2.2.1⟩
        · exact absurd h6 (by simp)
  -- the 15 pair distinctness facts for the sum expansion
  have d1 : ({u0, u1} : Set V3) ≠ {u0, u2} := p20k_pair_ne_sh1 hd.1 hd.2.1 hd.2.2.2.1
  have d2 : ({u0, u1} : Set V3) ≠ {u0, u3} := p20k_pair_ne_sh1 hd.1 hd.2.2.1 hd.2.2.2.2.1
  have d3 : ({u0, u1} : Set V3) ≠ {u2, u3} := p20k_pair_ne_gen hd.1 hd.2.1 hd.2.2.1
  have d4 : ({u0, u1} : Set V3) ≠ {u1, u3} := p20k_pair_ne_gen hd.1 hd.1 hd.2.2.1
  have d5 : ({u0, u1} : Set V3) ≠ {u1, u2} := p20k_pair_ne_gen hd.1 hd.1 hd.2.1
  have d6 : ({u0, u2} : Set V3) ≠ {u0, u3} := p20k_pair_ne_sh1 hd.2.1 hd.2.2.1 hd.2.2.2.2.2
  have d7 : ({u0, u2} : Set V3) ≠ {u2, u3} := p20k_pair_ne_gen hd.2.1 hd.2.1 hd.2.2.1
  have d8 : ({u0, u2} : Set V3) ≠ {u1, u3} := p20k_pair_ne_gen hd.2.1 hd.1 hd.2.2.1
  have d9 : ({u0, u2} : Set V3) ≠ {u1, u2} := p20k_pair_ne_gen hd.2.1 hd.1 hd.2.1
  have d10 : ({u0, u3} : Set V3) ≠ {u2, u3} := p20k_pair_ne_gen hd.2.2.1 hd.2.1 hd.2.2.1
  have d11 : ({u0, u3} : Set V3) ≠ {u1, u3} := p20k_pair_ne_gen hd.2.2.1 hd.1 hd.2.2.1
  have d12 : ({u0, u3} : Set V3) ≠ {u1, u2} := p20k_pair_ne_gen hd.2.2.1 hd.1 hd.2.1
  have d13 : ({u2, u3} : Set V3) ≠ {u1, u3} :=
    p20k_pair_ne_gen hd.2.2.2.2.2 (Ne.symm hd.2.2.2.1) hd.2.2.2.2.2
  have d14 : ({u2, u3} : Set V3) ≠ {u1, u2} :=
    p20k_pair_ne_gen2 hd.2.2.2.2.2 (Ne.symm hd.2.2.2.2.1) (Ne.symm hd.2.2.2.2.2)
  have d15 : ({u1, u3} : Set V3) ≠ {u1, u2} :=
    p20k_pair_ne_sh1 hd.2.2.2.2.1 hd.2.2.2.1 (Ne.symm hd.2.2.2.2.2)
  refine ⟨hvol, ?_⟩
  unfold gammaX gamma4fgcy vol4f
  rw [hvol, hts, hs0, hs1, hs2, hs3, hedges]
  unfold setSum
  rw [dif_pos (Set.toFinite (insert ({u0, u1} : Set V3) (insert ({u0, u2} : Set V3)
    (insert ({u0, u3} : Set V3) (insert ({u2, u3} : Set V3) (insert ({u1, u3} : Set V3)
      (insert ({u1, u2} : Set V3) (∅ : Set (Set V3)))))))))]
  simp only [Set.Finite.toFinset_insert, Set.Finite.toFinset_singleton]
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    Set.mem_insert_iff, Set.mem_singleton_iff, Finset.sum_insert]
  rw [p20k_edge_term_eps hd.1 lmfun sw01,
    p20k_edge_term_eps hd.2.1 lmfun sw02,
    p20k_edge_term_eps hd.2.2.1 lmfun sw03,
    p20k_edge_term_eps hd.2.2.2.2.2 lmfun sw23,
    p20k_edge_term_eps hd.2.2.2.2.1 lmfun sw13,
    p20k_edge_term_eps hd.2.2.2.1 lmfun sw12]
  rw [hd01, hd02, hd03, hd23, hd13, hd12]
  simp only [HL_2]
  rw [hy1, hy2, hy3, hy4, hy5, hy6]
  ring


/-- HOL `gammaX_gamma3f` (TSKAJXY1.hl:4178): same for a 3-cell: all
`sqrt2`-legs `y1 y2 y3` collapsed to `sqrt2`.

STILL SORRY (2026-10-08 收窄更新): the two gaps of the k = 4 sibling
gammaX_gamm4fgcy are now CLOSED — (a) the tetra-volume bridge exists
(Kepler.Geom.SimplexVolume.volume_real_convexHull_tetra, consumed by the
sibling) and (b) the edgeX six-pair epsilon sum is kitted
(p20k_dihX_swap + p20k_edge_term_eps, consumed by the sibling). What
remains here is the k = 3 apex-form dispatch: pin X = mcell 3 V ul as
convexHull {mxi V ul, u0, u1, u2} with the √2 distances of the apex (the
voronoi-sandwich of MXI_EXPLICIT + voronoiClosed, per the HL proof) and
VX V X = {u0, u1, u2} (LEPJBDJ at k = 3); after that the volume rewrites
via volume_real_convexHull_tetra, the sol/dihX slots reduce to the
permuted distances (√2,√2,√2,y4,y5,y6) through the same kit, and the
gammaX sum collapses exactly as in the sibling. -/
theorem gammaX_gamma3f (V X : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3)
    (y4 y5 y6 : ℝ) (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hX : X = mcell 3 V ul) (hn : ¬ nullSet X) (hul : ul = [u0, u1, u2, u3])
    (hy4 : dist u1 u2 = y4) (hy5 : dist u0 u2 = y5) (hy6 : dist u0 u1 = y6) :
    volume.real X = volY (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6 ∧
      sol u0 X = solY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 ∧
      sol u1 X = solY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5 ∧
      sol u2 X = solY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 ∧
      dihX V X (u0, u1) = dihY y6 y4 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y5 ∧
      dihX V X (u0, u2) = dihY y5 y6 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 ∧
      dihX V X (u1, u2) = dihY y4 y5 (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y6 ∧
      gammaX V X lmfun = gamma3f y4 y5 y6 (Real.sqrt 2) lmfun := by
  sorry
  -- NEEDS: same `cell_params_d` uniqueness (k = 3 instance) as above;
  -- blocked by the PA21 cycle for the kit.

/-- HOL `HJKDESR1a_1cell` (TSKAJXY1.hl:5652): numeric seed of the chain.

PROVED (2026-10-08): the docstring's cos-Taylor route is avoidable —
sin(1/3) < 1/3 gives arccos(1/3) ≤ π/2 - 1/3, hence sol0 ≤ π/2 - 1; with
Mathlib's certified π bounds (3.14 < π < 3.15) the chain 4π² >
(20π+6)·sol0 reduces to the everywhere-negative quadratic 6π² - 17π - 6. -/
theorem HJKDESR1a_1cell : 0 < 8 * Real.pi * Real.sqrt 2 / 3 - 8 * mm1 := by

  have hpi1 : (3.14:ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  have ha : Real.arccos (1 / 3) ≤ Real.pi / 2 - 1 / 3 := by
    have hsin : Real.sin (1 / 3) ≤ 1 / 3 := le_of_lt (Real.sin_lt (by norm_num))
    have hcw : Real.cos (Real.pi / 2 - 1 / 3) = Real.sin (1 / 3) :=
      Real.cos_pi_div_two_sub (1 / 3)
    have hstep : Real.arccos (1 / 3)
        ≤ Real.arccos (Real.cos (Real.pi / 2 - 1 / 3)) :=
      Real.arccos_le_arccos (hcw.trans_le hsin)
    rw [Real.arccos_cos (by linarith) (by linarith)] at hstep
    exact hstep
  have hsol : sol0 ≤ Real.pi / 2 - 1 := by
    have h0 : sol0 = 3 * Real.arccos (1 / 3) - Real.pi := rfl
    linarith
  have htau : 0 < tau0 := by
    have h0 : tau0 = 4 * Real.pi - 20 * sol0 := rfl
    linarith
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8:ℝ) = 4 * 2 from by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  have key : 0 < Real.pi * tau0 - 6 * sol0 := by
    have h1 : Real.pi * tau0 - 6 * sol0
        = 4 * Real.pi ^ 2 - (20 * Real.pi + 6) * sol0 := by
      have h0 : tau0 = 4 * Real.pi - 20 * sol0 := rfl
      rw [h0]
      ring
    rw [h1]
    have hpos : (0:ℝ) ≤ 20 * Real.pi + 6 := by positivity
    have h2 : (4:ℝ) * Real.pi ^ 2
        > (20 * Real.pi + 6) * (Real.pi / 2 - 1) := by
      have hq : (6:ℝ) * Real.pi ^ 2 - 17 * Real.pi - 6 < 0 := by
        nlinarith [hpi2, hpi1]
      linarith
    have h3 : (20 * Real.pi + 6) * (Real.pi / 2 - 1)
        ≥ (20 * Real.pi + 6) * sol0 := mul_le_mul_of_nonneg_left hsol hpos
    linarith
  have hmm1 : mm1 = sol0 * Real.sqrt 8 / tau0 := rfl
  rw [hmm1, h8]
  have e1 : 8 * Real.pi * Real.sqrt 2 / 3
      - 8 * (sol0 * (2 * Real.sqrt 2) / tau0)
      = 8 * Real.sqrt 2 / (3 * tau0) * (Real.pi * tau0 - 6 * sol0) := by
    field_simp
    ring
  rw [e1]
  refine mul_pos ?_ key
  positivity

/-! ## Support-lemma bank (generic forms of the hub's ~206 inlined
SET_RULE facts; private + proved) -/

private theorem p20_memPair {α : Type*} {x a b : α} :
    x ∈ ({a, b} : Set α) ↔ x = a ∨ x = b := by
  simp

private theorem p20_memTriple {α : Type*} {x a b c : α} :
    x ∈ ({a, b, c} : Set α) ↔ x = a ∨ x = b ∨ x = c := by
  simp

private theorem p20_memQuadruple {α : Type*} {x a b c d : α} :
    x ∈ ({a, b, c, d} : Set α) ↔ x = a ∨ x = b ∨ x = c ∨ x = d := by
  simp

private theorem p20_memQuintuple {α : Type*} {x a b c d e : α} :
    x ∈ ({a, b, c, d, e} : Set α) ↔ x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  simp

private theorem p20_memSextuple {α : Type*} {x a b c d e f : α} :
    x ∈ ({a, b, c, d, e, f} : Set α) ↔
      x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
  simp

private theorem p20_four_in_nats : (4 : ℕ) ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by simp

private theorem p20_three_in_nats : (3 : ℕ) ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by simp

private theorem p20_three_in_twothree : (3 : ℕ) ∈ ({2, 3} : Set ℕ) := by simp

private theorem p20_pair_comm {α : Type*} (a b : α) : ({a, b} : Set α) = {b, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup12 {α : Type*} (a b c : α) :
    ({a, a, b, c} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup13 {α : Type*} (a b c : α) :
    ({a, b, a, c} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup14 {α : Type*} (a b c : α) :
    ({a, b, c, a} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup23 {α : Type*} (a b c : α) :
    ({a, b, b, c} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup24 {α : Type*} (a b c : α) :
    ({a, b, c, b} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_dedup34 {α : Type*} (a b c : α) :
    ({a, b, c, c} : Set α) = {a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap12 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {b, a, c, d} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap13 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {c, b, a, d} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap14 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {d, b, c, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap23 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {a, c, b, d} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap24 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {a, d, c, b} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_swap34 {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {a, b, d, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_rot {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {b, c, d, a} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_perm4_rotBack {α : Type*} (a b c d : α) :
    ({a, b, c, d} : Set α) = {d, a, b, c} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_union_single {α : Type*} (a b c d : α) :
    ({a, b, c} : Set α) ∪ {d} = ({a, b, c, d} : Set α) := by
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem p20_member_subset {α : Type*} {a : α} {t : Set α}
    (h : ∃ s : Set α, a ∈ s ∧ s ⊆ t) : a ∈ t := by
  obtain ⟨s, ha, hst⟩ := h
  exact hst ha

private theorem p20_subset_antisymm {α : Type*} {A B : Set α} (h1 : A ⊆ B)
    (h2 : B ⊆ A) : A = B := Subset.antisymm h1 h2

private theorem p20_inter_subset_right {α : Type*} (a s : Set α) :
    a ∩ s ⊆ s := Set.inter_subset_right

private theorem p20_inter_subset_inter_left {α : Type*} {s t : Set α} (c : Set α)
    (h : s ⊆ t) : s ∩ c ⊆ t ∩ c := Set.inter_subset_inter_left c h

private theorem p20_inter_distrib_left {α : Type*} (a b c : Set α) :
    a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := Set.inter_union_distrib_left a b c

private theorem p20_inter_comm {α : Type*} (a b : Set α) : a ∩ b = b ∩ a :=
  Set.inter_comm a b

private theorem p20_disjoint_sing_triple (v0 v1 v2 v3 : V3) :
    ({v0} : Set V3) ∩ {v1, v2, v3} = ∅ ↔
      ¬(v0 = v1 ∨ v0 = v2 ∨ v0 = v3) := by
  constructor
  · intro h heq
    have hm : v0 ∈ ({v0} : Set V3) ∩ {v1, v2, v3} := by
      rcases heq with heq | heq | heq <;>
        exact Set.mem_inter (by simp) (by rw [heq]; simp)
    rw [h] at hm
    exact absurd hm (by simp)
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hx0, hx2⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx2
    exact h (hx0 ▸ hx2)

private theorem p20_quad_subset (V : Set V3) (u0 u1 u2 u3 : V3) :
    u0 ∈ V ∧ u1 ∈ V ∧ u2 ∈ V ∧ u3 ∈ V ↔ ({u0, u1, u2, u3} : Set V3) ⊆ V := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ x hx
    rcases p20_memQuadruple.mp hx with rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro h
    exact ⟨h (by simp), h (by simp), h (by simp), h (by simp)⟩
