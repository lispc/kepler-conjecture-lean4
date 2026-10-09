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
import Kepler.Text.PackingAuto17
import Kepler.Text.SphereKit
import Kepler.Text.Polytope
import Kepler.Text.PlanarityAuto12
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

`SOL_SOLID_TRIANGLE` is FULLY PROVED below (2026-10-08). The other five
remain giant `prove_by_refinement` bodies with `sorry`: the HOL bodies
inline ~206 SET_RULE facts + geometric heavy machinery (SOLID_J_,
MCELL_EXPLICIT, Flyspeck_constants.bounds, and for the four mcell-reduction
giants the `cell_params_d` uniqueness kit, which lives in PackingAuto21 --
unimportable here, PA21 imports this file); the statements are the chain
interface. -/

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

/-- HOL `DIHX_DIH_Y_lemma` (TSKAJXY1.hl:567): the six dihedral angles of
a saturated-packing 4-cell are the `dih_y` values of the edge-length
six-tuple (per the per-edge argument permutation). -/
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
  sorry
  -- NEEDS: cell_params_d uniqueness for `mcell4` (HL MCELLparam kit). The
  -- kit (MCELL_PARAM_D_UL/AJRIPQN) lives in PackingAuto17/21; PA21 imports
  -- this file, so the kit is unreachable here (cycle). Remaining: port the
  -- uniqueness argument (or its k=4 instance) locally, then dispatch
  -- `dihX` through `dihu4 ul` and match with the analytic `dih_y` formula.

/-- HOL `SOL_SOL_Y_EXPLICIT` (TSKAJXY1.hl:2995): the four vertex solid
angles of a 4-cell are the `sol_y` values of the edge six-tuple. -/
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
  sorry
  -- NEEDS: same `cell_params_d` uniqueness gap as DIHX_DIH_Y_lemma above,
  -- plus `SOL_SOLID_TRIANGLE`-style vertex dispatch of `sol` (this file,
  -- proved above) at the four vertices; blocked by the PA21 cycle.

/-- HOL `gammaX_gamm4fgcy` (TSKAJXY1.hl:3508): volume and `gammaX` of a
4-cell are the analytic `vol_y` / `gamma4fgcy` of the edge six-tuple. -/
theorem gammaX_gamm4fgcy (V X : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3) (i : ℕ)
    (y1 y2 y3 y4 y5 y6 : ℝ) (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hi : 4 ≤ i) (hX : X = mcell i V ul) (hn : ¬ nullSet X)
    (hul : ul = [u0, u1, u2, u3]) (hy1 : dist u0 u1 = y1) (hy2 : dist u0 u2 = y2)
    (hy3 : dist u0 u3 = y3) (hy4 : dist u2 u3 = y4) (hy5 : dist u1 u3 = y5)
    (hy6 : dist u1 u2 = y6) :
    volume.real X = volY y1 y2 y3 y4 y5 y6 ∧
      gammaX V X lmfun = gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  sorry
  -- NEEDS: `cell_params_d` uniqueness (as above) to unfold gammaX's VX /
  -- edgeX bank through the explicit 4-cell vertices, then the volume and
  -- gamma definitions rewrite via volY/gamma4fgcy. Blocked by the PA21
  -- cycle for the kit.

/-- HOL `gammaX_gamma3f` (TSKAJXY1.hl:4178): same for a 3-cell: all
`sqrt2`-legs `y1 y2 y3` collapsed to `sqrt2`. -/
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

/-- HOL `HJKDESR1a_1cell` (TSKAJXY1.hl:5652): numeric seed of the chain
(proof route: `3 * mm1 < 3 * 1.3 < pi * sqrt 2` via certified bounds of
`Flyspeck_constants.bounds`, not re-derivable without interval tactics). -/
theorem HJKDESR1a_1cell : 0 < 8 * Real.pi * Real.sqrt 2 / 3 - 8 * mm1 := by
  sorry
  -- NEEDS: certified numeric bounds. Unfolds to 4 * pi^2 > sol0 * (20 * pi + 6)
  -- (sol0 = 3 * arccos(1/3) - pi, mm1 = sol0 * sqrt 8 / tau0, tau0 = 4*pi - 20*sol0,
  -- all definitions in PackingAuto2). Sufficient inputs: pi > 157/50 and
  -- pi < 22/7 (both in Mathlib) plus arccos(1/3) < 1.234 -- the last needs a
  -- one-sided cos Taylor bound at 617/500 (Mathlib has no cos partial-sum
  -- bounds); sol0Bounds_p19 (LocalAuto19) is itself sorry. Route mapped
  -- 2026-10-08; not filled (out of budget).

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

/-! ## cell_params_d uniqueness kit (moved from PackingAuto21) -/

/-- HOL `MCELL_CELL_PARAMETERS_D_EXIST` (TSKAJXY3.hl:841; proved 2026-09-29
wave B1: the `cellParamsD` epsilon satisfies its predicate (`epsilon_spec`
with the witness `(k, ul)`), and `AJRIPQN` (PA17, sorry-tainted upstream)
identifies its first component with `k`). -/
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

/-- HOL `MCELL_PARAM_D_UL` (TSKAJXY3.hl:897; proved 2026-09-29 wave B1:
`cellParamsD V X ul'`'s epsilon satisfies its predicate, and `AJRIPQN`
(PA17, sorry-tainted upstream) transfers the parameters). -/
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
