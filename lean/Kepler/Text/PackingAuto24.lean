/-
PackingAuto24: port of `scripts/packing/REUHADY.hl` (Flyspeck chapter
"packing / Marchal cells", Vu Khac Ky, 8357 lines; 1 def + 11 theorems,
headlined by the measure-splitting/annulus book lemma `REUHADY1`).

FILE MAP (how this feeds the final Kepler count)
  The chapter establishes that, along a short edge `u0u1` of a saturated
  packing, the Marchal cells lying inside the closed azimuth wedge
  `wedge_ge u0 u1 n1 n2` have total dihedral angle exactly
  `azim u0 u1 n1 n2` (`REUHADY1`, the 8100-line giant refinement proof).
  Supporting kit: Harrison wedge lemmas (`WEDGE_SIMPLE`,
  `WEDGE_GE_WEDGE`: closed wedge = open wedge + the two azimuth level
  sets), Harrison `Arg`/halfline lemmas (`ARG_EQ_SUBSET_HALFLINE`,
  `ARG_DIV_EQ_SUBSET_HALFLINE`), the coplanarity of azimuth level sets
  (`COPLANAR_AZIM_EQ`), and the measure facts
  `MEASURABLE_CONIC_CAP_WEDGE_GE` /
  `VOLUME_CONIC_CAP_WEDGE_GE_VS_CONIC_CAP` (wedge proportionality of
  conic-cap volume) that downstream annulus estimates consume.
  Downstream in HL, OXLZLEZ3.hl instantiates `REUHADY1` on leaf cells
  (its `REUHADY`); the pack_concl conclusions `REUHADY_concl` /
  `REUHADY_concl_version2` (already stated in PackingAuto2) are
  discharged from `REUHADY1` only with the extra leaf-cell wedge
  disjointness input (HL `Leaf_cell.WEDGE_GE_ALMOST_DISJOINT`), so the
  capstones here are stated statement-identically to PackingAuto2 for
  merge-time discharge and remain `sorry` pending that input.

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `packing` <-> `Packing`;
    `saturated` <-> `PackingAuto2.saturated`; `hl`, `barV`,
    `truncate_simplex`, `set_of_list`, `EL 2`, `mcell_set`, `edgeX`,
    `dihX`, `sum` over sets, `aff_ge`, `wedge_ge` <-> the PackingAuto2
    definitions `hl`, `barV`, `truncateSimplex`, `setOfList`, `elV`,
    `mcellSet`, `edgeX`, `setSum`, `affGe`, `wedgeGe` (imported;
    `wedge_ge` is NOT redefined here).
  - HOL `wedge` (open wedge) <-> `Kepler.Text.wedge` (PackingAuto15 /
    Kepler.Geom.Azim); `conic_cap` <-> `conicCap` (PackingAuto15);
    `collinear{...}` <-> `Collinear3`; `coplanar` <-> `Coplanar ℝ`.
  - HOL `real^2` content (the `Arg` halfline lemmas, planar rays) <->
    `ℂ`: `Complex.arg` is native; the closed halfline `aff_ge {vec 0}
    {b}` is the closed ray `{z : ℂ | ∃ t ≥ 0, z = t • b}` (real-scalar
    smul), matching PackingAuto22's real^2-↔-ℂ precedent.
  - `measurable s` <-> `MeasurableSet s` for Lebesgue `volume`
    (PackingAuto10 style); HOL `vol` <-> `volume.real` (real-valued
    Lebesgue measure, `MeasureTheory.Measure.real` under
    `open MeasureTheory`).

SORRY INVENTORY (giants, with blockers)
  - `REUHADY1`: the 8100-line `prove_by_refinement` giant (HL lines
    239-8356); consumes Rogers/Marchal_cells_2_new/Packing3/Pack2
    voronoi machinery far beyond this lane's budget.
  - `coplanarAzimEq`: docstring carries the full Lean-side construction
    route (frame + `azim_eq_azim_iff` + coplanarity plumbing).
  - `measurableConicCapWedgeGe`: Borel-ness of azimuth level sets /
    the open wedge; the ℂ-transport route through WedgeVolume's `ang`
    machinery is documented in its docstring.
  - `volumeConicCapWedgeGeVsConicCap`: NEEDS `VOLUME_CONIC_CAP` /
    `VOLUME_CONIC_CAP_WEDGE` (flyspeck_multivariate.ml measure content,
    not yet ported in any lane) + `MEASURE_NEGLIGIBLE_SYMDIFF`.
  - `REUHADY_p24` / `REUHADY_version2_p24`: need `REUHADY1` plus the
    leaf-cell wedge-disjointness extraction (`WEDGE_GE_ALMOST_DISJOINT`
    / `FCHKUGT` / `EWYBJUA`, OXLZLEZ3.hl) and barV/pair half-length
    (`HL_2`) extraction to synthesize `REUHADY1`'s stronger hypotheses.
  - `GRUTOTI1_concl_p24`: statement copy of the parallel-owned Auto23
    chapter (GRUTOTI.hl:48-58; proof NOT importable — Auto23 lane).
    NEEDS marker only; delete at merge into Auto23's results.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.Polytope
import Kepler.Geom.Azim
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## `_p24` definition copies (Kepler.Text.PackingAuto15 has no built
olean in this checkout, so the chapter keeps a private copy; delete at
merge into the PackingAuto15 lane) -/

/-- HOL `conic_cap` (flyspeck_multivariate.ml:4832; PackingAuto15:109
copy): `conic_cap v0 v1 r a = normball v0 r INTER rcone_gt v0 v1 a`.
The HOL open `wedge` needs no copy: `Kepler.Geom.wedge` (Azim.lean:63)
is definitionally the PackingAuto15:113 `wedge`. -/
def conicCapP24 (v0 v1 : V3) (r a : ℝ) : Set V3 :=
  Metric.closedBall v0 r ∩ rconeGt v0 v1 a

/-! ## Private glue lemmas (azim degeneracy, list kit) -/

/-- HOL `AZIM_DEGENERATE` (flyspeck.ml, `azim_def` if-branch):
degenerate frames carry zero azimuth. -/
private theorem azim_eq_zero_of_collinearY (v0 v1 w y : V3) (h : Collinear3 v0 v1 y) :
    azim v0 v1 w y = 0 := by
  unfold azim
  exact if_pos (Or.inr h)

/-- HOL `UNIV_GSPEC` (REUHADY.hl:157). -/
theorem univGspec : {x : V3 | True} = (Set.univ : Set V3) := by
  rfl

/-- HOL `WEDGE_SIMPLE` (REUHADY.hl:68): the open wedge is the strict
azimuth interval (the `¬Collinear3` guard is implied by `0 < azim`). -/
theorem wedgeSimple (v0 v1 w1 w2 : V3) :
    wedge v0 v1 w1 w2 =
      {y | 0 < azim v0 v1 w1 y ∧ azim v0 v1 w1 y < azim v0 v1 w1 w2} := by
  ext y
  simp only [wedge, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    intro hc
    rw [azim_eq_zero_of_collinearY v0 v1 w1 y hc] at h1
    exact absurd h1 (by linarith)

/-- HOL `WEDGE_GE_WEDGE` (REUHADY.hl:77): the closed wedge is the open
wedge together with its two boundary azimuth level sets. (Union
parenthesization made explicit; `∪` associates in HOL.) -/
theorem wedgeGeWedge (v0 v1 w1 w2 : V3) :
    wedgeGe v0 v1 w1 w2 =
      wedge v0 v1 w1 w2 ∪ ({z | azim v0 v1 w1 z = 0} ∪
        {z | azim v0 v1 w1 z = azim v0 v1 w1 w2}) := by
  ext z
  have hb := azim_nonneg v0 v1 w1 w2
  simp only [wedgeGe, wedgeSimple, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨hle1, hle2⟩
    by_cases h0 : azim v0 v1 w1 z = 0
    · exact Or.inr (Or.inl h0)
    · rcases lt_or_eq_of_le hle2 with hlt | heq
      · exact Or.inl ⟨lt_of_le_of_ne hle1 (Ne.symm h0), hlt⟩
      · exact Or.inr (Or.inr heq)
  · rintro (h | h | h)
    · obtain ⟨hlt, hle2⟩ := h
      exact ⟨by linarith, hle2.le⟩
    · exact ⟨h.symm.le, by rw [h]; exact hb⟩
    · exact ⟨h ▸ hb, h.le⟩

/-- HOL `BARV_2_IMP_NOT_COLLINEAR_SET_OF_LIST` (REUHADY.hl:54): the
vertex set of a `barV V 2` simplex is not collinear. -/
theorem barV2_imp_not_collinear_setOfList (V : Set V3) (ul : List V3)
    (hP : Packing V) (hbar : barV V 2 ul) :
    ¬ Collinear ℝ (setOfList ul) := by
  intro hcol
  have hne : (setOfList ul) ≠ ∅ := by
    rintro hrfl
    have h1 : affDim (setOfList ul) = 2 := MHFTTZN1 V ul 2 hP hbar
    rw [affDim] at h1
    simp [hrfl] at h1
  have hd : affDim (setOfList ul) = 2 := MHFTTZN1 V ul 2 hP hbar
  rw [affDim, if_neg hne] at hd
  have hrank : Module.finrank ℝ (vectorSpan ℝ (setOfList ul)) ≤ 1 :=
    Collinear.finrank_le_one hcol
  exact absurd (by omega : (2 : ℤ) ≤ 1) (by norm_num)

/-! ## The REUHADY statement (REUHADY.hl:207 `REUHADY_concl1_new`) -/

/-- HOL `REUHADY_concl1_new` (REUHADY.hl:207-237): the Marchal cells in
the wedge `wedge_ge u0 u1 n1 n2` contribute total dihedral angle
`azim u0 u1 n1 n2` along the edge `u0u1`. -/
def REUHADY_concl1_new : Prop :=
  ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3) (n1 n2 : V3) (e : Set V3),
    saturated V →
    Packing V →
    u0 ∈ V →
    u1 ∈ V →
    u0 ≠ u1 →
    hl [u0, u1] < Real.sqrt 2 →
    e = {u0, u1} →
    wedgeGe u0 u1 n1 n2 ∩ wedgeGe u0 u1 n2 n1 ⊆
      affGe {u0, u1} {n1} ∪ affGe {u0, u1} {n2} →
    azim u0 u1 n1 n2 ≠ 0 →
    vl1 ≠ vl2 →
    hl vl1 < Real.sqrt 2 →
    hl vl2 < Real.sqrt 2 →
    barV V 2 vl1 →
    barV V 2 vl2 →
    setOfList (truncateSimplex 1 vl1) = e →
    setOfList (truncateSimplex 1 vl2) = e →
    n1 = elV vl1 2 →
    n2 = elV vl2 2 →
    (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 n1 n2 ∨ X ⊆ wedgeGe u0 u1 n2 n1) →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
      X ⊆ wedgeGe u0 u1 n1 n2} (fun t => dihX V t (u0, u1)) =
      azim u0 u1 n1 n2

/-- HOL `REUHADY1` (REUHADY.hl:239, refinement proof over lines
239-8356). GIANT — `sorry`. NEEDS: the Rogers/Marchal-cells/Packing3
voronoi machinery cited in the HL refinement tree. -/
theorem REUHADY1 : REUHADY_concl1_new := by
  sorry

/-! ## Harrison's `Arg` halfline lemmas (REUHADY.hl:88, :110)

HOL states these over `real^2` (complex identified); encoded over `ℂ`
(PackingAuto22 precedent). HOL `aff_ge {vec 0} {b}` (a closed halfline
from the origin through `b`) is encoded as the closed ray
`{z : ℂ | ∃ t ≥ 0, z = (t : ℂ) * b}`. -/

/-- HOL `ARG_EQ_SUBSET_HALFLINE` (REUHADY.hl:88). -/
theorem argEqSubsetHalfline : ∀ a : ℝ, ∃ b : ℂ, b ≠ 0 ∧
    {z : ℂ | Complex.arg z = a} ⊆ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = (t : ℂ) * b} := by
  intro a
  by_cases hsub : {z : ℂ | Complex.arg z = a} ⊆ {0}
  · refine ⟨1, one_ne_zero, fun z hz => ?_⟩
    have hz0 : z = 0 := hsub hz
    exact ⟨0, le_refl 0, by simp [hz0]⟩
  · obtain ⟨z, hz, hz0⟩ := Set.not_subset.mp hsub
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_singleton_iff] at hz0
    refine ⟨z, hz0, fun w hw => ?_⟩
    by_cases hwz : w = 0
    · exact ⟨0, le_refl 0, by simp [hwz]⟩
    · have hpz : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
      have hzne : ‖z‖ ≠ 0 := hpz.ne'
      refine ⟨‖w‖ / ‖z‖, div_nonneg (norm_nonneg _) hpz.le, ?_⟩
      have h1 : ‖((‖w‖ / ‖z‖ : ℝ) : ℂ)‖ = ‖w‖ / ‖z‖ := by
        norm_cast
        exact abs_of_nonneg (div_nonneg (norm_nonneg w) (norm_nonneg z))
      have hpw : (0:ℝ) < ‖w‖ := norm_pos_iff.mpr hwz
      have hre : Complex.arg ((↑(‖w‖ / ‖z‖) : ℂ) * z) = Complex.arg z :=
        Complex.arg_real_mul (r := ‖w‖ / ‖z‖) z (div_pos hpw hpz)
      refine Complex.ext_norm_arg ?_ ?_
      · rw [norm_mul, h1]
        field_simp
      · rw [hre, hw, hz]

/-- HOL `ARG_DIV_EQ_SUBSET_HALFLINE` (REUHADY.hl:110). -/
theorem argDivEqSubsetHalfline : ∀ w : ℂ, w ≠ 0 → ∀ a : ℝ, ∃ b : ℂ, b ≠ 0 ∧
    {z : ℂ | Complex.arg (z / w) = a} ⊆ {z : ℂ | ∃ t : ℝ, 0 ≤ t ∧ z = (t : ℂ) * b} := by
  intro w hw a
  obtain ⟨b₀, hb₀, hsub⟩ := argEqSubsetHalfline a
  refine ⟨b₀ * w, mul_ne_zero hb₀ hw, fun z hz => ?_⟩
  obtain ⟨t, ht0, hzr⟩ := hsub hz
  refine ⟨t, ht0, ?_⟩
  rw [← mul_assoc]
  exact (div_eq_iff hw).mp hzr

/-! ## List kit for the REUHADY1 preamble (glue, proved) -/

/-- `truncate_simplex 1 vl = [EL 0 vl; EL 1 vl]` for `2 ≤ LENGTH vl`
(HL `Marchal_cells.TRUNCATE_SIMPLEX_EXPLICIT_1/2` usage form, as
consumed by the `REUHADY1` preamble and OXLZLEZ3). -/
theorem truncateSimplex1_pair (vl : List V3) (h2 : 2 ≤ vl.length) :
    truncateSimplex 1 vl = [elV vl 0, elV vl 1] := by
  cases vl with
  | nil => exact absurd h2 (by simp)
  | cons x tl =>
    cases tl with
    | nil => exact absurd h2 (by simp)
    | cons y rest =>
      have hsub : initialSublist [x, y] (x :: y :: rest) := ⟨rest, rfl⟩
      have h := (INITIAL_SUBLIST_IMP_TRUNCATE_SIMPLEX hsub (by simp)).1
      exact h.symm

/-- HOL `set_of_list (truncate_simplex 1 vl) = {EL 0 vl, EL 1 vl}`. -/
theorem setOfList_truncateSimplex1 (vl : List V3) (h2 : 2 ≤ vl.length) :
    setOfList (truncateSimplex 1 vl) = {elV vl 0, elV vl 1} := by
  rw [truncateSimplex1_pair vl h2]
  ext x
  simp [setOfList]

/-- Collinearity with a pair puts the point on the pair's line
(forward direction; used by `coplanarAzimEq`'s axis case). -/
theorem collinear3_mem_affineSpan_pair {v0 v1 z : V3} (hne : v0 ≠ v1)
    (hc : Collinear3 v0 v1 z) : z ∈ (affineSpan ℝ {v0, v1} : Set V3) := by
  have hz : z ∈ ({v0, v1, z} : Set V3) := by simp
  have hm := hc.mem_affineSpan_of_mem_of_ne (p₁ := v0) (p₂ := v1) (p₃ := z)
    (by simp) (by simp) hz hne
  simpa using hm

/-! ## COPLANAR_AZIM_EQ and the measure theorems (giants for this lane) -/

/-- HOL `COPLANAR_AZIM_EQ` (REUHADY.hl:121). GIANT — `sorry`.
NEEDS: the witness-construction route — pick a frame via
`exists_on3_eq_smul` + `azimSpec_exists` for `(w1,w1)`, build
`f := v0 + r1*(cos(ψ+a)) • e1 + r1*(sin(ψ+a)) • e2 + h1 • (v1 - v0)`
with `azim v0 v1 w1 f = a` (via `azim_eq_azim_iff`), then
`{z | azim v0 v1 w1 z = a} ⊆ affineSpan ℝ {v0, v1, f}` (non-collinear
`z` from `azim_eq_azim_iff` + `affGt ⊆ affineSpan`; collinear `z` from
`collinear3_mem_affineSpan_pair` above) and finrank-vectorSpan ≤ 2
coplanarity. HL instead reduces to `real^2` `Arg` halflines via
pushin/dropout. -/
theorem coplanarAzimEq (v0 v1 w1 : V3) (a : ℝ)
    (h : Collinear3 v0 v1 w1 → ¬(a = 0)) :
    Coplanar ℝ {z | azim v0 v1 w1 z = a} := by
  sorry

/-- HOL `MEASURABLE_CONIC_CAP_WEDGE_GE` (REUHADY.hl:162). GIANT —
`sorry`. NEEDS: measurability of azimuth level sets and the open wedge
(route: translate to `0` via a private `azim_sub_self` copy
(WedgeVolume.lean:50, private there), then
`azim_eq_ang_of_frame` + `measurable_ang` + continuity of
`zOf e1 e2 (· - v0)`, plus `conicCap` = closedBall ∩ rconeGt Borel
(PackingAuto10:308-329 pattern, private there)); HL uses
`MEASURABLE_CONIC_CAP_WEDGE` + `COPLANAR_IMP_NEGLIGIBLE` +
`COPLANAR_AZIM_EQ`. -/
theorem measurableConicCapWedgeGe (v0 v1 w1 w2 : V3) (r a : ℝ) :
    MeasurableSet (conicCapP24 v0 v1 r a ∩ wedgeGe v0 v1 w1 w2) := by
  sorry

/-- HOL `VOLUME_CONIC_CAP_WEDGE_GE_VS_CONIC_CAP` (REUHADY.hl:178).
GIANT — `sorry`. NEEDS: `VOLUME_CONIC_CAP` /
`VOLUME_CONIC_CAP_WEDGE` (flyspeck_multivariate.ml conic-cap volume
formulas, not ported in any lane), `MEASURE_NEGLIGIBLE_SYMDIFF`
symmetric-difference argument on the wedge boundary level sets (via
`coplanarAzimEq`), and `azim < 2*pi` positivity arithmetic. -/
theorem volumeConicCapWedgeGeVsConicCap (v0 v1 w1 w2 : V3) (r a : ℝ)
    (ha1 : 0 < a) (ha2 : a < 1) (hr : 0 < r ∧ r ≤ 1)
    (h1 : ¬Collinear3 v0 v1 w1) (h2 : ¬Collinear3 v0 v1 w2) :
    volume.real (conicCapP24 v0 v1 r a ∩ wedgeGe v0 v1 w1 w2) =
      volume.real (conicCapP24 v0 v1 r a) * (azim v0 v1 w1 w2) / (2 * Real.pi) := by
  sorry

/-! ## Capstones: the pack_concl REUHADY conclusions -/

/-- HOL `REUHADY_concl` (pack_concl.hl:306-321), statement-identical to
`PackingAuto2.REUHADY_concl` (DISCHARGE candidate at merge). GIANT —
`sorry`. NEEDS: `REUHADY1` plus synthesis of its stronger hypotheses
from this one's: the closed-wedge intersection subset
(`wedgeGe u0 u1 v1 v2 ∩ wedgeGe u0 u1 v2 v1 ⊆ affGe ...`) requires the
leaf-cell wedge-disjointness input (`Leaf_cell.WEDGE_GE_ALMOST_DISJOINT`
/ `FCHKUGT`, OXLZLEZ3.hl:867-875); `u0,u1 ∈ V`, `u0 ≠ u1` come from
`barV`/packing extraction; `hl [u0,u1] < sqrt 2` from
`dist u0 u1 < sqrt 8` via the pair half-length (`HL_2`,
PackingAuto15:257, olean absent in this checkout); `vl1 ≠ vl2` from
`azim ≠ 0` + `azim_self`. -/
theorem REUHADY_p24 : ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3) (v1 v2 : V3)
    (e : Set V3) (w1 w2 : V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
    e = {u0, u1} → ¬(azim u0 u1 w1 w2 = 0) →
    hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
    barV V 2 vl1 ∧ barV V 2 vl2 →
    setOfList (truncateSimplex 1 vl1) = e ∧
    setOfList (truncateSimplex 1 vl2) = e ∧
    v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
    (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
      azim u0 u1 v1 v2 := by
  sorry

/-- HOL `REUHADY_concl_version2` (pack_concl.hl:325-340),
statement-identical to `PackingAuto2.REUHADY_concl_version2` (DISCHARGE
candidate at merge). GIANT — `sorry`. Same gap profile as
`REUHADY_p24` minus the azimuth non-degeneracy branch: the
wedge-intersection hypothesis is PRESENT here, but `u0,u1 ∈ V`,
`u0 ≠ u1`, `hl [u0,u1] < sqrt 2`, `vl1 ≠ vl2` still need the barV/pair
extraction noted above (`azim ≠ 0` is not available to kill `vl1 = vl2`
— that direction is WEDGE_GE_ALMOST_DISJOINT territory). -/
theorem REUHADY_version2_p24 : ∀ (V : Set V3) (u0 u1 : V3) (vl1 vl2 : List V3)
    (v1 v2 : V3) (e : Set V3), saturated V → Packing V → dist u0 u1 < Real.sqrt 8 →
    e = {u0, u1} →
    wedgeGe u0 u1 v1 v2 ∩ wedgeGe u0 u1 v2 v1 ⊆
      affGe {u0, u1} {v1} ∪ affGe {u0, u1} {v2} →
    hl vl1 < Real.sqrt 2 ∧ hl vl2 < Real.sqrt 2 →
    barV V 2 vl1 ∧ barV V 2 vl2 →
    setOfList (truncateSimplex 1 vl1) = e ∧
    setOfList (truncateSimplex 1 vl2) = e ∧
    v1 = elV vl1 2 ∧ v2 = elV vl2 2 ∧
    (∀ X : Set V3, X ∈ mcellSet V ∧ e ∈ edgeX V X →
      X ⊆ wedgeGe u0 u1 v1 v2 ∨ X ⊆ wedgeGe u0 u1 v2 v1) →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X ∧
        X ⊆ wedgeGe u0 u1 v1 v2} (fun t => dihX V t (u0, u1)) =
      azim u0 u1 v1 v2 := by
  sorry

/-! ## GRUTOTI statement copy (parallel-owned Auto23) -/

/-- NEEDS (Auto23, GRUTOTI.hl:48-58): `GRUTOTI1_concl` statement copy —
the parallel Auto23 lane owns the proof of `GRUTOTI1_concl` (already
sorried in PackingAuto2); the 2π edge-total is the complementary
measure-splitting fact consumed alongside `REUHADY1` by downstream
wedge/annulus arguments. This `_p24` copy documents the dependency for
merge; delete at merge into Auto23's results. -/
private theorem GRUTOTI1_concl_p24 : ∀ (V : Set V3) (u0 u1 : V3) (e : Set V3),
    saturated V → Packing V → u0 ∈ V → u1 ∈ V → u0 ≠ u1 →
    hl [u0, u1] < Real.sqrt 2 → e = {u0, u1} →
    setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X}
        (fun t => dihX V t (u0, u1)) = 2 * Real.pi := by
  sorry

end Kepler.Text
