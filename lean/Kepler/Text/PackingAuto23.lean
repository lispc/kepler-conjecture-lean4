/-
PackingAuto23.lean — GRUTOTI capstone (skeleton-first port).

HOL source: scripts/packing/GRUTOTI.hl (8005 lines; module Grutoti,
Flyspeck book lemma GRUTOTI, Vu Khac Ky 2012). The HL file is ONE
`prove_by_refinement` block (GRUTOTI.hl:60-8001, 636 NEW_GOALs) with no
explicit sub-lemmas; this port re-expresses the proof's milestone goals as a
private lemma chain feeding the capstone.

Statement (GRUTOTI.hl:48-58): the dihedral angles of all Marchal cells along
a short edge {u0,u1} (hl < √2) in a saturated packing sum to 2π. Matches
`PackingAuto2.GRUTOTI1_concl` shape verbatim; once the giants below are
discharged, `GRUTOTI` discharges GRUTOTI1_concl by `exact GRUTOTI …`.

Proof skeleton (HL GRUTOTI.hl line ranges → private lemmas):
  62-160    barV V 1 [u0;u1]; GLTVHUM_lemma1 k-set; k=3 Voronoi/Rogers cover
            → grutoti_barV, grutoti_3mem (proved); grutoti_vor_cover (giant).
  161-2636  sliver core: p = midpoint circumcenter, relative-interior S1/S2,
            ball p 8 finiteness, C = ball u0 1 ∩ rcone_gt u0 u1 c,
            r = min 1 (min r1 r2), d = max c (max d1 d2), D ⊆ C, mcell cover
            along e (HL:2631) → grutoti_region (giant).
  2652-7958 per-cell wedge volume vol (X ∩ D) = vol D·dihX/(2π); k = 2,3 case
            analysis (mxi/ω3, AZIM_COMPL), k = 0,1,4 null-intersection
            → grutoti_cell_vol (giant).
  7228-7400 sum over edge cells of vol (X ∩ D) = vol D (measure union) and
            finiteness → grutoti_sum_volD (giant).
  7960-7966 pivot sum (vol·∩D) = sum (vol D·dihX/2π) → grutoti_pivot (giant);
            the linear step SUM_EQ/SUM_LMUL is proved (grutoti_setSum_mul_div).
  7967-8001 cancel with vol D > 0 (VOLUME_CONIC_CAP) → grutoti_volD_pos
            (giant); grutoti_cancel/grutoti_concl_arith (proved).

Encoding: HOL `real^3` ↔ `V3`; `vol` ↔ `volume.real`; `NULLSET` ↔ `nullSet`;
`conic_cap a b r d` ↔ `conicCap a b r d` (closedBall ∩ rconeGt); NOTE
PackingAuto15 has no built olean yet, so its `conicCap`, `RCONE_GT_SUBSET`
(proved) and `HL_LE_SQRT2_IMP_BARV_1` (sorried there too) are re-stated
privately here;
HOL set `sum` ↔ `setSum` (Auto2; index finiteness folded into
grutoti_sum_volD); `mcell_set V X` ↔ `X ∈ mcellSet V`. Sorried giants carry
NEEDS-precision notes; mechanical steps are proved.

2026-09-19 pass: `grutoti_hl_barV` SHIMMED to
`PackingAuto15.HL_LE_SQRT2_IMP_BARV_1` (olean landed; still `sorry`ed
upstream); `grutoti_vor_cover` FILLED (assembled from `grutoti_3mem` +
Auto12's `VORONOI_LIST_3_SINGLETON_EXPLICIT` shim + `CLOSEST_POINT_SING`);
`grutoti_volD_pos` re-documented (frozen statement is FALSE for the
degenerate `u1 = u0` — the empty conic cap; caller `GRUTOTI` has `hne`).

2026-09-28 GT-2 pass: `PackingAuto15.FINITE_EDGE_X2` (Auto15:672) and
`PackingAuto15.MCELL_SUBSET_BALL8_1` (Auto15:794) FILLED upstream (this
lane's PA15 arm) — the two PA15 dependencies named in `grutoti_sum_volD`'s
docstring are now real. The finite Pack2-measure bridge and the SUM_EQ
assembly are banked here as proved privates (`p23_measure_setSum_biUnion`,
`p23_setSum_congr`, `p23_setSum_of_zero`, `p23_dihX_of_nullSet`); the two
giant sorries `grutoti_sum_volD` / `grutoti_pivot` remain frozen with
detailed NEEDS notes (both need the region-block cover + §H per-cell
non-nullness, shared with grutoti_region/grutoti_cell_vol); `grutoti_volD_pos`
frozen-false premise now carries a STATEMENT-FIX proposal + patch (item 18).

2026-09-30 GT-3b/c pass: the `grutoti_cell_vol` arm kit banked as proved
privates — private copies of PA24's `coplanarAzimEq` +
`p24_coplanar_measure_null` (PA23 does not import PA24; provenance notes
inline), the affine-hull null workhorse `p23_coplanar_affineSpan_null`
(HL's 34× `NEGLIGIBLE_SUBSET (affine hull …) + COPLANAR_IMP_NEGLIGIBLE`
pattern), the azimuth-sheet killer `p23_cap_inter_azimLevel_null`, the
self-cone emptiness `p23_rconeGt_self_empty` (degenerate capsule), the §H
counting arm `p23_edge_cell_k_ge_two` (k = 0,1 impossible for edge cells),
and the junk-safety `p23_dihX_of_cellParamsD_ne`. `grutoti_cell_vol`'s
`u0 = u1` degenerate arm discharged inline; its frozen `sorry` now covers
only the non-degenerate wedge identities (k = 2,3 core + k = 4
non-coplanar), which need the region-block data — see its docstring for the
updated branch map and the missing edge-cell-hypothesis caveat.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.ConicCapVolume
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto15
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## The edge-cell family (HL GRUTOTI.hl:7227 `s`) -/

/-- HOL `conic_cap` (marchal3.hl; Auto15:109 `conicCap`, no olean yet —
private copy). -/
private def grutotiConicCap (v0 v1 : V3) (r a : ℝ) : Set V3 :=
  Metric.closedBall v0 r ∩ rconeGt v0 v1 a

/-- marchal3.hl `RCONE_GT_SUBSET` (Auto15:289, proved; private copy). -/
private theorem grutoti_rconeGt_subset (u0 u1 : V3) (a b : ℝ) (h : a ≤ b) :
    rconeGt u0 u1 b ⊆ rconeGt u0 u1 a := by
  intro x hx
  simp only [rconeGt, Set.mem_setOf_eq] at hx ⊢
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h (by positivity)) hx

/-- marchal3.hl:1054 `HL_LE_SQRT2_IMP_BARV_1` (Auto15:282). SHIM
(2026-09-19): the PackingAuto15 olean HAS landed in this checkout, so the
private copy discharges to `Kepler.Text.PackingAuto15.HL_LE_SQRT2_IMP_BARV_1`
(statement-identical; still `sorry`ed upstream in Auto15 — a documented
transitive shim; delete the copy at merge into Auto15's results). -/
private theorem grutoti_hl_barV (V : Set V3) (u0 u1 : V3) (hs : saturated V)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) : barV V 1 [u0, u1] :=
  HL_LE_SQRT2_IMP_BARV_1 V u0 u1 hs hp hu0 hu1 hne hhl

/-- HL GRUTOTI.hl:7227: `s = {X | mcell_set V X /\ edgeX V X e}` — the index
set of the final sums (identical to the GRUTOTI1_concl set by definition). -/
private def grutotiEdgeCells (V : Set V3) (e : Set V3) : Set (Set V3) :=
  {X | X ∈ mcellSet V ∧ e ∈ edgeX V X}

/-! ## Mechanical chain links (proved) -/

/-- HL GRUTOTI.hl:62-64: the edge is a `barV V 1` simplex
(`grutoti_hl_barV`, marchal3.hl:1054). -/
private theorem grutoti_barV (V : Set V3) (u0 u1 : V3) (hs : saturated V)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) : barV V 1 [u0, u1] :=
  grutoti_hl_barV V u0 u1 hs hp hu0 hu1 hne hhl

/-- HL GRUTOTI.hl:100-128 helper: `truncate_simplex 1 [u0;u1] = [u0;u1]`. -/
private theorem grutoti_trunc1 (u0 u1 : V3) :
    truncateSimplex 1 [u0, u1] = [u0, u1] := by
  have hex : ∃ vl : List V3, vl.length = 1 + 1 ∧ initialSublist vl [u0, u1] :=
    ⟨[u0, u1], rfl, ⟨[], by simp⟩⟩
  have hspec := Classical.epsilon_spec
    (p := fun vl : List V3 => vl.length = 1 + 1 ∧ initialSublist vl [u0, u1]) hex
  obtain ⟨yl, hyl⟩ := hspec.2
  have hlen : ([u0, u1] : List V3).length = 2 := rfl
  rw [hyl, List.length_append, hspec.1] at hlen
  have h3 : yl.length = 0 := by omega
  rcases yl with _ | ⟨a, t⟩
  · rw [List.append_nil] at hyl
    exact hyl.symm
  · simp at h3

/-- HL GRUTOTI.hl:76-84: `3` lies in the GLTVHUM_lemma1 index set, giving the
`k = 3` Rogers/Voronoi cover of `voronoiList V [u0, u1]`. -/
private theorem grutoti_3mem (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (hbar : barV V 1 [u0, u1]) :
    voronoiList V [u0, u1] =
      ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc 1 (3 - 1)} ∪
        voronoiList V vl) | vl ∈ {vl : List V3 |
        barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]}} := by
  have h := GLTVHUM_lemma1 V [u0, u1] 1 hp hs (by norm_num) hbar
  have hmem : (3 : ℕ) ∈ {k : ℕ | k ∈ (Finset.Icc 1 3 : Set ℕ) ∧
      voronoiList V [u0, u1] =
        ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc 1 (k - 1)} ∪
          voronoiList V vl) | vl ∈ {vl : List V3 |
          barV V k vl ∧ truncateSimplex 1 vl = [u0, u1]}}} := by
    rw [h]
    simp
  exact hmem.2

/-- HL GRUTOTI.hl:1487-1488 analogue: the cap is inside the radius-`r`
closed ball. -/
private theorem grutoti_cap_subset_closedBall (u0 u1 : V3) (r d : ℝ) :
    grutotiConicCap u0 u1 r d ⊆ Metric.closedBall u0 r := Set.inter_subset_left

/-- HL GRUTOTI.hl:7322-7324 analogue: the cap is inside the radius-1 open
ball once `r < 1`. -/
private theorem grutoti_cap_subset_ball (u0 u1 : V3) (r d : ℝ) (hr : r < 1) :
    grutotiConicCap u0 u1 r d ⊆ Metric.ball u0 1 :=
  Set.inter_subset_left.trans (Metric.closedBall_subset_ball hr)

/-- HL GRUTOTI.hl:2620-2629: `D ⊆ rcone_gt u0 u1 c` (with `c ≤ d`) via
`RCONE_GT_SUBSET`. -/
private theorem grutoti_cap_rcone_mono (u0 u1 : V3) (r c d : ℝ) (h : c ≤ d) :
    grutotiConicCap u0 u1 r d ⊆ rconeGt u0 u1 c :=
  Set.inter_subset_right.trans (grutoti_rconeGt_subset u0 u1 c d h)

/-- HL GRUTOTI.hl:7964-7968: SUM_EQ + SUM_LMUL — pulling a constant
coefficient out of a `setSum`. -/
private theorem grutoti_setSum_mul_div (T : Set (Set V3)) (c : ℝ) (f : Set V3 → ℝ)
    (hT : T.Finite) :
    setSum T (fun X => c * f X / (2 * Real.pi)) = c * setSum T f / (2 * Real.pi) := by
  rw [setSum, dif_pos hT, setSum, dif_pos hT]
  rw [← Finset.sum_div, ← Finset.mul_sum]

/-- HL GRUTOTI.hl:7971-8001: cancelling the positive factor `vol D`. -/
private theorem grutoti_cancel (S D : ℝ) (hD : 0 < D)
    (h : D * S / (2 * Real.pi) = D) : S = 2 * Real.pi := by
  have h2 : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  refine mul_left_cancel₀ (ne_of_gt hD) ?_
  rwa [div_eq_iff (ne_of_gt h2)] at h

/-- Final assembly (HL GRUTOTI.hl:7962-8001): from `sum = vol D` and the
wedge pivot, `sum dihX = 2π`. -/
private theorem grutoti_concl_arith (w S volD : ℝ) (hvol : 0 < volD)
    (hsum : w = volD) (hpivot : w = volD * S / (2 * Real.pi)) :
    S = 2 * Real.pi :=
  grutoti_cancel S volD hvol (by rw [← hpivot]; exact hsum)

/-! ## GT-2 lane private kit (proved 2026-09-28)

The finite Pack2-measure bridge and SUM_EQ assembly lemmas feeding
`grutoti_sum_volD` / `grutoti_pivot`. -/

/-- HOL `SUM_EQ` finite form: on a finite index set, pointwise equal functions
have equal `setSum`s. -/
private theorem p23_setSum_congr {α : Type*} {s : Set α} {f g : α → ℝ}
    (hs : s.Finite) (h : ∀ x ∈ s, f x = g x) : setSum s f = setSum s g := by
  rw [setSum, dif_pos hs, setSum, dif_pos hs]
  refine Finset.sum_congr rfl fun x hx => ?_
  exact h x ((Set.Finite.mem_toFinset hs).mp hx)

/-- HOL junk lemma: a function vanishing on a finite index set has zero
`setSum`. -/
private theorem p23_setSum_of_zero {α : Type*} {s : Set α} {f : α → ℝ}
    (hs : s.Finite) (h : ∀ x ∈ s, f x = 0) : setSum s f = 0 := by
  rw [setSum, dif_pos hs]
  exact Finset.sum_eq_zero fun x hx => h x ((Set.Finite.mem_toFinset hs).mp hx)

/-- HOL `dihX` junk branch: `dihX` vanishes on null cells (PA2 encoding, the
`nullSet X → 0` first branch of `PackingAuto2.dihX`). -/
private theorem p23_dihX_of_nullSet (V : Set V3) (X : Set V3) (p : V3 × V3)
    (h : nullSet X) : dihX V X p = 0 := if_pos h

/-- Finite `MEASURE_NEGLIGIBLE_UNIONS_IMAGE` (Pack2 bridge; grutoti-scout §2.2):
over a finite family of measurable, individually finite-volume sets with
pairwise-null intersections, the sum of the volumes equals the volume of the
union of the images. -/
private theorem p23_measure_setSum_biUnion {ι : Type*} {s : Set ι} {f : ι → Set V3}
    (hs : s.Finite) (hmeas : ∀ i ∈ s, MeasurableSet (f i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → volume (f i ∩ f j) = 0)
    (hne : ∀ i ∈ s, volume (f i) ≠ ⊤) :
    setSum s (fun i => volume.real (f i)) = volume.real (⋃₀ (f '' s)) := by
  classical
  have hbU : (⋃ a ∈ s, f a) = ⋃ a ∈ hs.toFinset, f a := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, hfx⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨a, (Set.Finite.mem_toFinset hs).mpr ha, hfx⟩
    · intro hx
      obtain ⟨a, ha, hfx⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨a, (Set.Finite.mem_toFinset hs).mp ha, hfx⟩
  have hd : Set.Pairwise (↑hs.toFinset) (Function.onFun (AEDisjoint volume) f) := by
    intro i hi j hj hij
    show volume (f i ∩ f j) = 0
    exact hpair i ((Set.Finite.mem_toFinset hs).mp hi) j
      ((Set.Finite.mem_toFinset hs).mp hj) hij
  have hm : ∀ b ∈ hs.toFinset, NullMeasurableSet (f b) volume := fun b hb =>
    (hmeas b ((Set.Finite.mem_toFinset hs).mp hb)).nullMeasurableSet
  rw [setSum, dif_pos hs, Set.sUnion_image, hbU]
  show (∑ w ∈ hs.toFinset, (volume (f w)).toReal)
      = (volume (⋃ a ∈ hs.toFinset, f a)).toReal
  rw [MeasureTheory.measure_biUnion_finset₀ hd hm]
  rw [ENNReal.toReal_sum fun i hi => hne i ((Set.Finite.mem_toFinset hs).mp hi)]

/-! ## GT-3 lane private kit (2026-09-30)

The `grutoti_cell_vol`/`grutoti_pivot` arm kit: private copies of PA24's
`coplanarAzimEq` + `p24_coplanar_measure_null` (PA23 does not import PA24 —
ccv_-convention private copies, provenance notes inline) plus the
null-intersection/counting combos that close the `k = 0,1` arms and the
degenerate branches of the per-cell analysis (HL §E/§H junk arms). -/

/-! ### PA24 copies (bodies verbatim modulo the `p23_` renaming; all proved
upstream in PackingAuto24.lean, 2026-09-19/30) -/


/-! ### The azim witness/affine-span kit (2026-09-19 fill, proved) -/

private theorem p23_exists_azim_point (v0 v1 w1 : V3) (a : ℝ)
    (hv01 : v0 ≠ v1) (hcw : ¬ Collinear3 v0 v1 w1)
    (ha0 : 0 < a) (ha2 : a < 2 * Real.pi) :
    ∃ f : V3, ¬ Collinear3 v0 v1 f ∧ azim v0 v1 w1 f = a := by
  have hwv : v1 ≠ v0 := Ne.symm hv01
  obtain ⟨e1, e2, e3, hon, halign⟩ :=
    exists_on3_eq_smul (v1 - v0) (sub_ne_zero.mpr hwv)
  have hax : (v1 - v0 : V3) = dist v1 v0 • e3 := by rw [dist_eq_norm]; exact halign
  obtain ⟨hp1, -⟩ := axis_perp hax hon
  have hp1' : (e3 : V3) ⬝ᵥ e1 = 0 := by
    rw [show ((e3 : V3)) ⬝ᵥ (e1 : V3) = (e1 : V3) ⬝ᵥ (e3 : V3) from dotProduct_comm _ _]
    exact hon.2.2.2.2.1
  have hw2nc : ¬ Collinear3 v0 v1 (v0 + e1) := by
    intro hcol
    obtain ⟨c, hc⟩ := (collinear3_iff_smul hwv).mp hcol
    have hsimp : ((v0 + e1 : V3) - v0) = e1 := by simp
    rw [hsimp, hax, smul_smul] at hc
    have hdot := congrArg (fun x : V3 => x ⬝ᵥ e1) hc
    rw [show (((c * dist v1 v0 : ℝ)) • (e3 : V3)) ⬝ᵥ e1
        = c * dist v1 v0 * ((e3 : V3) ⬝ᵥ e1) from by
      rw [← inner_eq_dot, ← inner_eq_dot, real_inner_smul_left], hp1', mul_zero] at hdot
    rw [hon.1] at hdot
    exact absurd hdot (by norm_num)
  obtain ⟨ψ, r1, r2, hr1, hr2, hzw1, -⟩ := azim_frame_spec hcw hw2nc hon hax hwv
  set f : V3 := v0 + (r1 * Real.cos (ψ + a)) • e1 + (r1 * Real.sin (ψ + a)) • e2 with hf
  have hsub : (f : V3) - v0
      = (r1 * Real.cos (ψ + a)) • e1 + (r1 * Real.sin (ψ + a)) • e2 + (0:ℝ) • (v1 - v0) := by
    rw [hf]; module
  have hzF : zOf e1 e2 (f - v0) = (r1 : ℂ) * Complex.exp (((ψ + a : ℝ)) * Complex.I) :=
    zOf_of_rep hon hax hsub
  have hnz : zOf e1 e2 (f - v0) ≠ 0 := by
    rw [hzF]
    exact mul_ne_zero (by exact_mod_cast hr1.ne') (Complex.exp_ne_zero _)
  have hfnc : ¬ Collinear3 v0 v1 f :=
    (zOf_ne_zero_iff hon hax hwv f).mp hnz
  refine ⟨f, hfnc, ?_⟩
  have hspec : AzimSpec v0 v1 w1 f (azim v0 v1 w1 f) := by
    unfold azim
    rw [if_neg (by rintro (h | h); exacts [hcw h, hfnc h])]
    exact Classical.epsilon_spec (azimSpec_exists hcw hfnc)
  unfold AzimSpec at hspec
  obtain ⟨-, -, h1', h2', hframes⟩ := hspec
  obtain ⟨ψ', r1', r2', hrep1, hrep2, hr1', hr2'⟩ := hframes e1 e2 e3 hon hax hwv
  have hz1 : zOf e1 e2 (w1 - v0) = (r1' : ℂ) * Complex.exp ((ψ' : ℝ) * Complex.I) :=
    zOf_of_rep hon hax hrep1
  have hz2 : zOf e1 e2 (f - v0) = (r2' : ℂ) * Complex.exp
      (((ψ' + azim v0 v1 w1 f : ℝ)) * Complex.I) :=
    zOf_of_rep hon hax hrep2
  have hn1 : ‖zOf e1 e2 (w1 - v0)‖ = r1 := by
    rw [hzw1, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr1, exp_unit_norm, mul_one]
  have hn1' : ‖zOf e1 e2 (w1 - v0)‖ = r1' := by
    rw [hz1, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr1', exp_unit_norm, mul_one]
  have hn2 : ‖zOf e1 e2 (f - v0)‖ = r1 := by
    rw [hzF, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr1, exp_unit_norm, mul_one]
  have hn2' : ‖zOf e1 e2 (f - v0)‖ = r2' := by
    rw [hz2, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr2', exp_unit_norm, mul_one]
  have hr1eq : r1' = r1 := hn1'.symm.trans hn1
  have hr2eq : r2' = r1 := hn2'.symm.trans hn2
  rw [hr1eq] at hz1
  rw [hr2eq] at hz2
  have hu1 : Complex.exp ((ψ' : ℝ) * Complex.I) = Complex.exp ((ψ : ℝ) * Complex.I) := by
    have hkey : (r1 : ℂ) * Complex.exp ((ψ' : ℝ) * Complex.I)
        = (r1 : ℂ) * Complex.exp ((ψ : ℝ) * Complex.I) := hz1.symm.trans hzw1
    exact mul_left_cancel₀ (by exact_mod_cast hr1.ne') hkey
  have hunits : Complex.exp ((azim v0 v1 w1 f : ℝ) * Complex.I)
      = Complex.exp ((a : ℝ) * Complex.I) := by
    have hkey : (r1 : ℂ) * Complex.exp (((ψ' + azim v0 v1 w1 f : ℝ)) * Complex.I)
        = (r1 : ℂ) * Complex.exp (((ψ + a : ℝ)) * Complex.I) := hz2.symm.trans hzF
    rw [exp_add_I, exp_add_I, hu1] at hkey
    have h1 := mul_left_cancel₀ (a := ((r1 : ℂ))) (by exact_mod_cast hr1.ne') hkey
    exact mul_left_cancel₀ (a := Complex.exp ((ψ : ℝ) * Complex.I))
      (Complex.exp_ne_zero _) h1
  exact angle_eq_of_exp_eq (azim_nonneg v0 v1 w1 f) (azim_lt_two_pi v0 v1 w1 f)
    ha0.le ha2 hunits


private theorem p23_mem_affineSpan_triple (v0 v1 w z : V3) (c₂ c₃ : ℝ)
    (hz : z = v0 + c₂ • (v1 - v0) + c₃ • (w - v0)) :
    z ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)) := by
  have h0 : v0 ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)) := mem_affineSpan (k := ℝ) (by simp)
  have h1 : v1 ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)) := mem_affineSpan (k := ℝ) (by simp)
  have h2 : w ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)) := mem_affineSpan (k := ℝ) (by simp)
  have d1 : (v1 - v0 : V3) ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction h1 h0
  have d2 : (w - v0 : V3) ∈ (affineSpan ℝ ({v0, v1, w} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction h2 h0
  have dsum : c₂ • (v1 - v0) + c₃ • (w - v0) ∈
      (affineSpan ℝ ({v0, v1, w} : Set V3)).direction :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ d1) (Submodule.smul_mem _ _ d2)
  have hv := AffineSubspace.vadd_mem_of_mem_direction dsum h0
  rw [show ((c₂ • (v1 - v0) + c₃ • (w - v0)) +ᵥ v0)
    = v0 + (c₂ • (v1 - v0) + c₃ • (w - v0))
    from (vadd_eq_add _ _).trans (add_comm _ _)] at hv
  rw [hz, add_assoc]
  exact hv

/-- COPLANAR_IMP_NEGLIGIBLE (HOL `COPLANAR_IMP_NEGLIGIBLE` content, in the
root-`Coplanar` form `Module.rank ℝ (vectorSpan ℝ S) ≤ 2` that PA24's frozen
`Coplanar ℝ _` statements elaborate to): anything inside a coplanar set is
Lebesgue-null. The coplanar set lies in a proper affine subspace, null by
Mathlib `Measure.addHaar_affineSubspace`; outer-measure monotonicity (`measure_mono_null`)
needs no measurability of the inner set. -/
private theorem p23_coplanar_measure_null {T S : Set V3} (hS : Coplanar ℝ S)
    (hT : T ⊆ S) : volume T = 0 := by
  have hfd : FiniteDimensional ℝ (vectorSpan ℝ S) := hS.finiteDimensional_vectorSpan
  have hfin2 : Module.finrank ℝ (vectorSpan ℝ S) ≤ 2 :=
    (coplanar_iff_finrank_le_two (k := ℝ)).mp hS
  have hvs : (vectorSpan ℝ S : Submodule ℝ V3) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hfin2
    have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    rw [h3] at hfin2
    norm_num at hfin2
  have htop_aff : (affineSpan ℝ S : AffineSubspace ℝ V3) ≠ ⊤ := fun hE =>
    hvs (AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ V3 V3 hE)
  exact measure_mono_null (hT.trans (subset_affineSpan ℝ S))
    (Measure.addHaar_affineSubspace volume _ htop_aff)

/-- The affine span of a triple, as a set, is coplanar in the root-`Coplanar`
sense (Mathlib `coplanar_triple` transported along `direction_affineSpan`). -/
private theorem p23_coplanar_affineSpan_triple (u v w : V3) :
    Coplanar ℝ ((affineSpan ℝ ({u, v, w} : Set V3) : Set V3)) := by
  have h := _root_.coplanar_triple (k := ℝ) u v w
  show Module.rank ℝ ↥((affineSpan ℝ ({u, v, w} : Set V3)).direction) ≤ 2
  rw [direction_affineSpan]
  exact h

/-- HOL `COPLANAR_AZIM_EQ` (REUHADY.hl:121). FILLED (2026-09-30): the two
main ingredients proved above — `p23_exists_azim_point` (the frame/polar
witness `f` off the axis with `azim v0 v1 w1 f = a`) and
`p23_mem_affineSpan_triple` (affineSpan-triple membership) — splice into the
documented case tree. (1) `a ∉ [0, 2π)` is vacuous via `azim_nonneg` /
`azim_lt_two_pi`; (2) `a = 0` needs `¬Collinear3 v0 v1 w1` (from `h`), then
the zero sheet lies in `affineSpan ℝ {v0,v1,w1}` (`collinear3_iff_smul` on the
axis, `azim_eq_zero_iff_alt` + `affGt_pair_iff` off it); (3) `0 < a < 2π`:
`p23_exists_azim_point` gives the witness `f`, and `azim_eq_azim_iff` +
`affGt_pair_iff` put every `z` of the level set into `affineSpan ℝ {v0,v1,f}`;
(4) coplanarity is read off via `p23_coplanar_affineSpan_triple` +
`_root_.Coplanar.subset`. NOTE the Geom-vs-root `Coplanar` split: this frozen
statement is Mathlib's root `Coplanar` (two explicit arguments, rank-of-
vectorSpan ≤ 2), NOT `Kepler.Geom.Coplanar` (the affineSpan-triple
existential, one argument) — resolution is by arity. -/
private theorem p23_coplanarAzimEq (v0 v1 w1 : V3) (a : ℝ)
    (h : Collinear3 v0 v1 w1 → ¬(a = 0)) :
    Coplanar ℝ {z | azim v0 v1 w1 z = a} := by
  by_cases han : a < 0
  · -- a < 0: the level set is empty
    refine _root_.Coplanar.subset (fun z hz => ?_)
      (_root_.coplanar_empty (k := ℝ) (P := V3))
    have h1 := azim_nonneg v0 v1 w1 z
    rw [hz] at h1
    exact absurd h1 (not_le.mpr han)
  · by_cases ha2' : 2 * Real.pi ≤ a
    · -- a ≥ 2π: the level set is empty
      refine _root_.Coplanar.subset (fun z hz => ?_)
        (_root_.coplanar_empty (k := ℝ) (P := V3))
      have h1 := azim_lt_two_pi v0 v1 w1 z
      rw [hz] at h1
      exact absurd h1 (not_lt.mpr ha2')
    · rcases eq_or_lt_of_le (le_of_not_gt han) with ha0 | hapos
      · -- a = 0: the zero sheet lies in the plane affineSpan {v0, v1, w1}
        rw [← ha0] at h ⊢
        rcases eq_or_ne v0 v1 with hv | hv01
        · exact absurd rfl (h (by rw [hv]; exact collinear3_of_eq rfl))
        · have hnc1 : ¬ Collinear3 v0 v1 w1 := fun hc => (h hc) rfl
          refine _root_.Coplanar.subset (fun z hz => ?_)
            (p23_coplanar_affineSpan_triple v0 v1 w1)
          by_cases hcz : Collinear3 v0 v1 z
          · obtain ⟨cc, hczv⟩ := (collinear3_iff_smul (Ne.symm hv01)).mp hcz
            exact p23_mem_affineSpan_triple v0 v1 w1 z cc 0 (by
              rw [show z = v0 + (z - v0) from by abel, hczv]; module)
          · obtain ⟨c, hcpos, t, hdec⟩ :=
              (affGt_pair_iff (v0 := v0) (v1 := v1) (x := w1) (y := z) hv01
                (fun he => hnc1 (collinear3_pair_left he))
                (fun he => hnc1 (collinear3_pair_right he))).mp
              ((azim_eq_zero_iff_alt hnc1 hcz).mp hz)
            exact p23_mem_affineSpan_triple v0 v1 w1 z t c (by
              rw [show z = v0 + (z - v0) from by abel, hdec]; module)
      · -- 0 < a < 2π
        rcases Classical.em (Collinear3 v0 v1 w1) with hc1 | hnc1
        · -- w1 on the axis: every azimuth vanishes, the level set is empty
          refine _root_.Coplanar.subset (fun z hz => ?_)
            (_root_.coplanar_empty (k := ℝ) (P := V3))
          have h0 : azim v0 v1 w1 z = 0 := by
            rw [azim, if_pos (Or.inl hc1)]
          simp only [Set.mem_setOf_eq] at hz
          rw [h0] at hz
          exact (h hc1) hz.symm
        · rcases eq_or_ne v0 v1 with hv | hv01
          · exact absurd (by rw [hv]; exact collinear3_of_eq rfl) hnc1
          · obtain ⟨f, hfnc, hfaz⟩ := p23_exists_azim_point v0 v1 w1 a hv01 hnc1
              hapos (lt_of_not_ge ha2')
            refine _root_.Coplanar.subset (fun z hz => ?_)
              (p23_coplanar_affineSpan_triple v0 v1 f)
            by_cases hcz : Collinear3 v0 v1 z
            · have h0 : azim v0 v1 w1 z = 0 := by
                rw [azim, if_pos (Or.inr hcz)]
              simp only [Set.mem_setOf_eq] at hz
              rw [h0] at hz
              exact absurd hz.symm (by linarith)
            · have hmem := (azim_eq_azim_iff hnc1 hfnc hcz).mp (hfaz.trans hz.symm)
              obtain ⟨c, hcpos, t, hdec⟩ :=
                (affGt_pair_iff (v0 := v0) (v1 := v1) (x := f) (y := z) hv01
                  (fun he => hfnc (collinear3_pair_left he))
                  (fun he => hfnc (collinear3_pair_right he))).mp hmem
              exact p23_mem_affineSpan_triple v0 v1 f z t c (by
                rw [show z = v0 + (z - v0) from by abel, hdec]; module)

/-! ### New combos: the `grutoti_cell_vol` arm-closers (2026-09-30) -/

/-- COPLANAR_AFFINE_HULL_COPLANAR + NEGLIGIBLE_SUBSET in one piece: a set
inside the affine hull of a coplanar set is Lebesgue-null (the HL §E/§H
`NEGLIGIBLE_SUBSET (affine hull …) + COPLANAR_IMP_NEGLIGIBLE` workhorse,
34 uses). Adapted from `p24_coplanar_measure_null`'s proof. -/
private theorem p23_coplanar_affineSpan_null {T S : Set V3} (hS : Coplanar ℝ S)
    (hT : T ⊆ (affineSpan ℝ S : Set V3)) : volume T = 0 := by
  have hfd : FiniteDimensional ℝ (vectorSpan ℝ S) := hS.finiteDimensional_vectorSpan
  have hfin2 : Module.finrank ℝ (vectorSpan ℝ S) ≤ 2 :=
    (coplanar_iff_finrank_le_two (k := ℝ)).mp hS
  have hvs : (vectorSpan ℝ S : Submodule ℝ V3) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hfin2
    have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    rw [h3] at hfin2
    norm_num at hfin2
  have htop_aff : (affineSpan ℝ S : AffineSubspace ℝ V3) ≠ ⊤ := fun hE =>
    hvs (AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ V3 V3 hE)
  exact measure_mono_null hT (Measure.addHaar_affineSubspace volume _ htop_aff)

/-- The degenerate-branch killer combo: the cap's intersection with any
azimuth level sheet is null (`p23_coplanarAzimEq` + `p23_coplanar_measure_null`;
consumes the PA24 ammo in one line, as HL's COPLANAR_IMP_NEGLIGIBLE
applications on `conic_cap ∩ {azim = …}` sheets do). -/
private theorem p23_cap_inter_azimLevel_null (u0 u1 w : V3) (r a θ : ℝ)
    (h : Collinear3 u0 u1 w → ¬(θ = 0)) :
    volume (grutotiConicCap u0 u1 r a ∩ {z : V3 | azim u0 u1 w z = θ}) = 0 :=
  p23_coplanar_measure_null (p23_coplanarAzimEq u0 u1 w θ h) Set.inter_subset_right

/-- The self-cone is empty for ANY parameter (`rconeGt u u a = ∅`): the
dot product with the zero vector vanishes, and so does `dist x u * dist u u * a`.
Feeds the degenerate-capsule arm of `grutoti_cell_vol` (`u0 = u1` forces
`D = ∅`). -/
private theorem p23_rconeGt_self_empty (u : V3) (a : ℝ) :
    rconeGt u u a = ∅ := by
  ext x
  simp only [rconeGt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  rw [sub_self, dotProduct_zero, dist_self] at hx
  simp at hx

/-- The degenerate capsule (`u0 = u1`) is empty. -/
private theorem p23_grutotiConicCap_self_empty (u : V3) (r a : ℝ) :
    grutotiConicCap u u r a = ∅ := by
  rw [grutotiConicCap, p23_rconeGt_self_empty u a, Set.inter_empty]

/-- `truncateSimplex` ε-选取属性 (PA2 私件 `p2g_trunc_init_len` 的链复制:
PA23 需要, PA2 未公开). -/
private theorem p23_trunc_init_len (k : ℕ) (zl : List V3) (h : k + 1 ≤ zl.length) :
    initialSublist (truncateSimplex k zl) zl ∧ (truncateSimplex k zl).length = k + 1 := by
  have heps := @Classical.epsilon_spec _
    (fun vl : List V3 => vl.length = k + 1 ∧ initialSublist vl zl)
    ⟨zl.take (k + 1), List.length_take_of_le (by omega),
      ⟨zl.drop (k + 1), (List.take_append_drop (k + 1) zl).symm⟩⟩
  exact ⟨heps.2, heps.1⟩

/-- HL §H arm (a) (GRUTOTI.hl:7536-7556): an edge cell carrying two DISTINCT
edge points has `cellParams`-`k ≥ 2` — `k ≤ 1` gives `VX V X` of card ≤ 1
(list truncation), too small for `{u0, u1}`. Kills the `k = 0,1` arms of
`grutoti_cell_vol`/`grutoti_pivot` inside the edge-cell context. -/
private theorem p23_edge_cell_k_ge_two (V : Set V3) (X : Set V3) (u0 u1 : V3)
    (hm : X ∈ mcellSet V) (hu0 : u0 ∈ VX V X) (hu1 : u1 ∈ VX V X) (hne : u0 ≠ u1) :
    2 ≤ (cellParams V X).1 := by
  obtain ⟨i, ul, hX, hbar⟩ := Set.mem_setOf_eq.mp hm
  have hX4 : X = mcell (min i 4) V ul := by
    rcases Nat.lt_or_ge i 4 with hlt | hle
    · rw [hX, min_eq_left (le_of_lt hlt)]
    · rw [hX, min_eq_right hle, (MCELL_EXPLICIT i V ul).2.2.2.2 hle,
        (MCELL_EXPLICIT 4 V ul).2.2.2.2 (Nat.le_refl 4)]
  have hwit : (cellParams V X).1 ≤ 4 ∧ barV V 3 (cellParams V X).2 ∧
      X = mcell (cellParams V X).1 V (cellParams V X).2 :=
    Classical.epsilon_spec
      (p := fun q : ℕ × List V3 => q.1 ≤ 4 ∧ barV V 3 q.2 ∧ X = mcell q.1 V q.2)
      ⟨(min i 4, ul), by omega, hbar, hX4⟩
  have hnnull : ¬ nullSet X := by
    intro hnull
    unfold VX at hu0
    rw [if_pos hnull] at hu0
    simp at hu0
  unfold VX at hu0 hu1
  simp only [if_neg hnnull] at hu0 hu1
  by_cases hk0 : (cellParams V X).1 = 0
  · rw [if_pos hk0] at hu0
    simp at hu0
  · rw [if_neg hk0] at hu0 hu1
    have h4 : (cellParams V X).2.length = 4 := hwit.2.1.1
    have hlen : (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).length
        = (cellParams V X).1 := by
      have h := p23_trunc_init_len ((cellParams V X).1 - 1) (cellParams V X).2
        (by omega)
      omega
    set l := truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2 with hleq
    simp only [setOfList, Set.mem_setOf_eq] at hu0 hu1
    rcases l with _ | ⟨a, t⟩
    · simp at hu0
    · rcases t with _ | ⟨b, t2⟩
      · simp only [List.mem_singleton] at hu0 hu1
        exact absurd (hu0.trans hu1.symm) hne
      · simp only [List.length_cons] at hlen
        omega

/-- Junk-safety for the future `grutoti_pivot` fill (PA2:410-417 encoding):
`dihX` vanishes whenever the `cellParamsD` index is outside `{2,3,4}`
(the `k ≤ 1` arm) — the null-cell arm is already banked as
`p23_dihX_of_nullSet`. -/
private theorem p23_dihX_of_cellParamsD_ne (V : Set V3) (X : Set V3) (p : V3 × V3)
    (hnn : ¬ nullSet X)
    (h2 : (cellParamsD V X [p.1, p.2]).1 ≠ 2)
    (h3 : (cellParamsD V X [p.1, p.2]).1 ≠ 3)
    (h4 : (cellParamsD V X [p.1, p.2]).1 ≠ 4) : dihX V X p = 0 := by
  simp only [dihX, if_neg hnn, if_neg h2, if_neg h3, if_neg h4]


/-! ## Giants (sorried, NEEDS-precision) -/

/-- HL GRUTOTI.hl:86-160: the `k = 3` specialization of grutoti_3mem — the
Voronoi cell of the edge is the union of the Rogers hulls
`convex hull {ω₁, ω₂, ω₃}` over `barV V 3` lists truncating to `[u0, u1]`.
FILLED (2026-09-19) from grutoti_3mem plus
`PackingAuto12.VORONOI_LIST_3_SINGLETON_EXPLICIT` (SHIM: still `sorry`ed
upstream in Auto12): on each truncation list the Voronoi cell is the
singleton `{a}`, `a = circumcenter (setOfList vl)`, and `omega_list_n V vl 3`
— being `closest_point` on that singleton (with
`truncate_simplex 3 vl = vl` and `CLOSEST_POINT_SING`) — equals `a`, so the
3mem family `{hull ({ωᵢ | i ∈ Icc 1 2} ∪ voronoiList V vl)}` coincides with
the hull-of-triple family. -/
private theorem grutoti_vor_cover (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (hbar : barV V 1 [u0, u1]) :
    voronoiList V [u0, u1] =
      ⋃₀ {convexHull ℝ {omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3} |
          vl ∈ {vl : List V3 | barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]}} := by
  have key : ∀ vl : List V3, barV V 3 vl → truncateSimplex 1 vl = [u0, u1] →
      convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc 1 (3 - 1)} ∪ voronoiList V vl) =
        convexHull ℝ {omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3} := by
    intro vl hb _htr
    obtain ⟨a, hsingle, hcc, -⟩ := VORONOI_LIST_3_SINGLETON_EXPLICIT V vl hp hs hb
    have hlen : vl.length = 4 := hb.1
    have homeg : omegaListN V vl 3 = a := by
      have h3 : omegaListN V vl 3
          = closestPoint (voronoiList V (truncateSimplex 3 vl)) (omegaListN V vl 2) := rfl
      rw [h3, TRUNCATE_SIMPLEX_REFL 3 vl hlen, hsingle]
      exact CLOSEST_POINT_SING a (omegaListN V vl 2)
    have hIcc : {omegaListN V vl i | i ∈ Finset.Icc 1 (3 - 1)}
        = {omegaListN V vl 1, omegaListN V vl 2} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        Finset.mem_coe, Finset.mem_Icc]
      constructor
      · rintro ⟨i, hi1, hi2, rfl⟩
        rcases Nat.eq_zero_or_pos (i - 1) with h0 | _h0
        · exact Or.inl (by rw [show i = 1 by omega])
        · exact Or.inr (by rw [show i = 2 by omega])
      · rintro (rfl | rfl)
        · exact ⟨1, by norm_num, rfl⟩
        · exact ⟨2, by norm_num, rfl⟩
    congr 1
    rw [hIcc, hsingle, homeg]
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  rw [grutoti_3mem V u0 u1 hp hs hbar]
  refine Set.ext fun X => ?_
  constructor
  · intro hX
    rw [Set.mem_sUnion] at hX
    obtain ⟨t, ht, hX⟩ := hX
    rw [Set.mem_setOf_eq] at ht
    obtain ⟨vl, hmem, rfl⟩ := ht
    rw [Set.mem_setOf_eq] at hmem
    obtain ⟨hb, htr⟩ := hmem
    rw [key vl hb htr] at hX
    refine Set.mem_sUnion.mpr ⟨convexHull ℝ {omegaListN V vl 1, omegaListN V vl 2,
      omegaListN V vl 3}, ?_, hX⟩
    exact ⟨vl, Set.mem_setOf.mpr ⟨hb, htr⟩, rfl⟩
  · intro hX
    rw [Set.mem_sUnion] at hX
    obtain ⟨t, ht, hX⟩ := hX
    rw [Set.mem_setOf_eq] at ht
    obtain ⟨vl, hmem, rfl⟩ := ht
    rw [Set.mem_setOf_eq] at hmem
    obtain ⟨hb, htr⟩ := hmem
    rw [(key vl hb htr).symm] at hX
    refine Set.mem_sUnion.mpr ⟨convexHull ℝ ({omegaListN V vl i |
      i ∈ Finset.Icc 1 (3 - 1)} ∪ voronoiList V vl), ?_, hX⟩
    exact ⟨vl, Set.mem_setOf.mpr ⟨hb, htr⟩, rfl⟩

/-- HL GRUTOTI.hl:161-2636: the volumetric core. Produces cone/annulus
parameters `c r d` (`c = max b (hl/√2)`, `r = min 1 (min r1 r2)`,
`d = max c (max d1 d2)` from the P1..P4 extremal arguments) with `D =
grutotiConicCap u0 u1 r d ⊆ C`, and the mcell cover (HL:2631-2636): every
Marchal cell meeting `D` in positive measure is a `k ≥ 2` cell over a
`barV V 3` list with `truncateSimplex 1 vl = [u0, u1]`.
NEEDS-precision: relative-interior/affine-hull analysis of
`S1 = {x | 2(u0-u1)·x = …}` vs `S = voronoiList V [u0,u1]` (HL:203-1125),
finite `B = V ∩ ball p 8` selection of nearest point `a'` (HL:415-590),
`rcone_gt`/ball inclusion kit (HL:1091-1143), P1/P2 minima over truncation
lists (HL:1538-2283), `NEGLIGIBLE_AFFINE_HULL_3`/coplanarity sliver bounds. -/
private theorem grutoti_region (V : Set V3) (u0 u1 : V3) (e : Set V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) (he : e = {u0, u1}) :
    ∃ c r d : ℝ, 0 < c ∧ c < 1 ∧ 0 < r ∧ r ≤ 1 ∧ 0 < d ∧ d < 1 ∧ c ≤ d ∧
      (∀ X : Set V3, X ∈ mcellSet V ∧ ¬nullSet (X ∩ grutotiConicCap u0 u1 r d) →
        ∃ k : ℕ, ∃ vl : List V3, 2 ≤ k ∧ barV V 3 vl ∧ X = mcell k V vl ∧
          truncateSimplex 1 vl = [u0, u1]) := by
  sorry

/-- HL GRUTOTI.hl:2652-2653 (proved there by the case analysis to 7958): the
per-cell wedge-volume identity. GT-3b status (2026-09-30): the `u0 = u1`
degenerate arm is discharged inline below (`p23_grutotiConicCap_self_empty`:
the capsule is the empty self-cone); the k-arms over the `mcellSet` witness
consume the GT-3 kit banked above — `k = 0,1`: impossible once the cell
carries two distinct edge points (`p23_edge_cell_k_ge_two`, HL §H arm (a);
junk-safety outside `k ∈ {2,3,4}`: `p23_dihX_of_cellParamsD_ne`; null cells:
`p23_dihX_of_nullSet`); `k = 4`-degenerate and the k = 2/3 wedge-boundary
sheets: coplanar-⇒-null via `p23_coplanar_measure_null` (private copy of
PA24's COPLANAR_IMP_NEGLIGIBLE content), the affine-hull workhorse
`p23_coplanar_affineSpan_null` (HL's 34× `NEGLIGIBLE_SUBSET (affine hull …)`
pattern), and the azimuth level sheets `p23_cap_inter_azimLevel_null` (via
the `p23_coplanarAzimEq` private copy of PA24's `COPLANAR_AZIM_EQ` fill).
REMAINING GIANT (the `sorry` below): the non-degenerate wedge identities —
k = 2 (HL §D: `mcell2` = double `rconeGe` ∩ the `affGe {u0,u1} {mxi, ω₃}`
wedge `L`, `vol (X∩D) = vol (L∩D)`, closed by CCV `volumeConicCapWedge`),
k = 3 (HL §F: hull + the AZIM_COMPL complement identity, `AZIM_COMPL_EXT`
PA6:2107), k = 4 non-coplanar (HL §E: needs the region-block extremal data
from `grutoti_region` to put `X ∩ D` into the coplanar sliver). CAVEAT
(scout risk §3): the frozen signature carries no edge-cell hypothesis
(`e ∈ edgeX V X`, i.e. `u0,u1 ∈ VX V X ∧ u0 ≠ u1`) — the k = 0,1 counting
arm and the k = 4 degenerate closure are only consumable in that context,
which the `grutoti_pivot` fill supplies; an SF proposal for the hypothesis
should precede the core fill. -/
private theorem grutoti_cell_vol (V : Set V3) (u0 u1 : V3) (r d : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hd1 : d < 1) (X : Set V3)
    (hm : X ∈ mcellSet V) (hn : ¬nullSet (X ∩ grutotiConicCap u0 u1 r d)) :
    volume.real (X ∩ grutotiConicCap u0 u1 r d) =
      volume.real (grutotiConicCap u0 u1 r d) * dihX V X (u0, u1) / (2 * Real.pi) := by
  by_cases hne : u0 = u1
  · rw [hne] at hn
    have hnull : nullSet (X ∩ grutotiConicCap u1 u1 r d) := by
      show volume (X ∩ grutotiConicCap u1 u1 r d) = 0
      rw [p23_grutotiConicCap_self_empty u1 r d, Set.inter_empty]
      exact measure_empty
    exact absurd hnull hn
  -- NEEDS: the non-degenerate k-arms (HL §D/§E/§F) — k = 2 wedge identity via
  -- `volumeConicCapWedge` + the mcell2 shape; k = 3 via `AZIM_COMPL_EXT`;
  -- k = 4 non-coplanar needs `grutoti_region`'s extremal data (see docstring).
  sorry

/-- HL GRUTOTI.hl:7228-7400 (`sum s (\t. vol (t INTER D)) = vol D` via
`MEASURE_NEGLIGIBLE_UNIONS_IMAGE` over the almost-disjoint cell family) plus
index finiteness from `FINITE_MCELL_SET_LEMMA_2` (marchal3.hl:2620; Auto15:520,
cells are bounded, e.g. `grutoti_cap_subset_ball`). NEEDS-precision.
GT-2 lane note (2026-09-28): the PA15 dependencies are now REAL
(`FINITE_EDGE_X2` Auto15:672 FILLED, `MCELL_SUBSET_BALL8_1` Auto15:794 FILLED)
and the measure machinery is banked as `p23_measure_setSum_biUnion`. The frozen
signature itself is still unprovable for two independent reasons, both needing
the STATEMENT-FIX/编排者 channel rather than more filling:
(1) finiteness of `grutotiEdgeCells V e` is FALSE for a general `V` — the
statement carries no `Packing V`/`saturated V`; an adversarial `V`
(`{u0,u1}` plus infinitely many generic far points) has infinitely many
`barV V 3` lists whose `mcell 4` cells carry `e ∈ edgeX V X` (the true
finiteness route is FINITE_EDGE_X2, which needs `hp, hs`), and
(2) the vol identity holds only for the region-block `D`: `grutoti_region`
(HL 161-2636) + TIWWFYQ/GLTVHUM/SLTSTLO1 give `D` ⊆ ⋃₀ of edge-cell traces up
to a null set, and AJRIPQN (PA17:310, sorried) gives the pairwise-null
intersections that `p23_measure_setSum_biUnion` consumes. Suggested unfrozen
signature: add `hp hs`, the region cover hypothesis
`volume.real (D \ ⋃₀ {X ∩ D | X ∈ grutotiEdgeCells V e}) = 0` (or take the
cover as an explicit hypothesis), and `0 < r`/`d < 1`.
cells are bounded, e.g. `grutoti_cap_subset_ball`). NEEDS-precision. -/
private theorem grutoti_sum_volD (V : Set V3) (u0 u1 : V3) (e : Set V3) (r d : ℝ)
    (he : e = {u0, u1}) :
    (grutotiEdgeCells V e).Finite ∧
      setSum (grutotiEdgeCells V e)
        (fun X => volume.real (X ∩ grutotiConicCap u0 u1 r d)) =
        volume.real (grutotiConicCap u0 u1 r d) := by
  sorry

/-- HL GRUTOTI.hl:7962-7966: the wedge pivot — the vol-sum equals the
`vol D · dihX / 2π` sum. Needs grutoti_cell_vol per edge cell (the
¬nullSet hypothesis is discharged inside by the k-case analysis) and
grutoti_setSum_mul_div for the linear step. NEEDS-precision.
GT-2 lane note (2026-09-28): the honest route (HL §G/§H, 7441-7958) is now
mapped: (a) for EVERY edge cell X (u0,u1 ∈ VX V X) one first shows
k := (cellParams V X).1 ≥ 2 — the counting arm `i - 1 = 0` of §H: VX V X is a
set of ≤ k list points containing two distinct points; k ≤ 1 is impossible;
(b) for k ≥ 2 one shows `¬nullSet (X ∩ D)` — HL §H derives `F` from
`NULLSET (X ∩ D)` per k, using CONIC_CAP_INTER_CONVEX_HULL_4_GT_0
(Auto15:828, still sorried) for k = 3/4 and the region data for k = 2 —
this is the remaining blocker, shared with grutoti_cell_vol (GT-3);
(c) then `p23_setSum_congr` assembles the frozen identity from
`grutoti_cell_vol` pointwise. Junk safety: for k ≤ 1 / null cells the PA2
encoding gives dihX = 0 (`p23_dihX_of_nullSet`), and k ≤ 1 cells cannot carry
the edge at all, so no junk term enters the sum. CAVEAT for the future fill:
`cellParamsD V X [u0,u1]` may be epsilon-junk for edge cells whose param list
carries the edge REVERSED (`[u1;u0,…]` — its wedge is a genuinely different
set); HL §H handles this inside the case analysis, and the Lean fill must too.
grutoti_setSum_mul_div for the linear step. NEEDS-precision. -/
private theorem grutoti_pivot (V : Set V3) (u0 u1 : V3) (e : Set V3) (r d : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hd1 : d < 1) (he : e = {u0, u1})
    (hfin : (grutotiEdgeCells V e).Finite) :
    setSum (grutotiEdgeCells V e)
        (fun X => volume.real (X ∩ grutotiConicCap u0 u1 r d)) =
      setSum (grutotiEdgeCells V e)
        (fun X => volume.real (grutotiConicCap u0 u1 r d) *
          dihX V X (u0, u1) / (2 * Real.pi)) := by
  sorry

/-- HL GRUTOTI.hl:7983-8000: `0 < vol D` from `VOLUME_CONIC_CAP`
(marchal3; `vol (conic_cap u0 u1 r d) = 2/3 · π · r³ · (1-d)² …`-type formula,
positive for `0 < d < 1`, `0 < r`). STILL `sorry`, with an honest note
(2026-09-19): the statement as frozen is FALSE for the degenerate `u1 = u0`
(then `rconeGt u0 u0 d = ∅`, so `vol D = 0`); the caller `GRUTOTI` supplies
`hne : u0 ≠ u1` but the frozen private signature omits it. The fill route
under `u0 ≠ u1` is elementary — `D` contains the open ball
`ball (u0 + (r/2)·(u1-u0)/‖u1-u0‖, r·(1-d)/(4·(1+d)))` (cone/ball arithmetic
+ `volume` positivity of open balls) — port it together with the missing
hypothesis at merge. STATEMENT-FIX filed (2026-09-28 GT-2 lane):
`docs/statement-fix-proposals.md` item 18 + patch
`docs/statement-fix-proposals-patches/18-grutoti_volD_pos.patch` — add
`hne : u0 ≠ u1` (HOL: the goal lives under GRUTOTI1_concl's `~(u0 = u1)`,
GRUTOTI.hl:48-58; the frozen formula route is GT-1's
`ConicCapVolume.volumeConicCapPos`, which carries the same `hne`, and the
degenerate capsule is provably empty — ConicCapVolume `ccv_conicCap_empty`),
after which the fill is one line.
hypothesis at merge. -/
private theorem grutoti_volD_pos (u0 u1 : V3) (r d : ℝ) (hr : 0 < r) (hd : 0 < d)
    (hd1 : d < 1) (hne : u0 ≠ u1) : 0 < volume.real (grutotiConicCap u0 u1 r d) :=
  volumeConicCapPos hr hd hd1 hne

/-! ## Capstone -/

/-- HOL `GRUTOTI` (GRUTOTI.hl:60-8001): the dihedral angles of all Marchal
cells along a short edge sum to `2π`. Statement-identical to
`PackingAuto2.GRUTOTI1_concl`, which it discharges (`exact GRUTOTI …`) once
the sorried giants above are proved. -/
theorem GRUTOTI : ∀ (V : Set V3) (u0 u1 : V3) (e : Set V3), saturated V →
    Packing V → u0 ∈ V → u1 ∈ V → u0 ≠ u1 → hl [u0, u1] < Real.sqrt 2 →
    e = {u0, u1} →
    setSum {X | mcellSet V X ∧ e ∈ edgeX V X} (fun t => dihX V t (u0, u1)) =
      2 * Real.pi := by
  intro V u0 u1 e hs hp hu0 hu1 hne hhl he
  have hbar := grutoti_barV V u0 u1 hs hp hu0 hu1 hne hhl
  obtain ⟨c, r, d, hc0, hc1, hr0, hr1, hd0, hd1, hdc, _hcover⟩ :=
    grutoti_region V u0 u1 e hs hp hu0 hu1 hne hhl he
  have hvol := grutoti_volD_pos u0 u1 r d hr0 hd0 hd1 hne
  obtain ⟨hfin, hsum⟩ := grutoti_sum_volD V u0 u1 e r d he
  have hpivot := grutoti_pivot V u0 u1 e r d hr0 hr1 hd0 hd1 he hfin
  have hlin := grutoti_setSum_mul_div (grutotiEdgeCells V e)
    (volume.real (grutotiConicCap u0 u1 r d)) (fun X => dihX V X (u0, u1)) hfin
  exact grutoti_concl_arith _ _ _ hvol hsum (hpivot.trans hlin)

end Kepler.Text
