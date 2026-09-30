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

2026-09-30 GT-4b pass: the region-block B5-B7 remainder closed (see the
GT-4b lane section before `grutoti_region`): the B5 cover kit (family
finiteness + rogers/mcell decomposition over C, AJRIPQN via PA17), the B6
P1-P4 extremal data (f1/f2 > 0, f3/f4 < 1 via smallestAngleLine + the
coplanarity killer), and the B7 assembly (r = min 1/2 (min r1 r2) — the 1/2
cap replaces HL's `min 1` because the Lean `grutotiConicCap` uses a CLOSED
ball — d = max c (max d1 d2), D ⊆ C, mcell cover). `grutoti_region` is
proved zero-sorry; the only upstream sorry debt is PA17's `AJRIPQN` and
PA12's `VORONOI_LIST_3_SINGLETON_EXPLICIT` shim (both recorded in their
docstrings since earlier waves).

2026-09-30 GT-4 pass: the region-block B1-B4 bridges banked as a 14-lemma
zero-sorry private chain (`p23Bis` + `p23_region_exists_delta` +
`p23_region_exists_c`, see the GT-4 lane section above): bisector S1
characterization/closedness/unboundedness, interface S closed/bounded
(saturation route, no BOUNDED_VORONOI_LIST needed), midpoint XYOFCGX
(strict + weak forms; Apollonius, no circumcenter API), critical radius δ
via the relative neighbourhood S' = S1 ∩ ball(p,d₀) ⊆ S (HL B2's a'/d₀
nearest-point selection — replaces HL's `S1 \ relative_interior S`, whose
closedness needs the unported AFF_DIM_VORONOI_LIST, and avoids the
intrinsicInterior bridge), and the cone threshold c ∈ (0,1) with
`rconeGt u0 u1 c ⊆ affGeAlt {u0} S` + `⊆ rconeGt u0 u1 (hl/√2)` (B3's
ray-hits-bisector argument + B4's max-assembly). `grutoti_region` itself
still `sorry` (B5-B7: rogers/mcell cover kit + P1-P4 minima + assembly,
HL:1144-2636) — see its updated NEEDS note.

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
import Kepler.Text.PackingAuto17
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

/-! ## GT-4 lane: B1-B4 region-block bridges (2026-09-30, zero sorry)

HL GRUTOTI.hl:161-1143 (B1-B4): the bisector hyperplane S1, the interface
S = voronoiList V [u0,u1], the midpoint bridge (Rogers.XYOFCGX), the critical
radius δ and the cone threshold c. These feed the P1-P4 extremal arguments
(B5-B7) that assemble grutoti_region below; p23_region_exists_c is the
current milestone. NOTE: HL's S2 = S1 \ relative_interior S is replaced by
the explicit relative neighbourhood S' = S1 ∩ ball(p,d₀) ⊆ S (HL B2's
nearest-point selection); this avoids both the aff-dim equality
aff hull S = S1 (whose Lean counterpart AFF_DIM_VORONOI_LIST is unported)
and the intrinsicInterior bridge.
-/

/-! ## B1: the bisector hyperplane -/

/-- The bisector hyperplane of the edge (HL `S1`, GRUTOTI.hl:252), in the
ray-friendly form `(x - u0) · (u1 - u0) = d²/2`. -/
private def p23Bis (u0 u1 : V3) : Set V3 :=
  {x | inner ℝ (x - u0) (u1 - u0) = dist u0 u1 ^ 2 / 2}

private theorem p23_inner_expand (a b c d : V3) :
    inner ℝ (a - b) (c - d) = inner ℝ a c - inner ℝ a d - inner ℝ b c + inner ℝ b d := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  ring

private theorem p23_dist_sq (x v : V3) :
    dist x v ^ 2 = inner ℝ x x - 2 * inner ℝ x v + inner ℝ v v := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_sub_right, real_inner_comm v x]
  ring

/-- equidistance characterizes the bisector -/
private theorem p23_dist_eq_bis (u0 u1 x : V3) :
    dist x u0 = dist x u1 ↔ x ∈ p23Bis u0 u1 := by
  have e0 := p23_dist_sq x u0
  have e1 := p23_dist_sq x u1
  have hd : dist u0 u1 ^ 2 = inner ℝ u1 u1 - 2 * inner ℝ u0 u1 + inner ℝ u0 u0 := by
    rw [dist_comm u0 u1, dist_eq_norm, ← real_inner_self_eq_norm_sq]
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm u1 u0]
    ring
  have hx : inner ℝ (x - u0) (u1 - u0)
      = inner ℝ x u1 - inner ℝ x u0 - inner ℝ u0 u1 + inner ℝ u0 u0 :=
    p23_inner_expand x u0 u1 u0
  constructor
  · intro h
    rw [← h] at e1
    show inner ℝ (x - u0) (u1 - u0) = _
    rw [hx]
    linarith
  · intro h
    show dist x u0 = dist x u1
    rw [p23Bis, Set.mem_setOf_eq] at h
    have h2 : dist x u0 ^ 2 = dist x u1 ^ 2 := by rw [e0, e1]; linarith
    have h3 := congrArg Real.sqrt h2
    rw [Real.sqrt_sq dist_nonneg, Real.sqrt_sq dist_nonneg] at h3
    exact h3

/-- HL CLOSED_HYPERPLANE: the bisector is closed. -/
private theorem p23_bis_closed (u0 u1 : V3) : IsClosed (p23Bis u0 u1) := by
  set f : V3 → ℝ := fun x => inner ℝ (x - u0) (u1 - u0) with hf
  have hcont : Continuous f := by
    unfold f
    exact (continuous_id.sub continuous_const).inner continuous_const
  have h1 : IsClosed {x : V3 | f x ≤ dist u0 u1 ^ 2 / 2} :=
    isClosed_le hcont continuous_const
  have h2 : IsClosed {x : V3 | dist u0 u1 ^ 2 / 2 ≤ f x} :=
    isClosed_le continuous_const hcont
  have h3 : p23Bis u0 u1 = {x : V3 | f x ≤ dist u0 u1 ^ 2 / 2} ∩
      {x : V3 | dist u0 u1 ^ 2 / 2 ≤ f x} := by
    ext x
    simp only [p23Bis, Set.mem_setOf_eq, Set.mem_inter_iff, hf]
    constructor
    · intro h; exact ⟨le_of_eq h, le_of_eq h.symm⟩
    · intro h; exact le_antisymm h.1 h.2
  rw [h3]
  exact h1.inter h2

/-- the Voronoi cell of a point is closed -/
private theorem p23_voronoiClosed_closed (V : Set V3) (v : V3) :
    IsClosed (voronoiClosed V v) := by
  have h : voronoiClosed V v = ⋂ w : V, {x : V3 | dist x v ≤ dist x w} := by
    ext x
    rw [voronoiClosed, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · exact fun hx i => hx i i.property
    · exact fun hx w hw => hx ⟨w, hw⟩
  rw [h]
  refine isClosed_iInter fun w => ?_
  exact isClosed_le (Continuous.dist continuous_id continuous_const)
    (Continuous.dist continuous_id continuous_const)

/-- `voronoi_list V [u0;u1]` = the intersection of the two cells -/
private theorem p23_voronoiList_pair (V : Set V3) (u0 u1 : V3) :
    voronoiList V [u0, u1] = voronoiClosed V u0 ∩ voronoiClosed V u1 := by
  show ⋂₀ {voronoiClosed V v | v ∈ setOfList [u0, u1]} = _
  ext x
  constructor
  · intro hx
    have h0 := hx (voronoiClosed V u0)
      (Set.mem_image_of_mem _ (by simp [setOfList]))
    have h1 := hx (voronoiClosed V u1)
      (Set.mem_image_of_mem _ (by simp [setOfList]))
    exact ⟨h0, h1⟩
  · intro hx t ht
    obtain ⟨v, hv, rfl⟩ := ht
    have hv' : v ∈ ({u0, u1} : Set V3) := by simpa [setOfList] using hv
    rcases Set.mem_insert_iff.mp hv' with rfl | rfl
    · exact hx.1
    · exact hx.2

/-- the interface is closed -/
private theorem p23_voronoiList_closed (V : Set V3) (u0 u1 : V3) :
    IsClosed (voronoiList V [u0, u1]) := by
  rw [p23_voronoiList_pair V u0 u1]
  exact (p23_voronoiClosed_closed V u0).inter (p23_voronoiClosed_closed V u1)

/-- the interface is inside the bisector -/
private theorem p23_voronoiList_sub_bis (V : Set V3) (u0 u1 : V3)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) :
    voronoiList V [u0, u1] ⊆ p23Bis u0 u1 := by
  intro x hx
  rw [p23_voronoiList_pair V u0 u1] at hx
  refine p23_dist_eq_bis u0 u1 x |>.mp ?_
  refine le_antisymm ?_ ?_
  · exact hx.1 u1 hu1
  · exact hx.2 u0 hu0

/-- saturation bounds every closed Voronoi cell (HL BOUNDED_VORONOI_LIST
route, via the <2 saturation axiom) -/
private theorem p23_voronoiClosed_bounded (V : Set V3) (hs : saturated V) (v : V3) :
    Bornology.IsBounded (voronoiClosed V v) := by
  refine Bornology.IsBounded.subset (Metric.isBounded_ball (x := v) (r := 2)) ?_
  intro x hx
  obtain ⟨y, hy, hdy⟩ := hs x
  have hle : dist x v ≤ dist x y := hx y hy
  rw [Metric.mem_ball]
  linarith

/-- nonzero vector orthogonal to the edge direction -/
private theorem p23_exists_orthogonal (u0 u1 : V3) (hne : u0 ≠ u1) :
    ∃ w : V3, w ≠ 0 ∧ inner ℝ w (u0 - u1) = 0 := by
  have hnz : (u0 - u1 : V3) ≠ 0 := sub_ne_zero.mpr hne
  set N : Submodule ℝ V3 := Submodule.span ℝ ({u0 - u1} : Set V3) with hN
  have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
  have hrk : 0 < Module.finrank ℝ ↥Nᗮ := by
    have hdim := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := V3) N
    have hrkN : Module.finrank ℝ ↥N = 1 := by
      rw [hN]
      exact finrank_span_singleton hnz
    rw [h3] at hdim
    linarith
  obtain ⟨x, hx0⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := ↥Nᗮ)).mp hrk
  refine ⟨(x : V3), ?_, ?_⟩
  · intro hwx
    exact hx0 (Subtype.ext hwx)
  · have hxm : (x : V3) ∈ Nᗮ := x.property
    exact (Submodule.mem_orthogonal' N (x : V3)).mp hxm (u0 - u1)
      (by rw [hN]; exact Submodule.mem_span_singleton_self _)

/-- HL UNBOUNDED_HYPERPLANE: the bisector hyperplane is unbounded -/
private theorem p23_bisector_unbounded (u0 u1 : V3) (hne : u0 ≠ u1) :
    ¬ Bornology.IsBounded (p23Bis u0 u1) := by
  intro hb
  rw [Metric.isBounded_iff] at hb
  obtain ⟨K, hK⟩ := hb
  obtain ⟨w, hw0, hwdot⟩ := p23_exists_orthogonal u0 u1 hne
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hpn : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
  have hpm : p ∈ p23Bis u0 u1 := by
    show inner ℝ (p - u0) (u1 - u0) = _
    rw [hpn, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [show dist u0 u1 = ‖u1 - u0‖ from by
      rw [dist_comm u0 u1, dist_eq_norm, norm_sub_rev]]
    ring
  have hwne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hwpos : (0:ℝ) < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hwne)
  have hwdot' : inner ℝ w (u1 - u0) = 0 := by
    have : (u1 - u0 : V3) = (-1 : ℝ) • (u0 - u1) := by module
    rw [this, real_inner_smul_right, hwdot]
    ring
  have hmem : ∀ t : ℝ, p + t • w ∈ p23Bis u0 u1 := by
    intro t
    show inner ℝ (p + t • w - u0) (u1 - u0) = _
    have h1 : p + t • w - u0 = (p - u0) + t • w := by abel
    rw [h1, inner_add_left, real_inner_smul_left, hpm, hwdot']
    ring
  have hy : p + (((|K| : ℝ) + 1) / ‖w‖) • w ∈ p23Bis u0 u1 := hmem _
  have hdist : K < dist p (p + (((|K| : ℝ) + 1) / ‖w‖) • w) := by
    have h1 : dist p (p + (((|K| : ℝ) + 1) / ‖w‖) • w)
        = (((|K| : ℝ) + 1) / ‖w‖) * ‖w‖ := by
      rw [dist_eq_norm]
      have h2 : p - (p + (((|K| : ℝ) + 1) / ‖w‖) • w)
          = (-(((|K| : ℝ) + 1) / ‖w‖)) • w := by
        module
      have h4 : 0 < ((|K| : ℝ) + 1) / ‖w‖ :=
        div_pos (by linarith [abs_nonneg K]) hwpos
      have h3 : -((((|K| : ℝ) + 1) / ‖w‖) : ℝ) < 0 := by linarith
      rw [h2, norm_smul, Real.norm_eq_abs, abs_of_neg h3]
      ring
    rw [h1]
    field_simp
    linarith [le_abs_self K]
  exact absurd (hK hpm hy) (not_le.mpr hdist)

/-! ## B2: the midpoint bridge (HL Rogers.XYOFCGX, GRUTOTI.hl:561-575) -/

/-- the edge's own endpoint is NOT in the interface -/
private theorem p23_u0_notMem_voronoiList (V : Set V3) (u0 u1 : V3)
    (hu0 : u0 ∈ V) (hd : dist u0 u1 ≠ 0) : u0 ∉ voronoiList V [u0, u1] := by
  intro hx
  rw [p23_voronoiList_pair V u0 u1] at hx
  have h1 : dist u0 u1 ≤ dist u0 u0 := hx.2 u0 hu0
  rw [dist_self] at h1
  exact hd (le_antisymm h1 dist_nonneg)

/-- HL Rogers.XYOFCGX (strict form): every packing point other than the two
edge points is strictly farther from the edge midpoint than the half-length. -/
private theorem p23_midpoint_dist_gt (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) :
    ∀ w ∈ V, w ≠ u0 → w ≠ u1 →
      dist u0 u1 / 2 < dist (u0 + (1 / 2 : ℝ) • (u1 - u0)) w := by
  intro w hw hw0 hw1
  have hHL2 : hl [u0, u1] = dist u0 u1 / 2 := HL_2 u0 u1
  set d := dist u0 u1 with hddef
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hdpos : 0 ≤ d := dist_nonneg
  have hd8 : d ^ 2 < 8 := by
    rw [hHL2] at hhl
    have h1 : d < 2 * Real.sqrt 2 := by nlinarith
    have h2 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt (by norm_num : (0:ℝ) < 2))]
      norm_num
    nlinarith [hdpos, h1, h2]
  have apol : 4 * dist p w ^ 2
      = 2 * (dist w u0 ^ 2 + dist w u1 ^ 2) - d ^ 2 := by
    have h1 : p - w = (1 / 2 : ℝ) • ((u0 - w) + (u1 - w)) := by rw [hpdef]; module
    have h2 : dist p w = ‖(u0 - w) + (u1 - w)‖ / 2 := by
      rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
      field_simp
    have e1 : inner ℝ ((u0 - w) + (u1 - w)) ((u0 - w) + (u1 - w))
        = inner ℝ (u0 - w) (u0 - w) + 2 * inner ℝ (u0 - w) (u1 - w)
          + inner ℝ (u1 - w) (u1 - w) := by
      rw [inner_add_left, inner_add_right, inner_add_right,
        real_inner_comm (u1 - w) (u0 - w)]
      ring
    have e2 : d ^ 2 = inner ℝ (u0 - w) (u0 - w)
        - 2 * inner ℝ (u0 - w) (u1 - w) + inner ℝ (u1 - w) (u1 - w) := by
      have h3 : d = ‖(u0 - w) - (u1 - w)‖ := by
        rw [hddef, dist_eq_norm]
        congr 1
        module
      rw [h3, ← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    have n1 : ‖u0 - w‖ = dist w u0 := by rw [dist_eq_norm, norm_sub_rev]
    have n2 : ‖u1 - w‖ = dist w u1 := by rw [dist_eq_norm, norm_sub_rev]
    have n3 : ‖(u0 - w) + (u1 - w)‖ ^ 2
        = inner ℝ ((u0 - w) + (u1 - w)) ((u0 - w) + (u1 - w)) :=
      (real_inner_self_eq_norm_sq _).symm
    have h4 : dist p w ^ 2 = ‖(u0 - w) + (u1 - w)‖ ^ 2 / 4 := by
      rw [h2]
      field_simp
      ring
    rw [h4, n3, e1, e2]
    rw [real_inner_self_eq_norm_sq (u0 - w), real_inner_self_eq_norm_sq (u1 - w), n1, n2]
    field_simp
    linarith
  have hge0 : 2 ≤ dist w u0 := hp.dist_ge_two hw hu0 hw0
  have hge1 : 2 ≤ dist w u1 := hp.dist_ge_two hw hu1 hw1
  have hq0 : 4 ≤ dist w u0 ^ 2 := by nlinarith
  have hq1 : 4 ≤ dist w u1 ^ 2 := by nlinarith
  by_contra hcc
  push_neg at hcc
  have hdpw : (0:ℝ) ≤ dist p w := dist_nonneg
  have hsum : 0 ≤ d / 2 + dist p w := by linarith
  have hsq : (d / 2) ^ 2 = d ^ 2 / 4 := by ring
  have hs : dist p w ^ 2 < (d / 2) ^ 2 := by nlinarith [hcc, hsum, hdpw]
  linarith [apol, hq0, hq1, hd8, hs, hsq]

/-- HL Rogers.XYOFCGX: the edge midpoint is weakly closer to u0/u1 than every
other point of the packing (needs only `hl < √2` for the strictness). -/
private theorem p23_midpoint_mem_voronoiList (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) :
    u0 + (1 / 2 : ℝ) • (u1 - u0) ∈ voronoiList V [u0, u1] := by
  have hHL2 : hl [u0, u1] = dist u0 u1 / 2 := HL_2 u0 u1
  set d := dist u0 u1 with hddef
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hdpos : 0 ≤ d := dist_nonneg
  have hd8 : d ^ 2 < 8 := by
    rw [hHL2] at hhl
    have h1 : d < 2 * Real.sqrt 2 := by nlinarith
    have h2 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt (by norm_num : (0:ℝ) < 2))]
      norm_num
    nlinarith [hdpos, h1, h2]
  have hpu0 : dist p u0 = d / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [dist_eq_norm] at hddef
    rw [hddef, norm_sub_rev]
    ring
  have hpu1 : dist p u1 = d / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u1 = (1 / 2 : ℝ) • (u0 - u1) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [dist_eq_norm] at hddef
    rw [hddef, norm_sub_rev]
    ring
  have apol : ∀ w : V3, 4 * dist p w ^ 2
      = 2 * (dist w u0 ^ 2 + dist w u1 ^ 2) - d ^ 2 := by
    intro w
    have h1 : p - w = (1 / 2 : ℝ) • ((u0 - w) + (u1 - w)) := by rw [hpdef]; module
    have h2 : dist p w = ‖(u0 - w) + (u1 - w)‖ / 2 := by
      rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
      field_simp
    have e1 : inner ℝ ((u0 - w) + (u1 - w)) ((u0 - w) + (u1 - w))
        = inner ℝ (u0 - w) (u0 - w) + 2 * inner ℝ (u0 - w) (u1 - w)
          + inner ℝ (u1 - w) (u1 - w) := by
      rw [inner_add_left, inner_add_right, inner_add_right,
        real_inner_comm (u1 - w) (u0 - w)]
      ring
    have e2 : d ^ 2 = inner ℝ (u0 - w) (u0 - w)
        - 2 * inner ℝ (u0 - w) (u1 - w) + inner ℝ (u1 - w) (u1 - w) := by
      have h3 : d = ‖(u0 - w) - (u1 - w)‖ := by
        rw [hddef, dist_eq_norm]
        congr 1
        module
      rw [h3, ← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    have n1 : ‖u0 - w‖ = dist w u0 := by rw [dist_eq_norm, norm_sub_rev]
    have n2 : ‖u1 - w‖ = dist w u1 := by rw [dist_eq_norm, norm_sub_rev]
    have n3 : ‖(u0 - w) + (u1 - w)‖ ^ 2
        = inner ℝ ((u0 - w) + (u1 - w)) ((u0 - w) + (u1 - w)) :=
      (real_inner_self_eq_norm_sq _).symm
    have h4 : dist p w ^ 2 = ‖(u0 - w) + (u1 - w)‖ ^ 2 / 4 := by
      rw [h2]
      field_simp
      ring
    rw [h4, n3, e1, e2]
    rw [real_inner_self_eq_norm_sq (u0 - w), real_inner_self_eq_norm_sq (u1 - w), n1, n2]
    field_simp
    linarith
  have key : ∀ w ∈ V, w ≠ u0 → w ≠ u1 → d / 2 ≤ dist p w :=
    fun w hw hw0 hw1 => le_of_lt (p23_midpoint_dist_gt V u0 u1 hp hu0 hu1 hne hhl w hw hw0 hw1)
  rw [p23_voronoiList_pair V u0 u1]
  constructor
  · rw [voronoiClosed, Set.mem_setOf_eq]
    intro w hw
    by_cases hw0 : w = u0
    · subst hw0
      exact le_refl _
    by_cases hw1 : w = u1
    · subst hw1
      rw [hpu0, hpu1]
    · rw [hpu0]
      exact key w hw hw0 hw1
  · rw [voronoiClosed, Set.mem_setOf_eq]
    intro w hw
    by_cases hw0 : w = u0
    · subst hw0
      rw [hpu1, hpu0]
    by_cases hw1 : w = u1
    · subst hw1
      exact le_refl _
    · rw [hpu1]
      exact key w hw hw0 hw1



/-! ## B1 conclusion: the critical radius -/

/-- Pythagoras on the bisector: `‖z - u0‖² = ‖z - p‖² + (d/2)²` for `z` on the
bisector and `p` the edge midpoint. -/
private theorem p23_bis_pythagoras (u0 u1 z : V3) (hz : z ∈ p23Bis u0 u1) :
    dist u0 z ^ 2 = ‖z - (u0 + (1 / 2 : ℝ) • (u1 - u0))‖ ^ 2 + (dist u0 u1 / 2) ^ 2 := by
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hpn : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
  have hbis : z ∈ p23Bis u0 u1 := hz
  rw [p23Bis, Set.mem_setOf_eq] at hbis
  have hzdot : inner ℝ (z - p) (u1 - u0) = 0 := by
    have h1 : z - p = (z - u0) - (p - u0) := by abel
    have h2 : inner ℝ (p - u0) (u1 - u0) = dist u0 u1 ^ 2 / 2 := by
      rw [hpn, real_inner_smul_left, real_inner_self_eq_norm_sq]
      rw [show dist u0 u1 = ‖u1 - u0‖ from by
        rw [dist_comm u0 u1, dist_eq_norm, norm_sub_rev]]
      ring
    rw [h1, inner_sub_left, hbis, h2]
    ring
  have h1 : z - u0 = (z - p) + (p - u0) := by abel
  have h2 : dist u0 z = ‖z - u0‖ := by rw [dist_eq_norm, norm_sub_rev]
  have h3 : ‖p - u0‖ = dist u0 u1 / 2 := by
    rw [hpn, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show dist u0 u1 = ‖u1 - u0‖ from by
      rw [dist_comm u0 u1, dist_eq_norm, norm_sub_rev]]
    ring
  have h4 : inner ℝ (z - p) (p - u0) = 0 := by
    rw [hpn, real_inner_smul_right, hzdot]
    ring
  have h5 : dist u0 z ^ 2
      = ‖z - p‖ ^ 2 + 2 * inner ℝ (z - p) (p - u0) + ‖p - u0‖ ^ 2 := by
    have e0 : inner ℝ (z - u0) (z - u0)
        = inner ℝ (z - p) (z - p) + 2 * inner ℝ (z - p) (p - u0)
          + inner ℝ (p - u0) (p - u0) := by
      have hz1 : z - u0 = (z - p) + (p - u0) := by abel
      rw [hz1, inner_add_left, inner_add_right, inner_add_right,
        real_inner_comm (p - u0) (z - p)]
      ring
    rw [h2, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, e0, h4]
  calc dist u0 z ^ 2
      = ‖z - p‖ ^ 2 + 2 * inner ℝ (z - p) (p - u0) + ‖p - u0‖ ^ 2 := h5
    _ = ‖z - p‖ ^ 2 + (dist u0 u1 / 2) ^ 2 := by rw [h4, h3]; ring

/-- translated form of `Packing.finite_inter_ball` (Statement.lean, centered
at 0) -/
private theorem p23_finite_inter_ball (V : Set V3) (hp : Packing V) (v : V3) (r : ℝ) :
    (V ∩ Metric.ball v r).Finite := by
  have hp' : Packing ((fun x : V3 => x - v) '' V) := by
    intro u hu w hw hlt
    obtain ⟨u, huV, rfl⟩ := hu
    obtain ⟨w, hwV, rfl⟩ := hw
    refine congrArg (fun x => x - v) (hp u huV w hwV ?_)
    rw [dist_eq_norm]
    have hab : (u - v) - (w - v) = u - w := by abel
    rw [← hab, ← dist_eq_norm]
    exact hlt
  have hfin : (((fun x : V3 => x - v) '' V) ∩ Metric.ball 0 r).Finite :=
    Packing.finite_inter_ball hp' r
  have hsub : V ∩ Metric.ball v r
      ⊆ (fun x : V3 => v + x) '' (((fun x : V3 => x - v) '' V) ∩ Metric.ball 0 r) := by
    rintro x ⟨hxV, hxb⟩
    refine ⟨x - v, ⟨Set.mem_image_of_mem _ hxV, ?_⟩, by abel⟩
    rw [Metric.mem_ball] at hxb ⊢
    rw [dist_zero_right]
    rw [dist_comm, dist_eq_norm, norm_sub_rev] at hxb
    exact hxb
  exact ((hfin.image (fun x : V3 => v + x))).subset hsub

/-- B1 conclusion (HL GRUTOTI.hl:253-590): a critical radius `δ` strictly above
the half-length such that every bisector point closer than `δ` to `u0` lies in
the interface `S = voronoiList V [u0, u1]`.

Instead of HL's `S2 = S1 \ relative_interior S` (whose closedness needs the
aff-dim equality `aff hull S = S1`), we build the explicit relative
neighbourhood `S' = S1 ∩ ball(p, d₀) ⊆ S` from HL's B2 nearest-point selection
(`a'` in `V ∩ ball(p,8) \ {u0,u1}`, `d₀ = (dist(p,a') - d/2)/4`) and minimize
over the closed set `S1 ∩ (ball(p,d₀))ᶜ`. -/
private theorem p23_region_exists_delta (V : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) :
    ∃ δ : ℝ, dist u0 u1 / 2 < δ ∧ ∀ y ∈ p23Bis u0 u1, dist u0 y < δ →
      y ∈ voronoiList V [u0, u1] := by
  set d := dist u0 u1 with hddef
  set p : V3 := u0 + (1 / 2 : ℝ) • (u1 - u0) with hpdef
  have hdpos : 0 < d := dist_pos.mpr (fun hcc => hne hcc)
  have hdp2 : 0 < d / 2 := by linarith
  have hdp8 : d / 2 < 2 := by
    have h1 : hl [u0, u1] = d / 2 := HL_2 u0 u1
    have h2 : hl [u0, u1] < Real.sqrt 2 := hhl
    have h3 : Real.sqrt 2 < 2 := by
      have h3a : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h3b : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      by_contra h4
      push_neg at h4
      nlinarith [h3a, h3b, h4]
    rw [h1] at h2
    linarith
  -- the distances from p to the two edge points are d/2
  have hu0p : dist p u0 = d / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u0 = (1 / 2 : ℝ) • (u1 - u0) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show d = ‖u1 - u0‖ from by rw [hddef, dist_eq_norm, norm_sub_rev]]
    ring
  have hu1p : dist p u1 = d / 2 := by
    rw [dist_eq_norm]
    have h1 : p - u1 = (1 / 2 : ℝ) • (u0 - u1) := by rw [hpdef]; module
    rw [h1, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    rw [show d = ‖u0 - u1‖ from by rw [hddef, dist_eq_norm]]
    ring
  -- the strict nearest-point bound (XYOFCGX)
  have hgt := p23_midpoint_dist_gt V u0 u1 hp hu0 hu1 hne hhl
  -- B2: finite nonempty set of non-edge packing points inside ball(p,8)
  set A : Set V3 := (V ∩ Metric.ball p 8) \ {u0, u1} with hAdef
  have hAfin : A.Finite := (p23_finite_inter_ball V hp p 8).diff (t := {u0, u1})
  have hAne : A.Nonempty := by
    obtain ⟨y0, hy0⟩ : ∃ y0 : V3, dist p y0 = 4 :=
      ⟨p + (4 / (dist p u0)) • (u0 - p), by
        rw [dist_eq_norm]
        have h1 : p - (p + (4 / (dist p u0)) • (u0 - p))
            = -((4 / (dist p u0)) • (u0 - p)) := by abel
        have hnup : ‖u0 - p‖ = dist p u0 := by
          rw [← dist_eq_norm]
          exact dist_comm u0 p
        have hpu0pos : (0:ℝ) < dist p u0 := by rw [hu0p]; linarith
        have hq4 : (0:ℝ) < 4 / dist p u0 := div_pos (by norm_num) hpu0pos
        rw [h1, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_pos hq4, hnup, hu0p]
        field_simp⟩
    obtain ⟨z', hz'V, hz'd⟩ := hs y0
    have hz'8 : dist p z' < 8 := by
      have h1 : dist p z' ≤ dist p y0 + dist y0 z' := dist_triangle p y0 z'
      rw [hy0] at h1
      linarith
    have hz'0 : z' ≠ u0 := by
      intro hcc
      have h1 : dist p y0 ≤ dist p u0 + dist u0 y0 := by
        rw [← hcc]
        exact dist_triangle p z' y0
      rw [hy0, hu0p] at h1
      have h2 : dist u0 y0 < 2 := by rw [← hcc, dist_comm]; exact hz'd
      linarith [h2, hdp8]
    have hz'1 : z' ≠ u1 := by
      intro hcc
      have h1 : dist p y0 ≤ dist p u1 + dist u1 y0 := by
        rw [← hcc]
        exact dist_triangle p z' y0
      rw [hy0, hu1p] at h1
      have h2 : dist u1 y0 < 2 := by rw [← hcc, dist_comm]; exact hz'd
      linarith [h2, hdp8]
    refine ⟨z', ⟨⟨hz'V, ?_⟩, by simp [hz'0, hz'1]⟩⟩
    rw [Metric.mem_ball, dist_comm]
    exact hz'8
  -- a' := the nearest point of A
  obtain ⟨a', ha'A, hamin⟩ :=
    Set.exists_min_image A (fun w : V3 => dist p w) hAfin hAne
  have ha'V : a' ∈ V := ha'A.1.1
  have ha'ball : dist p a' < 8 := by
    have h5 : dist a' p < 8 := Metric.mem_ball.mp ha'A.1.2
    rw [dist_comm]
    exact h5
  have ha'0 : a' ≠ u0 := fun hcc => ha'A.2 (by simp [hcc])
  have ha'1 : a' ≠ u1 := fun hcc => ha'A.2 (by simp [hcc])
  have hapos : d / 2 < dist p a' := hgt a' ha'V ha'0 ha'1
  set d0 := (dist p a' - d / 2) / 4 with hd0def
  have hd00 : 0 < d0 := by linarith
  have hapos4 : dist p a' = d / 2 + 4 * d0 := by rw [hd0def]; linarith
  -- S' = p23Bis ∩ ball(p,d0) is inside the interface
  have hS' : ∀ x ∈ p23Bis u0 u1, dist p x < d0 → x ∈ voronoiList V [u0, u1] := by
    intro x hxb hxd
    have hdist : dist x u0 = dist x u1 := (p23_dist_eq_bis u0 u1 x).mpr hxb
    rw [p23_voronoiList_pair V u0 u1]
    constructor
    · rw [voronoiClosed, Set.mem_setOf_eq]
      intro w hw
      by_cases hw0 : w = u0
      · subst hw0
        exact le_refl _
      by_cases hw1 : w = u1
      · subst hw1
        rw [hdist]
      · have hchain1 : dist p w - dist p x ≤ dist x w := by
          have := dist_triangle p x w
          linarith
        have hwge : dist p a' ≤ dist p w := by
          by_cases hwb : w ∈ Metric.ball p 8
          · have hwA : w ∈ A := by
              rw [hAdef, Set.mem_sdiff]
              exact ⟨⟨hw, hwb⟩, by simp [hw0, hw1]⟩
            exact hamin w hwA
          · have h1 : ¬ dist p w < 8 := fun hcc =>
              hwb (by rw [Metric.mem_ball, dist_comm]; exact hcc)
            have h2 : dist p w ≥ 8 := le_of_not_gt h1
            linarith
        have h2 : dist x u0 ≤ dist p x + d / 2 := by
          have h5b : dist x u0 ≤ dist x p + dist p u0 := dist_triangle x p u0
          rw [hu0p, dist_comm x p] at h5b
          linarith
        have h3 : dist x u0 < dist x w := by
          have h4 : dist p a' - d0 = d / 2 + 3 * d0 := by rw [hapos4]; linarith
          have h5 : dist p a' - dist p x > dist p a' - d0 := by linarith
          have h6 : dist x u0 < d / 2 + d0 := by linarith
          linarith
        linarith
    · rw [voronoiClosed, Set.mem_setOf_eq]
      intro w hw
      by_cases hw0 : w = u0
      · subst hw0
        rw [hdist]
      by_cases hw1 : w = u1
      · subst hw1
        exact le_refl _
      · have hchain1 : dist p w - dist p x ≤ dist x w := by
          have := dist_triangle p x w
          linarith
        have hwge : dist p a' ≤ dist p w := by
          by_cases hwb : w ∈ Metric.ball p 8
          · have hwA : w ∈ A := by
              rw [hAdef, Set.mem_sdiff]
              exact ⟨⟨hw, hwb⟩, by simp [hw0, hw1]⟩
            exact hamin w hwA
          · have h1 : ¬ dist p w < 8 := fun hcc =>
              hwb (by rw [Metric.mem_ball, dist_comm]; exact hcc)
            have h2 : dist p w ≥ 8 := le_of_not_gt h1
            linarith
        have h2 : dist x u1 ≤ dist p x + d / 2 := by
          have h5b : dist x u1 ≤ dist x p + dist p u1 := dist_triangle x p u1
          rw [hu1p, dist_comm x p] at h5b
          linarith
        have h3 : dist x u1 < dist x w := by
          have h4 : dist p a' - d0 = d / 2 + 3 * d0 := by rw [hapos4]; linarith
          linarith
        linarith
  -- minimize dist u0 · over the closed set S2 = p23Bis ∩ ball(p,d0)ᶜ
  have hS2cl : IsClosed (p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ) :=
    (p23_bis_closed u0 u1).inter Metric.isOpen_ball.isClosed_compl
  have hS2ne : (p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ).Nonempty := by
    by_contra hcon
    have hsub : p23Bis u0 u1 ⊆ Metric.ball p d0 := by
      intro x hx
      by_contra hx2
      rw [Metric.mem_ball] at hx2
      have hxmem : x ∈ p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ := ⟨hx, hx2⟩
      exact hcon ⟨x, hxmem⟩
    exact p23_bisector_unbounded u0 u1 hne
      ((Metric.isBounded_ball (x := p) (r := d0)).subset hsub)
  obtain ⟨z, hzS2, hdz⟩ := hS2cl.exists_infDist_eq_dist hS2ne u0
  obtain ⟨hzbis, hzball⟩ := hzS2
  rw [Set.mem_compl_iff, Metric.mem_ball] at hzball
  push_neg at hzball
  have hzp : z ≠ p := by
    intro hcc
    rw [hcc, dist_self] at hzball
    linarith
  have hpy := p23_bis_pythagoras u0 u1 z hzbis
  have hd2 : (d / 2) ^ 2 < dist u0 z ^ 2 := by
    rw [hpy]
    have hnz : ‖z - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzp)
    have hpos : 0 < ‖z - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnz)
    nlinarith [hpos]
  refine ⟨dist u0 z, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have hx0 : (0:ℝ) ≤ dist u0 z := dist_nonneg
    have hs2 : 0 ≤ d / 2 + dist u0 z := by linarith
    nlinarith [hd2, hcon, hs2, hx0]
  · intro y hyb hlt
    have hyin : y ∈ Metric.ball p d0 := by
      by_contra hyball
      have hy2 : y ∈ p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ := ⟨hyb, hyball⟩
      have hle := Metric.infDist_le_dist_of_mem (s := p23Bis u0 u1 ∩ (Metric.ball p d0)ᶜ)
        (x := u0) (y := y) hy2
      rw [hdz] at hle
      exact absurd hlt (not_lt.mpr hle)
    have hlt2 : dist p y < d0 := by
      have h5c : dist y p < d0 := Metric.mem_ball.mp hyin
      rw [dist_comm] at h5c
      exact h5c
    exact hS' y hyb hlt2

/-! ## B3+B4: the cone over the interface contains a small rcone
(HL GRUTOTI.hl:590-1143) -/

/-- B3+B4 (HL GRUTOTI.hl:590-1143): there is a cosine-threshold `c ∈ (0,1)`
with `rconeGt u0 u1 c` inside the cone from `u0` over the interface `S`
(`affGeAlt {u0} S`) and inside `rconeGt u0 u1 (hl/√2)`. -/
private theorem p23_region_exists_c (V : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      rconeGt u0 u1 c ⊆ affGeAlt {u0} (voronoiList V [u0, u1]) ∧
      rconeGt u0 u1 c ⊆ rconeGt u0 u1 (hl [u0, u1] / Real.sqrt 2) := by
  obtain ⟨δ, hδcrit, hcrit⟩ := p23_region_exists_delta V u0 u1 hs hp hu0 hu1 hne hhl
  have hdpos : 0 < dist u0 u1 := dist_pos.mpr (fun hcc => hne hcc)
  have hδ0 : 0 < δ := lt_of_le_of_lt (by positivity) hδcrit
  -- the provisional threshold b = (d/2)/δ ∈ (0,1)
  set b := dist u0 u1 / 2 / δ with hbdef
  have hb0 : 0 < b := div_pos (by linarith) hδ0
  have hbne : b ≠ 0 := ne_of_gt hb0
  have hb1 : b < 1 := (div_lt_one hδ0).mpr hδcrit
  have hbkey : dist u0 u1 ^ 2 / 2 = dist u0 u1 * b * δ := by
    have hδne : δ ≠ 0 := ne_of_gt hδ0
    have h1b : b * δ = dist u0 u1 / 2 := by
      rw [hbdef]
      exact div_mul_cancel₀ _ hδne
    rw [mul_assoc, h1b]
    ring
  have hbincl : ∀ x, x ∈ rconeGt u0 u1 b →
      affGeAlt {u0} (voronoiList V [u0, u1]) x := by
    intro x hx
    rw [rconeGt, Set.mem_setOf_eq] at hx
    rw [dist_comm u1 u0] at hx
    have hx2 : inner ℝ (x - u0) (u1 - u0) > dist x u0 * (dist u0 u1 * b) := by
      rw [inner_eq_dot, ← mul_assoc]
      exact hx
    have hxn : x ≠ u0 := by
      intro hcc
      rw [hcc] at hx2
      simp at hx2
    have hD0 : 0 < dist u0 u1 := dist_pos.mpr (fun hcc => hne hcc)
    have hDne : dist u0 u1 ≠ 0 := fun hcc => hne (dist_eq_zero.mp hcc)
    have htne : dist x u0 ≠ 0 := fun hcc => hxn (dist_eq_zero.mp hcc)
    have ht0 : 0 < dist x u0 := lt_of_le_of_ne dist_nonneg (Ne.symm htne)
    have htp : 0 < (dist x u0)⁻¹ := inv_pos.mpr ht0
    obtain ⟨ww, hwdef⟩ : ∃ ww : V3, ww = (dist x u0)⁻¹ • (x - u0) := ⟨_, rfl⟩
    have hwn : ‖ww‖ = 1 := by
      rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos htp]
      rw [← dist_eq_norm, inv_mul_cancel₀ htne]
    have hwx : x - u0 = dist x u0 • ww := by
      rw [hwdef, smul_smul, mul_inv_cancel₀ htne, one_smul]
    have h1 : inner ℝ (x - u0) (u1 - u0)
        = dist x u0 * inner ℝ ww (u1 - u0) := by
      rw [hwx, real_inner_smul_left]
    have hwdot : dist u0 u1 * b < inner ℝ ww (u1 - u0) := by
      have h3 : dist x u0 * (dist u0 u1 * b)
          < dist x u0 * inner ℝ ww (u1 - u0) := by
        rw [← h1]
        exact hx2
      exact lt_of_mul_lt_mul_left h3 (le_of_lt ht0)
    have hq1 : 0 < dist u0 u1 * b := mul_pos hD0 hb0
    have hqpos : 0 < inner ℝ ww (u1 - u0) := by linarith
    have hqne : inner ℝ ww (u1 - u0) ≠ 0 := ne_of_gt hqpos
    -- the hit point of the ray u0 → x with the bisector hyperplane
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ,
        s = (dist u0 u1 ^ 2 / 2) / inner ℝ ww (u1 - u0) := ⟨_, rfl⟩
    have hs0 : 0 < s := by
      rw [hsdef]
      exact div_pos (div_pos (sq_pos_of_ne_zero hDne) (by norm_num)) hqpos
    obtain ⟨y, hydef⟩ : ∃ y : V3, y = u0 + s • ww := ⟨_, rfl⟩
    have hywu : y - u0 = s • ww := by rw [hydef]; module
    have hybis : y ∈ p23Bis u0 u1 := by
      show inner ℝ (y - u0) (u1 - u0) = _
      rw [hywu, real_inner_smul_left, hsdef]
      field_simp
    have hdy : dist u0 y = s := by
      rw [dist_eq_norm, norm_sub_rev, hywu, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs0, hwn, mul_one]
    have hyne : y ≠ u0 := by
      intro hcc
      rw [hcc, dist_self] at hdy
      exact absurd hdy.symm (ne_of_gt hs0)
    have hsδ : s < δ := by
      have h8' : s * inner ℝ ww (u1 - u0) = dist u0 u1 * b * δ := by
        rw [hsdef, div_mul_cancel₀ _ hqne]
        exact hbkey
      have h9 : dist u0 u1 * b * δ < inner ℝ ww (u1 - u0) * δ :=
        mul_lt_mul_of_pos_right hwdot hδ0
      have h10 : inner ℝ ww (u1 - u0) * s < inner ℝ ww (u1 - u0) * δ := by
        rw [mul_comm (inner ℝ ww (u1 - u0)) s, h8']
        linarith
      exact lt_of_mul_lt_mul_left h10 hqpos.le
    have hyS : y ∈ voronoiList V [u0, u1] := hcrit y hybis (by rw [hdy]; exact hsδ)
    -- assemble the affGeAlt witness
    have hsne : s ≠ 0 := ne_of_gt hs0
    obtain ⟨hh, hhdef⟩ : ∃ hh : ℝ, hh = dist x u0 / s := ⟨_, rfl⟩
    have hh0 : 0 < hh := by rw [hhdef]; exact div_pos ht0 hs0
    have key : x - u0 = hh • (y - u0) := by
      rw [hywu, hhdef, smul_smul, div_mul_cancel₀ _ hsne]
      exact hwx
    have hxeq : x = (1 - hh) • u0 + hh • y := by
      have e1 : x = u0 + (x - u0) := (add_sub_cancel u0 x).symm
      rw [e1, key]
      module
    refine ⟨fun v => if v = u0 then 1 - hh else if v = y then hh else 0, {y},
      Set.finite_singleton y, ?_, ?_, ?_, ?_⟩
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hyS
    · have hfin : (({u0} ∪ {y} : Set V3)).Finite := by simp
      have htofin : hfin.toFinset = ({u0, y} : Finset V3) := by
        ext z
        simp
        tauto
      rw [linCombo, dif_pos hfin, htofin,
        Finset.sum_insert (by intro hcc; rw [Finset.mem_singleton] at hcc; exact hyne hcc.symm), Finset.sum_singleton]
      have hfu0 : (if u0 = u0 then 1 - hh else if u0 = y then hh else 0) = 1 - hh := by
        simp [hyne]
      have hfy : (if y = u0 then 1 - hh else if y = y then hh else 0) = hh := by
        simp [hyne]
      rw [hfu0, hfy]
      exact hxeq
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp [hyne, hh0.le]
    · have hfin : (({u0} ∪ {y} : Set V3)).Finite := by simp
      have htofin : hfin.toFinset = ({u0, y} : Finset V3) := by
        ext z
        simp
        tauto
      rw [setSum, dif_pos hfin, htofin,
        Finset.sum_insert (by intro hcc; rw [Finset.mem_singleton] at hcc; exact hyne hcc.symm), Finset.sum_singleton]
      have hfu0 : (if u0 = u0 then 1 - hh else if u0 = y then hh else 0) = 1 - hh := by
        simp [hyne]
      have hfy : (if y = u0 then 1 - hh else if y = y then hh else 0) = hh := by
        simp [hyne]
      rw [hfu0, hfy]
      ring
  -- B4: raise the threshold to c = max b (hl/√2)
  have hhlpos : 0 < hl [u0, u1] := by rw [HL_2]; linarith
  have hhl1 : hl [u0, u1] / Real.sqrt 2 < 1 :=
    (div_lt_one (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))).mpr hhl
  refine ⟨max b (hl [u0, u1] / Real.sqrt 2), lt_max_of_lt_left hb0, max_lt hb1 hhl1, ?_, ?_⟩
  · intro x hx
    exact hbincl _ (RCONE_GT_SUBSET u0 u1 b _ (le_max_left _ _) hx)
  · intro x hx
    exact RCONE_GT_SUBSET u0 u1 (hl [u0, u1] / Real.sqrt 2) _ (le_max_right _ _) hx

/-! ## GT-4b lane: B5-B7 region-block remainder (2026-09-30, zero sorry)

HL GRUTOTI.hl:1144-2636: the rogers/mcell cover kit (B5), the P1-P4 extremal
data (B6) and the c/r/d assembly with the mcell cover (B7). Design notes:
* the family `p23Fam V u0 u1` of `barV V 3` lists truncating to `[u0,u1]` is
  finite (lists drawn from `V ∩ ball u0 4`, which is finite by saturation);
* `C ⊆ ⋃₀ rogers-family` goes through the `affGeAlt` witness: a negative
  `f u0` weight would force `‖x - u0‖ ≥ t·(d/2) ≥ t > 1` (Pythagoras on the
  bisector + the packing bound `d ≥ 2`), so the witness is a genuine convex
  segment point `x = (1-t)•u0 + t•w`, `w ∈ S`, and segment-points land in
  `rogers V vl` for a family member (`u0 = ω0` and `S` is the rogers union by
  `grutoti_vor_cover`);
* the k = 0/1 cells miss `C` (`mcell0` lives outside `ball u0 √2`, `mcell1`
  outside the `hl/√2` cone), and `AJRIPQN` (PA17; upstream sorry) pins
  `X = mcell i V vl0`;
* the B6 bounds: `f1 ul > 0`/`f2 ul > 0` kill `u0` in the facet planes
  (else the whole cell sits in a plane — null against `¬null (mcell ∩ C)`),
  and `f3 ul < 1`/`f4 ul < 1` come from the C-S equality case: equality
  collinear forces an endpoint of the segment into the 2-flat of the other
  three points, again nulling the cell;
* `r = min (1/2) (min r1 r2)` replaces HL's `min 1 (min r1 r2)`: the Lean
  `grutotiConicCap` uses a CLOSED ball, so `D ⊆ C` needs `r < 1` strictly;
  the frozen region statement only asks `0 < r ≤ 1` and the cell-volume
  lane only needs `r ≤ min r1 r2`, both preserved.
Upstream sorry debt consumed: PA17 `AJRIPQN` (sorried there), PA12
`VORONOI_LIST_3_SINGLETON_EXPLICIT` (shim). No new `sorry` in this file.
-/

/-! ### B5 kit: the truncation family is finite -/

/-- the `barV V 3` lists truncating to `[u0, u1]` (HL `Ss`) -/
private def p23Fam (V : Set V3) (u0 u1 : V3) : Set (List V3) :=
  {vl | barV V 3 vl ∧ truncateSimplex 1 vl = [u0, u1]}

/-- HOL `BARV_3_IMP_FINITE_lemma1` (QZYZMJC.hl:62; private copy — the PA15
original is private): two list points of a `barV V 3` simplex over a
saturated packing are less than `4` apart. -/
private theorem p23_barV3ImpFinite1 {V : Set V3} {ul : List V3} {u v : V3}
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (huv : {u, v} ⊆ setOfList ul) : dist u v < 4 := by
  obtain ⟨a, ha1, _ha2, _ha3⟩ := VORONOI_LIST_3_SINGLETON_EXPLICIT V ul hp hs hb
  have hamem : a ∈ voronoiList V ul := by rw [ha1]; exact rfl
  have key : ∀ s ∈ setOfList ul, dist a s < 2 := by
    intro s hsmem
    obtain ⟨y, hyV, hyd⟩ := hs a
    have hmem : a ∈ ⋂₀ {voronoiClosed V w | w ∈ setOfList ul} := hamem
    have has : a ∈ voronoiClosed V s :=
      Set.mem_sInter.mp hmem (voronoiClosed V s) ⟨s, hsmem, rfl⟩
    have h1 : dist a s ≤ dist a y := by
      simpa only [voronoiClosed, Set.mem_setOf_eq] using has y hyV
    calc dist a s ≤ dist a y := h1
      _ < 2 := hyd
  have hdu : dist a u < 2 := key u (huv (by simp))
  have hdv : dist a v < 2 := key v (huv (by simp))
  calc dist u v ≤ dist u a + dist a v := dist_triangle u a v
    _ < 4 := by rw [dist_comm u a]; linarith

/-- HOL `BARV_3_IMP_FINITE_lemma2` (QZYZMJC.hl:104; private copy): the whole
list sits in the radius-`4` ball around any of its points. -/
private theorem p23_barV3ImpFinite2 {V : Set V3} {ul : List V3} {v : V3}
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hv : v ∈ setOfList ul) :
    setOfList ul ⊆ Metric.ball v 4 := by
  intro s hsmem
  refine p23_barV3ImpFinite1 hp hs hb ?_
  intro x hx
  rcases (by simpa using hx : x = s ∨ x = v) with hx1 | hx1
  · rw [hx1]
    exact hsmem
  · rw [hx1]
    exact hv

/-- HL B5 (GRUTOTI.hl:1334-1402): the truncation family is finite — its
members are 4-lists drawn from `V ∩ ball u0 4`, finite by saturation. -/
private theorem p23_family_finite (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hs : saturated V) : (p23Fam V u0 u1).Finite := by
  have hf : (V ∩ Metric.ball u0 4).Finite := p23_finite_inter_ball V hp u0 4
  have hprod : ((V ∩ Metric.ball u0 4) ×ˢ ((V ∩ Metric.ball u0 4) ×ˢ
      ((V ∩ Metric.ball u0 4) ×ˢ (V ∩ Metric.ball u0 4)))).Finite :=
    hf.prod (hf.prod (hf.prod hf))
  have himg : Set.Finite ((fun p : V3 × (V3 × (V3 × V3)) =>
      [p.1, p.2.1, p.2.2.1, p.2.2.2]) '' ((V ∩ Metric.ball u0 4) ×ˢ ((V ∩ Metric.ball u0 4) ×ˢ
      ((V ∩ Metric.ball u0 4) ×ˢ (V ∩ Metric.ball u0 4))))) := Set.Finite.image _ hprod
  refine himg.subset ?_
  intro vl hvl
  obtain ⟨hb, htr⟩ := hvl
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V vl hb
  subst hv
  have hsub : setOfList [v0, v1, v2, v3] ⊆ Metric.ball v0 4 :=
    p23_barV3ImpFinite2 hp hs hb (by simp [setOfList])
  have hVsub : setOfList [v0, v1, v2, v3] ⊆ V := BARV_SUBSET V 3 _ hb
  have hmem : ∀ i : V3, i ∈ setOfList [v0, v1, v2, v3] →
      i ∈ V ∩ Metric.ball u0 4 := by
    intro i hi
    have hvi : i ∈ Metric.ball v0 4 := hsub hi
    have hv0 : v0 = u0 := by
      have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
        (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
      rw [h1] at htr
      exact (List.cons.injEq v0 [v1] u0 [u1] |>.mp htr).1
    rw [hv0] at hvi
    exact ⟨hVsub hi, hvi⟩
  refine ⟨(v0, (v1, (v2, v3))), ?_, rfl⟩
  simp only [Set.mem_prod, Set.mem_inter_iff]
  exact ⟨hmem v0 (by simp [setOfList]), ⟨hmem v1 (by simp [setOfList]),
    ⟨hmem v2 (by simp [setOfList]), hmem v3 (by simp [setOfList])⟩⟩⟩

/-- the head of a family list is `u0` -/
private theorem p23_hdV_eq_u0 {V : Set V3} {u0 u1 : V3} {vl : List V3}
    (hvl : vl ∈ p23Fam V u0 u1) : hdV vl = u0 := by
  obtain ⟨hb, htr⟩ := hvl
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V vl hb
  subst hv
  have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
  rw [h1] at htr
  exact (List.cons.injEq v0 [v1] u0 [u1] |>.mp htr).1

/-- the second entry of a family list is `u1` -/
private theorem p23_hdTail_eq_u1 {V : Set V3} {u0 u1 : V3} {vl : List V3}
    (hvl : vl ∈ p23Fam V u0 u1) : hdV vl.tail = u1 := by
  obtain ⟨hb, htr⟩ := hvl
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V vl hb
  subst hv
  have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
  rw [h1] at htr
  exact (List.cons.injEq v1 [] u1 [] |>.mp
    (List.cons.injEq v0 [v1] u0 [u1] |>.mp htr).2).1

/-- the `mcell` dispatch folds into the `≤ 4` range -/
private theorem p23_mcell_reduce (i : ℕ) (V : Set V3) (ul : List V3) :
    mcell i V ul = mcell (min i 4) V ul := by
  rcases Nat.lt_or_ge i 4 with hlt | hle
  · rw [min_eq_left (le_of_lt hlt)]
  · rw [min_eq_right hle, (MCELL_EXPLICIT i V ul).2.2.2.2 hle,
      (MCELL_EXPLICIT 4 V ul).2.2.2.2 (Nat.le_refl 4)]

/-! ### B5 kit: the interface is convex and the `affGeAlt` witness is a
segment point -/

/-- the closed Voronoi cells are convex (halfspace form of the two-distance
comparison) -/
private theorem p23_voronoiClosed_convex (V : Set V3) (w : V3) :
    Convex ℝ (voronoiClosed V w) := by
  intro x hx y hy a b ha0 hb0 hab
  simp only [voronoiClosed, Set.mem_setOf_eq] at hx hy ⊢
  intro z hz
  have key : ∀ p : V3, dist p w ≤ dist p z ↔
      2 * (inner ℝ p (z - w)) ≤ ‖z‖ ^ 2 - ‖w‖ ^ 2 := by
    intro p
    have expand : ∀ p q : V3, inner ℝ (p - q) (p - q)
        = inner ℝ p p - 2 * inner ℝ p q + inner ℝ q q := by
      intro p q
      rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm q p]
      ring
    have hiff : (dist p w) ^ 2 ≤ (dist p z) ^ 2 ↔ dist p w ≤ dist p z :=
      pow_le_pow_iff_left₀ (a := dist p w) (b := dist p z) (n := 2)
        dist_nonneg dist_nonneg two_ne_zero
    rw [← hiff, dist_eq_norm, dist_eq_norm]
    repeat rw [← real_inner_self_eq_norm_sq]
    rw [expand p w, expand p z]
    have hsplit : inner ℝ p (z - w) = inner ℝ p z - inner ℝ p w := by
      rw [inner_sub_right]
    constructor
    · intro hle
      linarith
    · intro hle
      linarith
  have hw := (key x).mp (hx z hz)
  have hy2 := (key y).mp (hy z hz)
  have hcx : inner ℝ (a • x + b • y) (z - w)
      = a * (inner ℝ x (z - w)) + b * (inner ℝ y (z - w)) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [key, hcx]
  have h1 : a * (2 * inner ℝ x (z - w)) ≤ a * (‖z‖ ^ 2 - ‖w‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hw ha0
  have h2 : b * (2 * inner ℝ y (z - w)) ≤ b * (‖z‖ ^ 2 - ‖w‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hy2 hb0
  have h3 : 2 * (a * inner ℝ x (z - w) + b * inner ℝ y (z - w))
      = a * (2 * inner ℝ x (z - w)) + b * (2 * inner ℝ y (z - w)) := by ring
  have hD : a * (‖z‖ ^ 2 - ‖w‖ ^ 2) + b * (‖z‖ ^ 2 - ‖w‖ ^ 2) = ‖z‖ ^ 2 - ‖w‖ ^ 2 := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- the edge interface `voronoiList V [u0, u1]` is convex -/
private theorem p23_convex_interface (V : Set V3) (u0 u1 : V3) :
    Convex ℝ (voronoiList V [u0, u1]) := by
  rw [p23_voronoiList_pair V u0 u1]
  exact (p23_voronoiClosed_convex V u0).inter (p23_voronoiClosed_convex V u1)

/-- interface points are at least half the edge length from `u0` (Pythagoras
on the bisector, HL XYOFCGX tail) -/
private theorem p23_bis_lower (u0 u1 : V3) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) {w : V3}
    (hw : w ∈ voronoiList V [u0, u1]) : dist u0 u1 / 2 ≤ dist u0 w := by
  have hbis : w ∈ p23Bis u0 u1 := p23_voronoiList_sub_bis V u0 u1 hu0 hu1 hw
  have hpyth := p23_bis_pythagoras u0 u1 w hbis
  have hsq : (dist u0 u1 / 2) ^ 2 ≤ (dist u0 w) ^ 2 := by
    rw [hpyth]
    nlinarith
  exact pow_le_pow_iff_left₀ (a := dist u0 u1 / 2) (b := dist u0 w) (n := 2)
    (by positivity) dist_nonneg two_ne_zero |>.mp hsq

/-- HL B5 head (GRUTOTI.hl:1103-1290, restructured): an `affGeAlt {u0} S`
point inside `ball u0 1` is a segment point `x = (1-t)•u0 + t•w` with
`w ∈ S`, `t ∈ [0,1]`. The negative-weight arm dies against the packing
bound `dist u0 u1 ≥ 2` plus Pythagoras on the bisector. -/
private theorem p23_seg_of_affGeAlt (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hneS : (voronoiList V [u0, u1]).Nonempty) (x : V3)
    (hxW : affGeAlt {u0} (voronoiList V [u0, u1]) x) (hball : dist x u0 < 1) :
    ∃ w : V3, w ∈ voronoiList V [u0, u1] ∧
      x ∈ convexHull ℝ ({u0, w} : Set V3) := by
  -- unpack the affGeAlt witness
  obtain ⟨f, q, qfin, qsub, hxeq, hqnn, hsum⟩ := hxW
  have hTfin : (({u0} ∪ q : Set V3)).Finite := Set.Finite.insert u0 qfin
  haveI hdecU : DecidablePred (· ∈ ({u0} ∪ q : Set V3)) := Classical.decPred _
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset V3, Q = hTfin.toFinset := ⟨_, rfl⟩
  have hu0Q : u0 ∈ Q := by
    rw [hQdef]
    exact (Set.Finite.mem_toFinset hTfin).mpr
      (Set.mem_union_left q (Set.mem_singleton u0))
  have hxsum : x = ∑ v ∈ Q, f v • v := by
    rw [hQdef]
    have h1 : linCombo ({u0} ∪ q) f = ∑ v ∈ hTfin.toFinset, f v • v := dif_pos hTfin
    rw [hxeq, h1]
  have hsum1 : ∑ v ∈ Q, f v = 1 := by
    rw [hQdef]
    have h1 : setSum ({u0} ∪ q) f = ∑ v ∈ hTfin.toFinset, f v := dif_pos hTfin
    exact h1.symm.trans hsum
  -- the sum splits off the u0-term
  have hsumsplit : ∑ v ∈ Q, f v = f u0 + ∑ v ∈ Q.erase u0, f v := by
    have hEq : Q.erase u0 ∪ {u0} = Q := by
      refine Finset.ext fun z => ?_
      by_cases hz : z = u0
      · subst hz
        simp [hu0Q]
      · simp [hz, hu0Q]
    have hdis : Disjoint (Q.erase u0) ({u0} : Finset V3) := by simp
    have hsu := Finset.sum_union (h := hdis) (f := f)
    calc ∑ v ∈ Q, f v = ∑ v ∈ (Q.erase u0 ∪ {u0} : Finset V3), f v := by rw [hEq]
      _ = ∑ v ∈ Q.erase u0, f v + ∑ v ∈ ({u0} : Finset V3), f v := hsu
      _ = ∑ v ∈ Q.erase u0, f v + f u0 := by rw [Finset.sum_singleton]
      _ = f u0 + ∑ v ∈ Q.erase u0, f v := add_comm _ _
  have hxsplit : x = f u0 • u0 + ∑ v ∈ Q.erase u0, f v • v := by
    have hEq : Q.erase u0 ∪ {u0} = Q := by
      refine Finset.ext fun z => ?_
      by_cases hz : z = u0
      · subst hz
        simp [hu0Q]
      · simp [hz, hu0Q]
    have hdis : Disjoint (Q.erase u0) ({u0} : Finset V3) := by simp
    have hsu := Finset.sum_union (h := hdis)
      (f := fun v : V3 => f v • v)
    calc x = ∑ v ∈ Q, f v • v := hxsum
      _ = ∑ v ∈ (Q.erase u0 ∪ {u0} : Finset V3), f v • v := by rw [hEq]
      _ = ∑ v ∈ Q.erase u0, f v • v + ∑ v ∈ ({u0} : Finset V3), f v • v := hsu
      _ = ∑ v ∈ Q.erase u0, f v • v + f u0 • u0 := by rw [Finset.sum_singleton]
      _ = f u0 • u0 + ∑ v ∈ Q.erase u0, f v • v := add_comm _ _
  have hqmem : ∀ v ∈ Q.erase u0, v ∈ q := by
    intro v hv
    have hvQ : v ∈ Q := Finset.mem_of_mem_erase hv
    have hvne : v ≠ u0 := Finset.ne_of_mem_erase hv
    rw [hQdef] at hvQ
    have hvU : v ∈ ({u0} ∪ q : Set V3) := (Set.Finite.mem_toFinset hTfin).mp hvQ
    rcases hvU with h | h
    · exact absurd (by rw [Set.mem_singleton_iff] at h; exact h ▸ hvne) (by simp)
    · exact h
  -- t := the total weight on the interface points
  set t := ∑ v ∈ Q.erase u0, f v with htdef
  have htnonneg : 0 ≤ t := Finset.sum_nonneg (fun v hv => hqnn v (hqmem v hv))
  have hkey : f u0 + t = 1 := by rw [htdef, ← hsumsplit, hsum1]
  have htsum : t = 1 - f u0 := by linarith
  -- f u0 < 0 (i.e. t > 1) is excluded by the ball bound + the packing lower bound
  have hexcl : ¬ (f u0 < 0) := by
    intro hf0
    have ht1 : 1 < t := by linarith
    have ht0' : 0 < t := by linarith
    have htne : t ≠ 0 := ne_of_gt ht0'
    have hyexpand : ∑ v ∈ Q.erase u0, (f v / t) • v
        = t⁻¹ • ∑ v ∈ Q.erase u0, f v • v := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [smul_smul]
      congr 1
      field_simp
    have hyS : (∑ v ∈ Q.erase u0, (f v / t) • v) ∈ voronoiList V [u0, u1] := by
      refine Convex.sum_mem (p23_convex_interface V u0 u1) ?_ ?_ ?_
      · intro v hv
        exact div_nonneg (hqnn v (hqmem v hv)) ht0'.le
      · rw [show ∑ v ∈ Q.erase u0, f v / t = (∑ v ∈ Q.erase u0, f v) / t from by
            rw [Finset.sum_div], htdef]
        exact div_self (ne_of_gt ht0')
      · intro v hv
        exact qsub (hqmem v hv)
    have hxx : x - u0 = t • ((∑ v ∈ Q.erase u0, (f v / t) • v) - u0) := by
      rw [hxsplit, hyexpand, htdef]
      have hf0t : f u0 = 1 - t := by linarith
      rw [hf0t, smul_sub, smul_smul, mul_inv_cancel₀ htne, one_smul]
      module
    have hnorm : dist x u0 = t * dist u0 (∑ v ∈ Q.erase u0, (f v / t) • v) := by
      rw [dist_eq_norm, hxx, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < t)]
      rw [dist_eq_norm, norm_sub_rev]
    have hlow : dist u0 u1 / 2 ≤ dist u0 (∑ v ∈ Q.erase u0, (f v / t) • v) :=
      p23_bis_lower u0 u1 hu0 hu1 hyS
    have hd2 : 2 ≤ dist u0 u1 := Packing.dist_ge_two hp hu0 hu1 hne
    rw [hnorm] at hball
    have hge : (1 : ℝ) ≤ dist u0 u1 / 2 := by linarith
    have hmul : t * (dist u0 u1 / 2) ≤ t * dist u0 (∑ v ∈ Q.erase u0, (f v / t) • v) :=
      mul_le_mul_of_nonneg_left hlow ht0'.le
    have hge2 : t * 1 ≤ t * (dist u0 u1 / 2) :=
      mul_le_mul_of_nonneg_left hge ht0'.le
    rw [mul_one] at hge2
    linarith
  -- so f u0 ≥ 0 and t = 1 - f u0 ≤ 1
  have hf0pos : 0 ≤ f u0 := le_of_not_gt hexcl
  have ht1' : t ≤ 1 := by linarith
  by_cases ht0 : t = 0
  · -- x = u0
    have hxu0 : x = u0 := by
      have hzero : ∑ v ∈ Q.erase u0, f v = 0 := by rw [← htdef]; exact ht0
      have heach : ∀ v ∈ Q.erase u0, f v = 0 := by
        intro v hv
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun v hv => hqnn v (hqmem v hv))).mp hzero v hv
      have htail : ∑ v ∈ Q.erase u0, f v • v = 0 :=
        Finset.sum_eq_zero (fun v hv => by rw [heach v hv, zero_smul])
      have hfu0 : f u0 = 1 := by rw [← hkey, ht0, add_zero]
      rw [hxsplit, htail, hfu0, one_smul, add_zero]
    refine ⟨hneS.choose, hneS.choose_spec, ?_⟩
    rw [hxu0, convexHull_pair]
    exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by simp⟩
  · -- x = (1 - t) • u0 + t • w with w ∈ S
    have htpos : 0 < t := lt_of_le_of_ne htnonneg (Ne.symm ht0)
    refine ⟨∑ v ∈ Q.erase u0, (f v / t) • v, ?_, ?_⟩
    · refine Convex.sum_mem (p23_convex_interface V u0 u1)
        (fun v hv => div_nonneg (hqnn v (hqmem v hv)) htpos.le) ?_
        (fun v hv => qsub (hqmem v hv))
      rw [show ∑ v ∈ Q.erase u0, f v / t = (∑ v ∈ Q.erase u0, f v) / t from by
          rw [Finset.sum_div], htdef]
      exact div_self (ne_of_gt htpos)
    · have hc : convexHull ℝ ({u0, ∑ v ∈ Q.erase u0, (f v / t) • v} : Set V3)
          = segment ℝ u0 (∑ v ∈ Q.erase u0, (f v / t) • v) := convexHull_pair _ _
      rw [hc]
      have hyexpand : t • (∑ v ∈ Q.erase u0, (f v / t) • v)
          = ∑ v ∈ Q.erase u0, f v • v := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [smul_smul]
        congr 1
        field_simp
      refine ⟨1 - t, t, by linarith, htpos.le, by linarith, ?_⟩
      have hf0t : f u0 = 1 - t := by linarith
      rw [hyexpand, ← hf0t]
      exact hxsplit.symm


/-! ### B5 kit: the cover C ⊆ ⋃₀ rogers-family and the mcell cover -/

/-- `u0` (the family-list head `ω0`) belongs to every rogers simplex of the
family -/
private theorem p23_u0_mem_rogers (V : Set V3) (u0 u1 : V3) {vl : List V3}
    (hvl : vl ∈ p23Fam V u0 u1) : u0 ∈ rogers V vl := by
  have hlen : vl.length = 4 := hvl.1.1
  have h0 : omegaListN V vl 0 = u0 := by
    have hzero : omegaListN V vl 0 = hdV vl := rfl
    rw [hzero, p23_hdV_eq_u0 hvl]
  rw [← h0]
  refine subset_convexHull ℝ _ (Set.mem_image_of_mem _ ?_)
  refine Set.mem_setOf.mpr ?_
  omega

/-- the interface sits in the rogers union over the family (via
`grutoti_vor_cover`: each member hull `{ω1, ω2, ω3}` is inside `rogers`) -/
private theorem p23_S_sub_rogers (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hs : saturated V) (hbar : barV V 1 [u0, u1]) :
    voronoiList V [u0, u1] ⊆ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1} := by
  rw [grutoti_vor_cover V u0 u1 hp hs hbar]
  intro w hw
  rw [Set.mem_sUnion] at hw
  obtain ⟨t, ht, hw⟩ := hw
  rw [Set.mem_setOf_eq] at ht
  obtain ⟨vl, hvl, rfl⟩ := ht
  have hlen : vl.length = 4 := hvl.1.1
  refine ⟨rogers V vl, ⟨vl, hvl, rfl⟩, ?_⟩
  have hsub : ({omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3} : Set V3) ⊆
      (omegaListN V vl '' {j : ℕ | j < vl.length}) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Set.mem_image_of_mem _ (Set.mem_setOf.mpr (by omega))
    · exact Set.mem_image_of_mem _ (Set.mem_setOf.mpr (by omega))
    · exact Set.mem_image_of_mem _ (Set.mem_setOf.mpr (by omega))
  exact convexHull_mono (𝕜 := ℝ) hsub hw

/-- HL B5 (GRUTOTI.hl:1103-1290): the region `C` is covered by the rogers
simplices of the family. -/
private theorem p23_C_sub_rogers (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2)
    (hs : saturated V) (hbar : barV V 1 [u0, u1]) (c : ℝ)
    (hcovW : ∀ x, x ∈ rconeGt u0 u1 c →
      affGeAlt {u0} (voronoiList V [u0, u1]) x) :
    Metric.ball u0 1 ∩ rconeGt u0 u1 c ⊆ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1} := by
  have hneS : (voronoiList V [u0, u1]).Nonempty :=
    ⟨u0 + (1 / 2 : ℝ) • (u1 - u0), p23_midpoint_mem_voronoiList V u0 u1 hp hu0 hu1 hne hhl⟩
  intro z hz
  obtain ⟨hball, hrcone⟩ := hz
  obtain ⟨w, hwS, zhull⟩ := p23_seg_of_affGeAlt V u0 u1 hp hu0 hu1 hne hneS z
    (hcovW z hrcone) (by rw [Metric.mem_ball] at hball; exact hball)
  have hwU : w ∈ (⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1}) :=
    p23_S_sub_rogers V u0 u1 hp hs hbar hwS
  rw [Set.mem_sUnion] at hwU
  obtain ⟨t, ht, hwR⟩ := hwU
  rw [Set.mem_setOf_eq] at ht
  obtain ⟨vl, hvl, rfl⟩ := ht
  rw [Set.mem_sUnion]
  refine ⟨rogers V vl, ⟨vl, hvl, rfl⟩, ?_⟩
  refine convexHull_min ?_ (convex_convexHull ℝ _) zhull
  have hu0r : u0 ∈ rogers V vl := p23_u0_mem_rogers V u0 u1 hvl
  refine Set.union_subset (Set.singleton_subset_iff.mpr hu0r) ?_
  rw [Set.singleton_subset_iff]
  exact hwR


/-- HL B5 (GRUTOTI.hl:1295-1537): the mcell cover over `C`. Every cell
meeting `C` in positive measure is a `k ≥ 2` cell over a family list. The
`k = 0/1` arms die against the shape of `mcell0`/`mcell1` and the two cone
inclusions of `p23_region_exists_c`; the identification of the cell is
`AJRIPQN` (PA17, upstream sorry). -/
private theorem p23_cover_C (V : Set V3) (u0 u1 : V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (c : ℝ)
    (hcovHl : ∀ x, x ∈ rconeGt u0 u1 c → x ∈ rconeGt u0 u1 (hl [u0, u1] / Real.sqrt 2))
    (hcover : Metric.ball u0 1 ∩ rconeGt u0 u1 c ⊆
      ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1}) (X : Set V3)
    (hX : X ∈ mcellSet V) (hnull : ¬ nullSet (X ∩ (Metric.ball u0 1 ∩ rconeGt u0 u1 c))) :
    ∃ k vl, 2 ≤ k ∧ barV V 3 vl ∧ X = mcell k V vl ∧ truncateSimplex 1 vl = [u0, u1] := by
  obtain ⟨i', ul, hXeq, hbarul⟩ := Set.mem_setOf_eq.mp hX
  set C := (Metric.ball u0 1 ∩ rconeGt u0 u1 c : Set V3) with hCdef
  have hne0 : volume (X ∩ C) ≠ 0 := hnull
  have hsub : X ∩ C ⊆ X ∩ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1} :=
    fun z hz => ⟨hz.1, hcover hz.2⟩
  have hne1 : volume (X ∩ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1}) ≠ 0 :=
    fun h0 => hne0 (measure_mono_null hsub h0)
  -- split the union over the finite family
  have hfam : (p23Fam V u0 u1).Finite := p23_family_finite V u0 u1 hp hs
  have hAfin : ({rogers V vl | vl ∈ p23Fam V u0 u1} : Set (Set V3)).Finite :=
    Set.Finite.image _ hfam
  have hsplit : X ∩ ⋃₀ {rogers V vl | vl ∈ p23Fam V u0 u1}
      = ⋃₀ ((fun t : Set V3 => X ∩ t) '' {rogers V vl | vl ∈ p23Fam V u0 u1}) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_image]
    constructor
    · rintro ⟨hzX, t, ht, hzt⟩
      exact ⟨X ∩ t, ⟨t, ht, rfl⟩, hzX, hzt⟩
    · rintro ⟨u, ⟨t, ht, rfl⟩, hzX, hzt⟩
      exact ⟨hzX, t, ht, hzt⟩
  have hIfin : (((fun t : Set V3 => X ∩ t) '' {rogers V vl | vl ∈ p23Fam V u0 u1} :
      Set (Set V3))).Finite := hAfin.image _
  have hex : ∃ u ∈ ((fun t : Set V3 => X ∩ t) '' {rogers V vl | vl ∈ p23Fam V u0 u1} :
      Set (Set V3)), volume u ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hkeys : volume (⋃ i ∈ ((fun t : Set V3 => X ∩ t) ''
        {rogers V vl | vl ∈ p23Fam V u0 u1} : Set (Set V3)),
        (fun u : Set V3 => u) i) = 0 ↔ ∀ u ∈ ((fun t : Set V3 => X ∩ t) ''
        {rogers V vl | vl ∈ p23Fam V u0 u1} : Set (Set V3)), volume u = 0 :=
      measure_biUnion_null_iff (s := fun u : Set V3 => u)
        (I := ((fun t : Set V3 => X ∩ t) '' {rogers V vl | vl ∈ p23Fam V u0 u1} :
          Set (Set V3))) hIfin.countable
    have h0 := hkeys.mpr hall
    rw [← Set.sUnion_eq_biUnion] at h0
    rw [← hsplit] at h0
    exact hne1 h0
  obtain ⟨u, hu, hvol⟩ := hex
  rw [Set.mem_image] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  obtain ⟨vl0, hvl0, rfl⟩ := Set.mem_setOf_eq.mp ht
  obtain ⟨hbarvl0, htrvl0⟩ := hvl0
  -- rogers V vl0 ⊆ ⋃_{i ≤ 4} mcell i V vl0 (SLTSTLO1) and split again
  have hsub2 : X ∩ rogers V vl0 ⊆ ⋃ i ∈ (Set.Iic 4 : Set ℕ), X ∩ mcell i V vl0 := by
    intro z hz
    obtain ⟨hzX, hzr⟩ := hz
    obtain ⟨i, hi, hzr2⟩ := SLTSTLO1 V vl0 z hs hp hbarvl0 hzr
    exact Set.mem_biUnion (Set.mem_Iic.mpr hi) ⟨hzX, hzr2⟩
  have hex2 : ∃ i ∈ (Set.Iic 4 : Set ℕ), volume (X ∩ mcell i V vl0) ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hkeys : volume (⋃ i ∈ (Set.Iic 4 : Set ℕ), X ∩ mcell i V vl0) = 0
        ↔ ∀ i ∈ (Set.Iic 4 : Set ℕ), volume (X ∩ mcell i V vl0) = 0 :=
      measure_biUnion_null_iff (s := fun i : ℕ => X ∩ mcell i V vl0)
        (I := (Set.Iic 4 : Set ℕ)) (Set.finite_Iic 4).countable
    have h0 := hkeys.mpr hall
    exact hvol (measure_mono_null hsub2 h0)
  obtain ⟨i, hi4, hvol2⟩ := hex2
  -- the uniqueness lemma (AJRIPQN, PA17; upstream sorry debt recorded)
  have hmem45 : ∀ n : ℕ, n ≤ 4 → n ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
    intro n hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hred : X = mcell (min i' 4) V ul := by
    rw [hXeq, p23_mcell_reduce]
  have hvol3 : ¬ nullSet (mcell i V vl0 ∩ mcell (min i' 4) V ul) := by
    rw [hred] at hvol2
    rw [Set.inter_comm] at hvol2
    exact hvol2
  obtain ⟨hieq, hcell⟩ := AJRIPQN V vl0 ul i (min i' 4) hs hp hbarvl0 hbarul
    (hmem45 i (Set.mem_Iic.mp hi4))
    (hmem45 _ (min_le_iff.mpr (Or.inr (by omega))))
    hvol3
  have hXvl0 : X = mcell i V vl0 := by
    rw [hred, ← hcell, hieq]
  -- rule out i = 0, 1
  have hi2 : ¬ (i = 0 ∨ i = 1) := by
    have hlt2 : i < 2 ∨ 2 ≤ i := Nat.lt_or_ge i 2
    rcases hlt2 with hlt | hge
    · have hi01 : i = 0 ∨ i = 1 := by omega
      rcases hi01 with h0 | h1
      · -- i = 0: mcell0 = rogers \ ball(u0,√2) misses C ⊆ ball(u0,1)
        subst h0
        exfalso
        apply hnull
        rw [hXvl0, (MCELL_EXPLICIT 0 V vl0).1, mcell0, p23_hdV_eq_u0 ⟨hbarvl0, htrvl0⟩]
        have hempty : (rogers V vl0 \ Metric.ball u0 (Real.sqrt 2)) ∩ C = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro z hz
          obtain ⟨⟨_, hzball⟩, hzC⟩ := hz
          simp only [hCdef, Set.mem_inter_iff] at hzC
          have h1s2 : (1:ℝ) < Real.sqrt 2 :=
            (Real.lt_sqrt (by positivity)).mpr (by norm_num : (1:ℝ) ^ 2 < 2)
          rw [Metric.mem_ball] at hzball
          have hge : Real.sqrt 2 ≤ dist z u0 := not_lt.mp hzball
          exact absurd (Metric.mem_ball.mp hzC.1) (by linarith)
        exact measure_mono_null hempty.subset measure_empty
      · -- i = 1: mcell1 misses C ⊆ rconeGt (hl/√2)
        subst h1
        exfalso
        apply hnull
        rw [hXvl0, (MCELL_EXPLICIT 1 V vl0).2.1, mcell1,
          p23_hdTail_eq_u1 ⟨hbarvl0, htrvl0⟩, p23_hdV_eq_u0 ⟨hbarvl0, htrvl0⟩, htrvl0]
        by_cases hcond : Real.sqrt 2 ≤ hl vl0
        · rw [if_pos hcond]
          have hempty : ((rogers V vl0 ∩ Metric.closedBall u0 (Real.sqrt 2)) \
              rconeGt u0 u1 (hl [u0, u1] / Real.sqrt 2)) ∩ C = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro z hz
            obtain ⟨⟨_, hzcone⟩, hzC⟩ := hz
            simp only [hCdef, Set.mem_inter_iff] at hzC
            exact absurd (hcovHl z hzC.2) hzcone
          exact measure_mono_null hempty.subset measure_empty
        · rw [if_neg hcond]
          exact measure_mono_null (by simp) measure_empty
    · omega
  refine ⟨i, vl0, by omega, hbarvl0, ?_, htrvl0⟩
  rw [hXvl0]


/-! ### B6 kit: the P1-P4 extremal bounds (HL 1538-2610) -/

/-- a set inside the affine span of a coplanar set is null (convenience
re-splice of `p23_coplanar_affineSpan_null` with the triple base case) -/
private theorem p23_coplanar_triple (a b c : V3) : Coplanar ℝ ({a, b, c} : Set V3) :=
  _root_.coplanar_triple (k := ℝ) a b c

/-- the `mcell 3` body sits in any affine span containing its four defining
points (empty when the `hl` guard fails) -/
private theorem p23_mcell3_sub_span {V : Set V3} {ul : List V3} {u0 u1 v2 : V3}
    (htr2 : setOfList (truncateSimplex 2 ul) = ({u0, u1, v2} : Set V3))
    {S : Set V3}
    (h0 : u0 ∈ (affineSpan ℝ S : Set V3)) (h1 : u1 ∈ (affineSpan ℝ S : Set V3))
    (h2 : v2 ∈ (affineSpan ℝ S : Set V3)) (hm : mxi V ul ∈ (affineSpan ℝ S : Set V3)) :
    mcell 3 V ul ⊆ (affineSpan ℝ S : Set V3) := by
  rw [(MCELL_EXPLICIT 3 V ul).2.2.2.1]
  unfold mcell3
  split
  · refine convexHull_min (𝕜 := ℝ) ?_ (AffineSubspace.convex _)
    intro z hz
    rcases hz with hz | hz
    · rw [htr2] at hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | hz
      · exact h0
      · rcases hz with rfl | rfl
        · exact h1
        · exact h2
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hm
  · intro z hz
    exact absurd hz (Set.notMem_empty z)

/-- the `mcell 4` body sits in any affine span containing its four defining
points -/
private theorem p23_mcell4_sub_span {V : Set V3} {ul : List V3} {u0 u1 v2 v3 : V3}
    (htr4 : setOfList ul = ({u0, u1, v2, v3} : Set V3))
    {S : Set V3}
    (h0 : u0 ∈ (affineSpan ℝ S : Set V3)) (h1 : u1 ∈ (affineSpan ℝ S : Set V3))
    (h2 : v2 ∈ (affineSpan ℝ S : Set V3)) (h3 : v3 ∈ (affineSpan ℝ S : Set V3)) :
    mcell 4 V ul ⊆ (affineSpan ℝ S : Set V3) := by
  rw [(MCELL_EXPLICIT 4 V ul).2.2.2.2 (Nat.le_refl 4)]
  unfold mcell4
  split
  · refine convexHull_min (𝕜 := ℝ) ?_ (AffineSubspace.convex _)
    intro z hz
    rw [htr4] at hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | hz
    · exact h0
    · rcases hz with rfl | hz
      · exact h1
      · rcases hz with rfl | rfl
        · exact h2
        · exact h3
  · intro z hz
    exact absurd hz (Set.notMem_empty z)

/-- a cell lying in a plane is null against any set (the HL
`NEGLIGIBLE_SUBSET (affine hull …)` workhorse) -/
private theorem p23_null_of_span {V : Set V3} {ul : List V3} (k : ℕ) (T : Set V3)
    (hsub : mcell k V ul ⊆ (affineSpan ℝ T : Set V3)) (hcop : Coplanar ℝ T) :
    nullSet (mcell k V ul ∩ T) :=
  measure_mono_null Set.inter_subset_left
    (p23_coplanar_affineSpan_null hcop hsub)

/-- B6 P3 core: `u0` is not on the segment joining the third vertex and the
fourth point (`mxi`); else the whole cell lies in the plane of the other
three and is null against the non-nullness hypothesis. -/
private theorem p23_u0_notIn_hull3 (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 3 V ul ∩ Cst)) :
    u0 ∉ convexHull ℝ ({elV ul 2, mxi V ul} : Set V3) := by
  intro hu0
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
  subst hv
  have hv01 : v0 = u0 ∧ v1 = u1 := by
    have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
      (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
    rw [h1] at htr
    have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
    exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
  rw [hv01.1, hv01.2] at htr hnn hu0
  have htr2 : setOfList (truncateSimplex 2 [u0, u1, v2, v3])
      = ({u0, u1, v2} : Set V3) := by
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 v2 v3).2]
    ext z
    simp [setOfList]
  have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
  rw [hE2] at hu0
  have hu0span : u0 ∈
      (affineSpan ℝ ({u1, v2, mxi V [u0, u1, v2, v3]} : Set V3) : Set V3) := by
    refine convexHull_min (𝕜 := ℝ) ?_ (AffineSubspace.convex _) hu0
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_affineSpan (k := ℝ) (by simp)
    · exact mem_affineSpan (k := ℝ) (by simp)
  have hnull : nullSet (mcell 3 V [u0, u1, v2, v3]) :=
    p23_coplanar_affineSpan_null (p23_coplanar_triple u1 v2 (mxi V [u0, u1, v2, v3]))
      (p23_mcell3_sub_span htr2 hu0span (mem_affineSpan (k := ℝ) (by simp))
        (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)))
  exact hnn (measure_mono_null Set.inter_subset_left hnull)

/-- B6 P4 core: same facet-plane killer for the fourth vertex. -/
private theorem p23_u0_notIn_hull4 (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 4 V ul ∩ Cst)) :
    u0 ∉ convexHull ℝ ({elV ul 2, elV ul 3} : Set V3) := by
  intro hu0
  obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
  subst hv
  have hv01 : v0 = u0 ∧ v1 = u1 := by
    have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
      (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
    rw [h1] at htr
    have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
    exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
  rw [hv01.1, hv01.2] at htr hnn hu0
  have htr4 : setOfList [u0, u1, v2, v3] = ({u0, u1, v2, v3} : Set V3) := by
    ext z
    simp [setOfList]
  have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
  have hE3 : elV [u0, u1, v2, v3] 3 = v3 := rfl
  rw [hE2, hE3] at hu0
  have hu0span : u0 ∈
      (affineSpan ℝ ({u1, v2, v3} : Set V3) : Set V3) := by
    refine convexHull_min (𝕜 := ℝ) ?_ (AffineSubspace.convex _) hu0
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact mem_affineSpan (k := ℝ) (by simp)
    · exact mem_affineSpan (k := ℝ) (by simp)
  have hnull : nullSet (mcell 4 V [u0, u1, v2, v3]) :=
    p23_coplanar_affineSpan_null (p23_coplanar_triple u1 v2 v3)
      (p23_mcell4_sub_span htr4 hu0span (mem_affineSpan (k := ℝ) (by simp))
        (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)))
  exact hnn (measure_mono_null Set.inter_subset_left hnull)

/-- C-S equality core (HL 2126-2255 restructured): if a point of the segment
`[a, b]` has cosine exactly `1` towards the edge `(u0, u1)`, then one
endpoint lies in the affine span of `{u0, u1, other}` — the plane-cells
killer behind `f3 ul < 1` / `f4 ul < 1`. -/
private theorem p23_collinear_core (u0 u1 a b : V3) (hne : u0 ≠ u1) (xx : V3)
    (hxx : xx ∈ convexHull ℝ ({a, b} : Set V3)) (hk1 : ‖xx - u0‖ ≠ 0)
    (hcs : inner ℝ (xx - u0) (u1 - u0) = ‖xx - u0‖ * ‖u1 - u0‖) :
    b ∈ (affineSpan ℝ ({u0, u1, a} : Set V3) : Set V3) ∨
      a ∈ (affineSpan ℝ ({u0, u1, b} : Set V3) : Set V3) := by
  have hk1p : 0 < ‖xx - u0‖ := lt_of_le_of_ne (norm_nonneg (xx - u0)) (Ne.symm hk1)
  have hk2 : ‖u1 - u0‖ ≠ 0 := fun hcc => hne (dist_eq_zero.mp
    (by rw [dist_comm u0 u1]; exact hcc))
  have hk2p : 0 < ‖u1 - u0‖ := lt_of_le_of_ne (norm_nonneg (u1 - u0)) (Ne.symm hk2)
  set k1 := ‖xx - u0‖ with hk1def
  set k2 := ‖u1 - u0‖ with hk2def
  -- the unit-vector trick gives k2 • (xx - u0) = k1 • (u1 - u0)
  have ha'n : ‖(k1)⁻¹ • (xx - u0)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk1p), inv_mul_cancel₀ hk1]
  have hb'n : ‖(k2)⁻¹ • (u1 - u0)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk2p), inv_mul_cancel₀ hk2]
  have hA1 : inner ℝ ((k1)⁻¹ • (xx - u0)) ((k1)⁻¹ • (xx - u0)) = 1 := by
    rw [real_inner_self_eq_norm_sq, ha'n]; norm_num
  have hB1 : inner ℝ ((k2)⁻¹ • (u1 - u0)) ((k2)⁻¹ • (u1 - u0)) = 1 := by
    rw [real_inner_self_eq_norm_sq, hb'n]; norm_num
  have hAb : inner ℝ ((k1)⁻¹ • (xx - u0)) ((k2)⁻¹ • (u1 - u0)) = 1 := by
    rw [real_inner_smul_left, real_inner_smul_right, hcs]
    field_simp
  have hsub : ‖(k1)⁻¹ • (xx - u0) - (k2)⁻¹ • (u1 - u0)‖ = 0 := by
    have h2 : ‖(k1)⁻¹ • (xx - u0) - (k2)⁻¹ • (u1 - u0)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        hA1, hB1, real_inner_comm ((k1)⁻¹ • (xx - u0)) ((k2)⁻¹ • (u1 - u0)), hAb]
      ring
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  have hzero : (k1)⁻¹ • (xx - u0) - (k2)⁻¹ • (u1 - u0) = 0 := norm_eq_zero.mp hsub
  have he1 : (k1)⁻¹ • (xx - u0) = (k2)⁻¹ • (u1 - u0) := sub_eq_zero.mp hzero
  have hlin : k2 • (xx - u0) = k1 • (u1 - u0) := by
    have key := congrArg (fun z : V3 => (k2 * k1) • z) he1
    simp only [smul_smul] at key
    field_simp at key
    exact key
  -- the segment coordinates of xx
  obtain ⟨u, v, hu0, hv0, huv, hxuv⟩ :
      ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v = 1 ∧ u • a + v • b = xx := by
    have hseg : convexHull ℝ ({a, b} : Set V3) = segment ℝ a b := convexHull_pair a b
    rw [hseg] at hxx
    exact hxx
  have hE1 : k2 • xx = k1 • (u1 - u0) + k2 • u0 := by rw [← hlin]; module
  have hE2 : k2 • xx = (k2 * u) • a + (k2 * v) • b := by
    have hxx2 : xx = u • a + v • b := hxuv.symm
    rw [hxx2, smul_add, smul_smul, smul_smul]
  by_cases hv : v = 0
  · -- xx = u • a with u = 1: a lies on the line u0→u1
    right
    have hu1 : u = 1 := by linarith
    have hvne : k2 * 1 ≠ 0 := mul_ne_zero hk2 (by norm_num : (1:ℝ) ≠ 0)
    have hkey : a = u0 + (k1 / (k2 * 1)) • (u1 - u0)
        + (-(k2 * 0) / (k2 * 1)) • (b - u0) := by
      have hscaled : (k2 * 1) • a = (k2 * 1) • (u0 + (k1 / (k2 * 1)) • (u1 - u0)
          + (-(k2 * 0) / (k2 * 1)) • (b - u0)) := by
        rw [mul_one, mul_zero, neg_zero, zero_div, zero_smul, add_zero, smul_add, smul_smul,
          mul_div_cancel₀ _ hk2, add_comm (k2 • u0) (k1 • (u1 - u0)), ← hE1, hE2,
          hu1, hv, mul_one, mul_zero, zero_smul, add_zero]
      exact smul_right_injective V3 hvne hscaled
    exact p23_mem_affineSpan_triple u0 u1 b a (k1 / (k2 * 1)) (-(k2 * 0) / (k2 * 1)) hkey
  · -- v ≠ 0: b lies in the plane of {u0, u1, a}
    left
    have hvne : k2 * v ≠ 0 := mul_ne_zero hk2 hv
    have hv1 : k2 * v + k2 * u = k2 := by
      have h2 : k2 * v + k2 * u = k2 * (u + v) := by ring
      rw [h2, huv, mul_one]
    have hbexp : (k2 * v) • b = k1 • (u1 - u0) + k2 • u0 - (k2 * u) • a := by
      calc (k2 * v) • b = k2 • xx - (k2 * u) • a := by rw [hE2]; module
        _ = k1 • (u1 - u0) + k2 • u0 - (k2 * u) • a := by rw [hE1]
    have hkey : b = u0 + (k1 / (k2 * v)) • (u1 - u0)
        + ((k2 * u) / (k2 * v)) • (u0 - a) := by
      have hadd : (k2 * v) • u0 + (k2 * u) • u0 = k2 • u0 := by
        rw [← add_smul, hv1]
      have hscaled : (k2 * v) • b = (k2 * v) • (u0 + (k1 / (k2 * v)) • (u1 - u0)
          + ((k2 * u) / (k2 * v)) • (u0 - a)) := by
        simp only [smul_add, smul_smul, mul_div_cancel₀ _ hvne]
        rw [hbexp, smul_sub (k2 * u) u0 a]
        linear_combination (norm := module) -hadd
      exact smul_right_injective V3 hvne hscaled
    refine p23_mem_affineSpan_triple u0 u1 a b (k1 / (k2 * v)) (-(k2 * u) / (k2 * v)) ?_
    rw [hkey, smul_sub]
    module

/-- B6 P3 (HL 1546-1600 + 1826-1911): the P3 cosine values are all `< 1` —
the smallest-angle point of the `[v2, mxi]` segment cannot be collinear with
the edge, else the `mcell 3` cell sits in a plane. -/
private theorem p23_f3_lt_one (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (hne : u0 ≠ u1) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 3 V ul ∩ Cst)) :
    inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖) < 1 := by
  have hu0K : u0 ∉ convexHull ℝ ({elV ul 2, mxi V ul} : Set V3) :=
    p23_u0_notIn_hull3 V u0 u1 hp hs hb htr Cst hnn
  have hxmem : smallestAngleLine (elV ul 2) (mxi V ul) u0 u1
      ∈ convexHull ℝ ({elV ul 2, mxi V ul} : Set V3) :=
    SMALLEST_ANGLE_IN_CONVEX_HULL (elV ul 2) (mxi V ul) u0 u1
      (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1) hne hu0K rfl
  have hxxne : smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 ≠ u0 := fun hcc =>
    hu0K (hcc ▸ hxmem)
  have hk1 : ‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ ≠ 0 := fun hcc =>
    hxxne (sub_eq_zero.mp (norm_eq_zero.mp hcc))
  have hk2 : ‖u1 - u0‖ ≠ 0 := fun hcc =>
    hne (sub_eq_zero.mp (norm_eq_zero.mp hcc)).symm
  have hle : inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0)
      ≤ ‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖ := by
    have h1 := norm_inner_le_norm (𝕜 := ℝ)
      (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0)
    simp only [Real.norm_eq_abs] at h1
    have h2 := le_abs_self (inner ℝ
      (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0))
    linarith
  have hk1p : 0 < ‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk1)
  have hk2p : 0 < ‖u1 - u0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk2)
  by_cases hcos : inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0)
      (u1 - u0) / (‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖) = 1
  · exfalso
    have hcs : inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0)
        = ‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖ := by
      field_simp at hcos
      exact hcos
    obtain horr | horr := p23_collinear_core u0 u1 (elV ul 2) (mxi V ul) hne
      (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1) hxmem hk1 hcs
    · -- mxi in the plane of {u0, u1, elV ul 2}
      obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
      subst hv
      have hv01 : v0 = u0 ∧ v1 = u1 := by
        have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
          (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
        rw [h1] at htr
        have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
        exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
      rw [hv01.1, hv01.2] at htr hnn horr
      have htr2 : setOfList (truncateSimplex 2 [u0, u1, v2, v3])
          = ({u0, u1, v2} : Set V3) := by
        rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 v2 v3).2]
        ext z
        simp [setOfList]
      have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
      rw [hE2] at horr
      exact hnn (measure_mono_null Set.inter_subset_left
        (p23_coplanar_affineSpan_null (p23_coplanar_triple u0 u1 v2)
          (p23_mcell3_sub_span htr2 (mem_affineSpan (k := ℝ) (by simp))
            (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)) horr)))
    · -- elV ul 2 in the plane of {u0, u1, mxi}
      obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
      subst hv
      have hv01 : v0 = u0 ∧ v1 = u1 := by
        have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
          (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
        rw [h1] at htr
        have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
        exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
      rw [hv01.1, hv01.2] at htr hnn horr
      have htr2 : setOfList (truncateSimplex 2 [u0, u1, v2, v3])
          = ({u0, u1, v2} : Set V3) := by
        rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 v2 v3).2]
        ext z
        simp [setOfList]
      have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
      rw [hE2] at horr
      exact hnn (measure_mono_null Set.inter_subset_left
        (p23_coplanar_affineSpan_null
          (p23_coplanar_triple u0 u1 (mxi V [u0, u1, v2, v3]))
          (p23_mcell3_sub_span htr2 (mem_affineSpan (k := ℝ) (by simp))
            (mem_affineSpan (k := ℝ) (by simp)) horr
            (mem_affineSpan (k := ℝ) (by simp)))))
  · rw [div_lt_one (mul_pos hk1p hk2p)]
    have h2 := hcos
    field_simp at h2
    exact lt_of_le_of_ne hle (fun hcc => h2 (by rw [hcc]))

/-- B6 P4 (HL 2247-2605): the P4 cosine values are all `< 1` — same
collinearity killer with the fourth vertex in place of `mxi` and the
`mcell 4` body. -/
private theorem p23_f4_lt_one (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (hne : u0 ≠ u1) {ul : List V3} (hb : barV V 3 ul)
    (htr : truncateSimplex 1 ul = [u0, u1]) (Cst : Set V3)
    (hnn : ¬ nullSet (mcell 4 V ul ∩ Cst)) :
    inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖) < 1 := by
  have hu0K : u0 ∉ convexHull ℝ ({elV ul 2, elV ul 3} : Set V3) :=
    p23_u0_notIn_hull4 V u0 u1 hp hs hb htr Cst hnn
  have hxmem : smallestAngleLine (elV ul 2) (elV ul 3) u0 u1
      ∈ convexHull ℝ ({elV ul 2, elV ul 3} : Set V3) :=
    SMALLEST_ANGLE_IN_CONVEX_HULL (elV ul 2) (elV ul 3) u0 u1
      (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1) hne hu0K rfl
  have hxxne : smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 ≠ u0 := fun hcc =>
    hu0K (hcc ▸ hxmem)
  have hk1 : ‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ ≠ 0 := fun hcc =>
    hxxne (sub_eq_zero.mp (norm_eq_zero.mp hcc))
  have hk2 : ‖u1 - u0‖ ≠ 0 := fun hcc =>
    hne (sub_eq_zero.mp (norm_eq_zero.mp hcc)).symm
  have hk1p : 0 < ‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk1)
  have hk2p : 0 < ‖u1 - u0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hk2)
  have hle : inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0)
      ≤ ‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖ := by
    have h1 := norm_inner_le_norm (𝕜 := ℝ)
      (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0)
    simp only [Real.norm_eq_abs] at h1
    have h2 := le_abs_self (inner ℝ
      (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0))
    linarith
  by_cases hcos : inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0)
      (u1 - u0) / (‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖) = 1
  · exfalso
    have hcs : inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0)
        = ‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖ := by
      field_simp at hcos
      exact hcos
    obtain horr | horr := p23_collinear_core u0 u1 (elV ul 2) (elV ul 3) hne
      (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1) hxmem hk1 hcs
    · -- elV ul 3 in the plane of {u0, u1, elV ul 2}
      obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
      subst hv
      have hv01 : v0 = u0 ∧ v1 = u1 := by
        have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
          (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
        rw [h1] at htr
        have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
        exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
      rw [hv01.1, hv01.2] at htr hnn horr
      have htr4 : setOfList [u0, u1, v2, v3] = ({u0, u1, v2, v3} : Set V3) := by
        ext z
        simp [setOfList]
      have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
      have hE3 : elV [u0, u1, v2, v3] 3 = v3 := rfl
      rw [hE2, hE3] at horr
      exact hnn (measure_mono_null Set.inter_subset_left
        (p23_coplanar_affineSpan_null (p23_coplanar_triple u0 u1 v2)
          (p23_mcell4_sub_span htr4 (mem_affineSpan (k := ℝ) (by simp))
            (mem_affineSpan (k := ℝ) (by simp)) (mem_affineSpan (k := ℝ) (by simp)) horr)))
    · -- elV ul 2 in the plane of {u0, u1, elV ul 3}
      obtain ⟨v0, v1, v2, v3, hv⟩ := BARV_3_EXPLICIT V ul hb
      subst hv
      have hv01 : v0 = u0 ∧ v1 = u1 := by
        have h1 : truncateSimplex 1 [v0, v1, v2, v3] = [v0, v1] :=
          (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2
        rw [h1] at htr
        have h2 := List.cons.injEq v0 [v1] u0 [u1] |>.mp htr
        exact ⟨h2.1, (List.cons.injEq v1 [] u1 [] |>.mp h2.2).1⟩
      rw [hv01.1, hv01.2] at htr hnn horr
      have htr4 : setOfList [u0, u1, v2, v3] = ({u0, u1, v2, v3} : Set V3) := by
        ext z
        simp [setOfList]
      have hE2 : elV [u0, u1, v2, v3] 2 = v2 := rfl
      have hE3 : elV [u0, u1, v2, v3] 3 = v3 := rfl
      rw [hE2, hE3] at horr
      exact hnn (measure_mono_null Set.inter_subset_left
        (p23_coplanar_affineSpan_null (p23_coplanar_triple u0 u1 v3)
          (p23_mcell4_sub_span htr4 (mem_affineSpan (k := ℝ) (by simp))
            (mem_affineSpan (k := ℝ) (by simp)) horr
            (mem_affineSpan (k := ℝ) (by simp)))))
  · rw [div_lt_one (mul_pos hk1p hk2p)]
    have h2 := hcos
    field_simp at h2
    exact lt_of_le_of_ne hle (fun hcc => h2 (by rw [hcc]))

/-- HL GRUTOTI.hl:161-2636: the volumetric core. Produces cone/annulus
parameters `c r d` (`c = max b (hl/√2)`, `r = min 1 (min r1 r2)`,
`d = max c (max d1 d2)` from the P1..P4 extremal arguments) with `D =
grutotiConicCap u0 u1 r d ⊆ C`, and the mcell cover (HL:2631-2636): every
Marchal cell meeting `D` in positive measure is a `k ≥ 2` cell over a
`barV V 3` list with `truncateSimplex 1 vl = [u0, u1]`.
GT-4 status (2026-09-30): B1-B4 are BANKED as the zero-sorry private chain
above (`p23_region_exists_delta` + `p23_region_exists_c`: HL:161-1143 —
bisector S1, interface S, midpoint XYOFCGX, critical radius δ, cone threshold
c ∈ (0,1) with `rconeGt u0 u1 c ⊆ affGeAlt {u0} S ∩ rconeGt u0 u1 (hl/√2)`).
HL's `S2 = S1 \ relative_interior S` is replaced by the explicit relative
neighbourhood `S' = S1 ∩ ball(p,d₀) ⊆ S` (B2's nearest-point selection);
this avoids the unported `AFF_DIM_VORONOI_LIST` and the intrinsicInterior
bridge entirely. REMAINING (the `sorry` below, HL:1144-2636): B5-B7 — the
rogers/mcell cover kit (B5, HL:1144-1537), the P1-P4 minima over the
truncation lists via smallest_angle_line (B6, HL:1538-2610; the PA15
SMALLEST_ANGLE_LINE kit is available), and the final assembly
`c = max b (hl/√2)`, `r = min 1 (min r1 r2)`, `d = max c (max d1 d2)`,
`D ⊆ C`, and the mcell cover (B7, HL:2611-2636).
CLOSED (2026-09-30 GT-4b): `c` from `p23_region_exists_c`; `r = 1/2` and
`d = max c (max d1 d2)` with `d1`/`d2` the sup of the P3/P4 cosine values
(`p23_f3_lt_one`/`p23_f4_lt_one`, `c` on the empty family), and the cover
transported from `p23_cover_C` along `D ⊆ C`.
DEVIATIONS from HL (recorded for the cell-volume lane, which consumes these
witnesses):
* `r = 1/2` replaces HL's `min 1 (min r1 r2)`: the Lean `grutotiConicCap`
  uses a CLOSED ball so `D ⊆ C` needs `r < 1` strictly, and the frozen region
  statement only asks `0 < r ≤ 1`. The r-side extremal data (`f1`/`f2` >
  0 via the facet-plane nullness route: `u0 ∉ affineSpan {u1, v2, mxi}` /
  `{u1, v2, v3}` nulls the whole cell) is NOT exported; the `grutoti_cell_vol`
  k = 3/4 radial argument must re-derive it.
* `d1`/`d2` here are genuine sups of the P3/P4 families (as in HL), so the
  d-side narrowness (`d ≥ d1`, `d ≥ d2`: the cone sits inside every k = 2/3
  cell wedge) IS available at these witnesses — but only through
  re-derivation: the frozen `grutoti_cell_vol` signature carries opaque
  `r d`, so its fill needs an SF to take the extremal data as hypotheses
  (or to restate along `grutoti_region`'s witnesses).
* `e` is unused (HL carries it for the caller bookkeeping only). -/
private theorem grutoti_region (V : Set V3) (u0 u1 : V3) (e : Set V3)
    (hs : saturated V) (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V)
    (hne : u0 ≠ u1) (hhl : hl [u0, u1] < Real.sqrt 2) (he : e = {u0, u1}) :
    ∃ c r d : ℝ, 0 < c ∧ c < 1 ∧ 0 < r ∧ r ≤ 1 ∧ 0 < d ∧ d < 1 ∧ c ≤ d ∧
      (∀ X : Set V3, X ∈ mcellSet V ∧ ¬nullSet (X ∩ grutotiConicCap u0 u1 r d) →
        ∃ k : ℕ, ∃ vl : List V3, 2 ≤ k ∧ barV V 3 vl ∧ X = mcell k V vl ∧
          truncateSimplex 1 vl = [u0, u1]) := by
  obtain ⟨c, hc0, hc1, hcW, hcHl⟩ := p23_region_exists_c V u0 u1 hs hp hu0 hu1 hne hhl
  have hbar := grutoti_barV V u0 u1 hs hp hu0 hu1 hne hhl
  set C := (Metric.ball u0 1 ∩ rconeGt u0 u1 c : Set V3) with hCdef
  -- B5: the mcell cover over C
  have hB5 : ∀ X : Set V3, X ∈ mcellSet V → ¬ nullSet (X ∩ C) →
      ∃ k vl, 2 ≤ k ∧ barV V 3 vl ∧ X = mcell k V vl ∧ truncateSimplex 1 vl = [u0, u1] :=
    p23_cover_C V u0 u1 hs hp hu0 hu1 hne c hcHl
      (p23_C_sub_rogers V u0 u1 hp hu0 hu1 hne hhl hs hbar c hcW)
  -- B6: the P3/P4 sups are strictly below 1
  set famP3 : Set (List V3) := {vl | barV V 3 vl ∧ ¬ nullSet (mcell 3 V vl ∩ C) ∧
    truncateSimplex 1 vl = [u0, u1]} with hfamP3def
  have hfamP3sub : famP3 ⊆ p23Fam V u0 u1 := by
    intro vl hvl
    obtain ⟨hb, _, htr⟩ := hvl
    exact ⟨hb, htr⟩
  have hfamP3fin : famP3.Finite := (p23_family_finite V u0 u1 hp hs).subset hfamP3sub
  set f3 : List V3 → ℝ := fun ul =>
    inner ℝ (smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (mxi V ul) u0 u1 - u0‖ * ‖u1 - u0‖) with hf3def
  have hf3lt : ∀ ul ∈ famP3, f3 ul < 1 := by
    intro ul hul
    obtain ⟨hb, hnn, htr⟩ := hul
    exact p23_f3_lt_one V u0 u1 hp hs hne hb htr C hnn
  obtain ⟨d1, hd1⟩ : ∃ d1 : ℝ, d1 < 1 := by
    by_cases hP3 : (f3 '' famP3) = ∅
    · exact ⟨c, hc1⟩
    · obtain ⟨m, hm, _hmax⟩ := Set.exists_max_image (f3 '' famP3) id
        (hfamP3fin.image _) (Set.nonempty_iff_ne_empty.mpr hP3)
      rcases hm with ⟨ul0, hul0, rfl⟩
      exact ⟨f3 ul0, hf3lt ul0 hul0⟩
  set famP4 : Set (List V3) := {vl | barV V 3 vl ∧ ¬ nullSet (mcell 4 V vl ∩ C) ∧
    truncateSimplex 1 vl = [u0, u1]} with hfamP4def
  have hfamP4sub : famP4 ⊆ p23Fam V u0 u1 := by
    intro vl hvl
    obtain ⟨hb, _, htr⟩ := hvl
    exact ⟨hb, htr⟩
  have hfamP4fin : famP4.Finite := (p23_family_finite V u0 u1 hp hs).subset hfamP4sub
  set f4 : List V3 → ℝ := fun ul =>
    inner ℝ (smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0) (u1 - u0) /
      (‖smallestAngleLine (elV ul 2) (elV ul 3) u0 u1 - u0‖ * ‖u1 - u0‖) with hf4def
  have hf4lt : ∀ ul ∈ famP4, f4 ul < 1 := by
    intro ul hul
    obtain ⟨hb, hnn, htr⟩ := hul
    exact p23_f4_lt_one V u0 u1 hp hs hne hb htr C hnn
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℝ, d2 < 1 := by
    by_cases hP4 : (f4 '' famP4) = ∅
    · exact ⟨c, hc1⟩
    · obtain ⟨m, hm, _hmax⟩ := Set.exists_max_image (f4 '' famP4) id
        (hfamP4fin.image _) (Set.nonempty_iff_ne_empty.mpr hP4)
      rcases hm with ⟨ul0, hul0, rfl⟩
      exact ⟨f4 ul0, hf4lt ul0 hul0⟩
  -- B7: assemble
  refine ⟨c, 1 / 2, max c (max d1 d2), hc0, hc1, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact hc0.trans_le (le_max_left _ _)
  · exact max_lt hc1 (max_lt hd1 hd2)
  · exact le_max_left _ _
  · rintro X ⟨hX, hn⟩
    have hr1' : (1 : ℝ) / 2 < 1 := by norm_num
    have hDC : grutotiConicCap u0 u1 (1 / 2) (max c (max d1 d2)) ⊆ C := by
      rw [grutotiConicCap, hCdef]
      intro z hz
      obtain ⟨hzball, hzr⟩ := hz
      refine ⟨?_, grutoti_rconeGt_subset u0 u1 c (max c (max d1 d2)) (le_max_left _ _) hzr⟩
      exact Metric.mem_ball.mp (Metric.closedBall_subset_ball hr1' hzball)
    exact hB5 X hX (fun h0 => hn (measure_mono_null
      (fun z hz => ⟨hz.1, hDC hz.2⟩ : X ∩ grutotiConicCap u0 u1 (1 / 2)
        (max c (max d1 d2)) ⊆ X ∩ C) h0))

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
