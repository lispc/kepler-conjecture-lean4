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
per-cell wedge-volume identity. NEEDS-precision: `k = 2` cells are the
hull/aff_ge `L = aff_ge {u0,u1} {mxi, ω₃}` wedge with `vol (X ∩ D) = vol (L ∩ D)`
(HL:2673-2830); `k = 3` uses the azim-complement identity `AZIM_COMPL`
(HL:7197-7223); `k = 0,1,4` and degenerate cases give null intersection via
`COPLANAR_IMP_NEGLIGIBLE`/`NEGLIGIBLE_AFFINE_HULL_3` (HL:7521-7958);
`dihX` dispatch via `MCELL_EXPLICIT` (Auto12:524). -/
private theorem grutoti_cell_vol (V : Set V3) (u0 u1 : V3) (r d : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hd : 0 < d) (hd1 : d < 1) (X : Set V3)
    (hm : X ∈ mcellSet V) (hn : ¬nullSet (X ∩ grutotiConicCap u0 u1 r d)) :
    volume.real (X ∩ grutotiConicCap u0 u1 r d) =
      volume.real (grutotiConicCap u0 u1 r d) * dihX V X (u0, u1) / (2 * Real.pi) := by
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
