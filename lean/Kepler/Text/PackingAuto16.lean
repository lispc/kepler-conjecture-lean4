/-
Packing chapter, solid-angle totals and ball bounds (S16 stage): the
`QZYZMJC` + `KIZHLTL` lane.

HOL sources:
- `scripts/packing/QZYZMJC.hl` (1111 lines, module `Qzyzmjc`, VU KHAC KY,
  book lemma QZYZMJC, chapter Packing): the capstone `QZYZMJC` — the solid
  angles of the Marchal cells around a packing point sum to `4π` — over its
  private chain `mcell_set_2`, `BARV_3_IMP_FINITE_lemma1/2`,
  `lemma_r_r'_fix2`, `MCELL_SET_NOT_EMPTY`.
- `scripts/packing/KIZHLTL.hl` (1032 lines, module `Kizhltl`): the three
  capstones `KIZHLTL1`/`KIZHLTL2`/`KIZHLTL4` (isoperimetric-style upper
  bounds of the cell volume / total solid angle / edge-dihedral sums over
  `ball 0 r` by Voronoi / vertex-count / edge sums over the packing, up to
  `c * r^2`). `KIZHLTL3_concl` (`pack_concl.hl:210-220`, the general-`f`
  version with `dist < sqrt 8`) has NO proof anywhere in the local HL tree
  (`KIZHLTL.hl` proves the `lmfun`/`2 * h0` specialization `KIZHLTL4`
  instead; `UPFZBZM_support_lemmas.hl:71` only restates a `_new_concl`) —
  stated faithfully here and sorried.

## File map

1. Private support chain of QZYZMJC.hl (proved mechanical lemmas +
   one sorried giant `MCELL_SET_NOT_EMPTY`).
2. The five capstones `QZYZMJC`, `KIZHLTL1`, `KIZHLTL2`, `KIZHLTL3`,
   `KIZHLTL4` (all sorried giants).

## DISCHARGES convention

- `QZYZMJC` matches the `pack_concl` interface verbatim:
  DISCHARGES: PackingAuto2.QZYZMJC_concl (PackingAuto2.lean:803).
- `KIZHLTL1` DISCHARGES: PackingAuto2.KIZHLTL1_concl (PackingAuto2.lean:808);
  the statement is unchanged, with the private `voronoiOpenP16` copy of
  `voronoi_open` (identical body; PackingAuto2's `voronoiOpen` is private to
  that file — merge-time `exact` works up to delta).
- `KIZHLTL2` DISCHARGES: PackingAuto2.KIZHLTL2_concl (PackingAuto2.lean:816).
- `KIZHLTL3` DISCHARGES: PackingAuto2.KIZHLTL3_concl (PackingAuto2.lean:824).
- `KIZHLTL4` has no `pack_concl` interface (defined locally in KIZHLTL.hl:533
  and consumed by UPFZBZM.hl:122): DISCHARGES: none (feeds UPFZBZM
  downstream).

## Encoding notes

- HOL `real^3` ↔ `V3` (Kepler.Geom); `ball`/`normball` ↔ `Metric.ball` (HL
  `ball` is open); `vol` ↔ `volume.real`; `measurable` ↔ `MeasurableSet`;
  `sum S f` ↔ `setSum` (PackingAuto2, junk 0 on infinite sets); `packing` ↔
  `Packing` (Kepler.Statement); `saturated`, `voronoi_closed`, `voronoi_list`,
  `barV`, `rogers`, `mcell`, `mcell_set`, `cell_params`, `VX`, `edgeX`,
  `dihX`, `sol` (Kepler.Geom.Volume), `hl`, `mm1`, `mm2`, `h0`, `lmfun`,
  `total_solid` ↔ `totalSolid` are the PackingAuto2 / Kepler.Geom.Volume
  definitions. `HD ul` ↔ `hdV`; `truncate_simplex` ↔ `truncateSimplex`;
  `set_of_list` ↔ `setOfList`; `negligible` ↔ `nullSet` (the VX convention).
- HOL `\({u,v}). g X {u,v}` (pattern lambda over unordered edge pairs) ↔ the
  gammaX/KIZHLTL3_concl encoding by `Classical.epsilon` over the unfolding
  `e = {u.1, u.2}` (PackingAuto2 gammaX precedent; the chapter proves the
  value order-independent via DIHX_SYM).
- The pattern-lambda `if {u,v} IN edgeX V X then ... else &0` guard of
  KIZHLTL4 is kept verbatim (it is definitionally satisfied on `edgeX`).
- `lemma_r_r'_fix2`: HL `radial_norm` ↔ `Kepler.Geom.Volume.radialNorm`
  (same junk-free body); the `s < r` case is
  `radialNorm.volume_scaling` (Vol1 `lemma_r_r'`), the `s = r` case is
  `C ⊆ ball x r` from `radialNorm`'s first conjunct.
- Proof architecture of the sorried giants (for the fill-in harness):
  QZYZMJC needs (beyond this file's chain) NEEDS URRPHBZ2, NEEDS SLTSTLO1
  (marchal3 lane, parallel-owned PackingAuto13 — its olean is not built in
  this checkout, NOT importable here), NEEDS LEPJBDJ (PackingAuto11),
  NEEDS HDTFNFZ (PackingAuto10), NEEDS AJRIPQN
  (AJRIPQN.hl — NOT yet on the Lean side: unique-representation of a cell as
  `mcell i V ul` with `ul IN barV V 3 /\ i IN 0..4`; needs a `_p16` copy at
  fill-in time), NEEDS GLTVHUM (PackingAuto6), NEEDS VORONOI_LIST_3_
  SINGLETON_EXPLICIT (marchal2.hl:2231 — parallel-owned PackingAuto12, also
  unbuilt here: private `voronoiList3SingletonExplicit_p16` copy below,
  delete at merge), NEEDS `sol_spec` (Kepler.Geom.Volume).
  KIZHLTL1/2/4 additionally need NEEDS FINITE_MCELL_SET_LEMMA,
  NEEDS PACKING_BALL_BOUNDARY, NEEDS MCELL_SUBSET_BALL_4, NEEDS DIHX_SYM
  (marchal3.hl — parallel-owned Auto15, NOT importable: `_p16` copies +
  NEEDS markers at fill-in), NEEDS MEASURE_NEGLIGIBLE_UNIONS_IMAGE and
  NEEDS MEASURE_VORONOI_CLOSED_OPEN / MEASURABLE_VORONOI_CLOSED /
  NEGLIGIBLE_INTER_VORONOI_CLOSED (Pack2.hl, not on the Lean side), NEEDS
  TIWWFYQ (PackingAuto5), NEEDS Flyspeck_constants bounds
  `#1.012080 < mm1` (numerical: mm1 ≈ 1.0121).
- The `mcell` dispatch step of `mcell_set_2` (HL uses marchal2
  `MCELL_EXPLICIT`) is proved inline from the public PackingAuto2 `mcell`
  definition — no Auto12 dependency needed.
- Proof status (2026-09-19): `voronoiList3SingletonExplicit_p16` SHIMMED to
  `PackingAuto12.VORONOI_LIST_3_SINGLETON_EXPLICIT` (olean landed; still
  `sorry`ed upstream there — documented transitive shim). The four mechanical
  private lemmas of QZYZMJC.hl are proved; `MCELL_SET_NOT_EMPTY` and the five
  capstones remain `sorry`ed giants (HL proofs run 350-600 lines each).
- Proof status (2026-09-30, U-2B/2C fill lane): `KIZHLTL1` and `KIZHLTL2`
  DISCHARGED (HL KIZHLTL.hl:46-279 / :285-527 ported; both consume the sorried
  giants listed above as legal in-tree flow: QZYZMJC, AJRIPQN/PackingAuto17,
  HDTFNFZ/PackingAuto10, MCELL_SUBSET_BALL_4 + PACKING_BALL_BOUNDARY +
  FINITE_MCELL_SET_LEMMA/PackingAuto15, TIWWFYQ + CLOSED/CONVEX_VORONOI_CLOSED
  + VORONOI_BALL2/PackingAuto5). The Pack2.hl measure bridge (all four pieces)
  is proved inline below as `p16_` privates (hyperplane-null via
  `Measure.addHaar_affineSubspace`, closed-vs-open volume via
  `Convex.addHaar_frontier` + the tie-point/interior argument, a.e.-disjoint
  finite unions by Finset induction, measurable-voronoi-closed from PA5).
  KIZHLTL2 needs only the SIGN `0 ≤ mm1` of the Flyspeck constant (proved
  from `cos_pi_div_five` + arccos antitonicity; no Taylor machinery). The
  `KIZHLTL1` proof of this file also discharges the wave-2 scout's pieces 1-4
  without needing `IsOpen (voronoi_open)`. KIZHLTL4 discharged (wave 3,
  2026-09-30): the edge-dihedral capstone, consuming PA15's three ★ stars
  (`DIHX_SYM` / `FINITE_EDGE_X2` / `SUM_PAIR_2_SET`) + PA2 `GRUTOTI1_concl`
  directly (see its docstring; `MCELL_SUBSET_BALL_4`/`PACKING_BALL_BOUNDARY`
  turned out unnecessary). Still sorried: `MCELL_SET_NOT_EMPTY`,
  `QZYZMJC`, `KIZHLTL3` (no HL proof exists).
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto15
import Kepler.Text.PackingAuto17
import Mathlib

set_option maxHeartbeats 5000000
set_option maxHeartbeats 20000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## Private support chain (QZYZMJC.hl:43-496) -/

/-- HOL `mcell_set_2` (QZYZMJC.hl:43-58): `mcell_set` = the cells `mcell i V ul`
over `barV V 3` lists with `i <= 4` (the `i > 4` duplicates fold onto `mcell 4`
by `MCELL_EXPLICIT`). -/
private theorem mcellSet2 (V : Set V3) :
    mcellSet V = {X | ∃ i ul, X = mcell i V ul ∧ barV V 3 ul ∧ i ≤ 4} := by
  ext X
  simp only [mcellSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, ul, rfl, hb⟩
    rcases le_or_gt i 4 with hi | hi
    · exact ⟨i, ul, rfl, hb, hi⟩
    · refine ⟨4, ul, ?_, hb, le_refl 4⟩
      rw [mcell, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
      rfl
  · rintro ⟨i, ul, rfl, hb, _hi⟩
    exact ⟨i, ul, rfl, hb⟩

/-- NEEDS: marchal2.hl:2231 `VORONOI_LIST_3_SINGLETON_EXPLICIT` — SHIM
(2026-09-19): the parallel PackingAuto12 olean HAS landed in this checkout,
so the private `_p16` copy discharges to
`Kepler.Text.PackingAuto12.VORONOI_LIST_3_SINGLETON_EXPLICIT`
(statement-identical; still `sorry`ed upstream in Auto12 — a documented
transitive shim, deleting the statement duplication; delete the copy at
merge when Auto12's giant lands). -/
private theorem voronoiList3SingletonExplicit_p16 (V : Set V3) (ul : List V3)
    (_hp : Packing V) (_hs : saturated V) (_hb : barV V 3 ul) :
    ∃ a, voronoiList V ul = {a} ∧ a = circumcenter (setOfList ul) ∧
      hl ul = dist (hdV ul) a :=
  VORONOI_LIST_3_SINGLETON_EXPLICIT V ul _hp _hs _hb

/-- HOL `BARV_3_IMP_FINITE_lemma1` (QZYZMJC.hl:62-100): two list points of a
`barV V 3` simplex over a saturated packing are less than `4` apart (the
circumcenter of the simplex sees every list point at distance `< 2` by
saturatedness, so the diameter is `< 4`). -/
private theorem barV3ImpFinite1 {V : Set V3} {ul : List V3} {u v : V3}
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (huv : {u, v} ⊆ setOfList ul) : dist u v < 4 := by
  obtain ⟨a, ha1, _ha2, _ha3⟩ := voronoiList3SingletonExplicit_p16 V ul hp hs hb
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

/-- HOL `BARV_3_IMP_FINITE_lemma2` (QZYZMJC.hl:104-110): the whole list sits
in the radius-`4` ball around any of its points. -/
private theorem barV3ImpFinite2 {V : Set V3} {ul : List V3} {v : V3}
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hv : v ∈ setOfList ul) :
    setOfList ul ⊆ Metric.ball v 4 := by
  intro s hsmem
  refine barV3ImpFinite1 hp hs hb ?_
  intro x hx
  rcases (by simpa using hx : x = s ∨ x = v) with hx1 | hx1
  · rw [hx1]
    exact hsmem
  · rw [hx1]
    exact hv

/-- HOL `lemma_r_r'_fix2` (QZYZMJC.hl:114-133): the volume of a radial set cut
by a smaller normball scales as `(s / r)^3` (`s < r` is Vol1 `lemma_r_r'_fix`
= `Kepler.Geom.Volume.radialNorm.volume_scaling`; `s = r` is the identity
case via `C ⊆ ball x r` from `radial_norm`). -/
private theorem lemmaRRFix2 {C : Set V3} {x : V3} {r s : ℝ}
    (hm : MeasurableSet C) (hrad : radialNorm r x C) (hs0 : 0 < s) (hsr : s ≤ r) :
    MeasurableSet (C ∩ Metric.ball x s) ∧
      volume.real (C ∩ Metric.ball x s) = volume.real C * (s / r) ^ 3 := by
  rcases lt_or_eq_of_le hsr with hlt | heq
  · exact ⟨hm.inter Metric.isOpen_ball.measurableSet,
      radialNorm.volume_scaling hrad hs0 hlt⟩
  · have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hs0 hsr)
    refine ⟨hm.inter Metric.isOpen_ball.measurableSet, ?_⟩
    rw [heq, Set.inter_eq_left.mpr hrad.1]
    field_simp

/-- GIANT — HOL `MCELL_SET_NOT_EMPTY` (QZYZMJC.hl:137-496): a packing point
lies in a non-null Marchal cell (the `mcell 0` sliver around `v` is null, so
some `mcell i V ul`, `1 <= i <= 4`, is not).

Sorried: the HL proof is a 360-line refinement chain — vol-monotonicity over
the cell covering (NEEDS SLTSTLO1, NEEDS MEASURABLE_MCELL/Auto10), the null
decomposition of `rogers V vl` (NEEDS mcell0 = rogers DIFF ball), the
identification `voronoi_closed V v ∩ ball(v, sqrt 2)` with the union over
`barV V 3` lists truncating to `[v]` (NEEDS GLTVHUM/PackingAuto6), finiteness
by NEEDS KIUMVTC (PackingAuto5) + FINITE_SET_LIST_LEMMA (AJRIPQN.hl, not on
the Lean side), the `1 < sqrt 2` + `VOLUME_BALL` positivity contradiction,
and NEEDS LEPJBDJ (PackingAuto11) for `V ∩ mcell i V ul =
set_of_list (truncate_simplex (i - 1) ul)`. -/
private theorem mcellSetNotEmpty (V : Set V3) (v : V3) (hs : saturated V)
    (hp : Packing V) (hv : v ∈ V) :
    {X | mcellSet V X ∧ ¬nullSet X ∧ v ∈ V ∩ X} ≠ ∅ := by
  sorry

/-! ## QZYZMJC (QZYZMJC.hl:36-39, 503-1108) -/

/-- GIANT — HOL `QZYZMJC` (QZYZMJC.hl:503-1108, concl `QZYZMJC1_concl`
HL:36-39): the solid angles of the non-null Marchal cells around a packing
point sum to `4π`. The set `{X | mcell_set V X /\ v IN VX V X}` is first
rewritten to `{X | mcell_set V X /\ ~NULLSET X /\ v IN V INTER X}` (VX of a
null cell is empty; HDTFNFZ/PackingAuto10 identifies `VX` with `V ∩ X`
otherwise), proved FINITE (the pair `(i, ul)` ranges over a finite product —
`mcellSet2`, `barV3ImpFinite2`, LEPJBDJ, KIUMVTC), then each summand `sol v t`
is unfolded via `sol_spec` at a uniform small radius `r` (SKOLEM + inf of the
finitely many radiality witnesses URRPHBZ2/PackingAuto13, `lemmaRRFix2`),
`sum S vol` collapses to `vol (normball v r)` by pairwise-disjointness of the
cells (NEEDS AJRIPQN uniqueness; null cells contribute 0) and
`normball v r ⊆ voronoi_closed V v ⊆ UNIONS cells` (GLTVHUM/PackingAuto6 +
SLTSTLO1/PackingAuto13), giving `(3 / r^3) * vol (ball v r) = 4π`.

DISCHARGES: PackingAuto2.QZYZMJC_concl (PackingAuto2.lean:803). -/
theorem QZYZMJC : ∀ (V : Set V3) (v : V3), saturated V → Packing V → v ∈ V →
    setSum {X | mcellSet V X ∧ v ∈ VX V X} (fun t => sol v t) = 4 * Real.pi := by
  sorry

/-! ## KIZHLTL (KIZHLTL.hl) -/

/-- HOL `voronoi_open` (sphere.hl:304; pack1.hl:153). NEEDS:
PackingAuto1.voronoi_open (parallel worker) / the private PackingAuto2 copy —
identical body, private to those files; keep one public copy at merge. -/
private def voronoiOpenP16 (V : Set V3) (v : V3) : Set V3 :=
  {x | ∀ w ∈ V, w ≠ v → dist x v < dist x w}

/-! ### open-cell kit -/

private theorem p16_voronoi_in_ball {V : Set V3} {x v : V3} (hpack : Packing V)
    (hsat : saturated V) (hx : x ∈ voronoiOpenP16 V v) : dist x v < 2 := by
  obtain ⟨y, hyV, hyd⟩ := hsat x
  by_cases hyv : y = v
  · rw [← hyv]
    exact hyd
  · exact lt_trans (hx y hyV hyv) hyd

/-- HOL `Pack1.open_voronoi`: the open Voronoi cell is open (template:
PackingJGXZYGW.jg_open_voronoi, private there). -/
private theorem p16_open_voronoi (v : V3) (V : Set V3) (hV : Packing V)
    (hs : saturated V) : IsOpen (voronoiOpenP16 V v) := by
  classical
  rw [Metric.isOpen_iff]
  rintro x₀ hx₀
  have hD : dist x₀ v < 2 := p16_voronoi_in_ball hV hs hx₀
  set F : Set V3 := (V ∩ Metric.ball v 4) \ {v} with hFdef
  have hFsub : F ⊆ V ∩ Metric.ball 0 (‖v‖ + 4) := by
    intro w hw
    obtain ⟨hwS, hwb⟩ := hw.1
    refine ⟨hwS, Metric.mem_ball.2 ?_⟩
    rw [dist_zero_right]
    have htri : dist 0 w ≤ dist 0 v + dist v w := dist_triangle 0 v w
    simp only [dist_zero_left] at htri
    rw [Metric.mem_ball, dist_comm] at hwb
    linarith
  have hFfin : F.Finite := (hV.finite_inter_ball (‖v‖ + 4)).subset hFsub
  have hpos : ∀ w ∈ F, 0 < dist x₀ w - dist x₀ v := by
    intro w hw
    obtain ⟨⟨hwS, -⟩, hwv⟩ := hw
    have hwne : w ≠ v := by simpa using hwv
    linarith [hx₀ w hwS hwne]
  have hmin : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ F, dist x₀ v + m ≤ dist x₀ w := by
    by_cases hFe : F = ∅
    · refine ⟨1, one_pos, ?_⟩
      intro w hw
      exact absurd hw (by rw [hFe]; simp)
    · have hne : Set.Finite.toFinset hFfin |>.Nonempty := by
        obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hFe
        exact ⟨w, Set.Finite.mem_toFinset hFfin |>.mpr hw⟩
      have htne : ((Set.Finite.toFinset hFfin).image
          (fun w => dist x₀ w - dist x₀ v)).Nonempty := by
        obtain ⟨w, hw⟩ := hne
        exact ⟨dist x₀ w - dist x₀ v, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
      refine ⟨(Set.Finite.toFinset hFfin).image
        (fun w : V3 => dist x₀ w - dist x₀ v) |>.min' htne, ?_, ?_⟩
      · rcases Finset.mem_image.mp (Finset.min'_mem _ htne) with ⟨w₀, hw₀, hw₀eq⟩
        rw [← hw₀eq]
        exact hpos w₀ (Set.Finite.mem_toFinset hFfin |>.mp hw₀)
      · intro w hw
        have hwT : w ∈ Set.Finite.toFinset hFfin := (Set.Finite.mem_toFinset hFfin).mpr hw
        have himg : (fun w : V3 => dist x₀ w - dist x₀ v) w ∈
            (Set.Finite.toFinset hFfin).image (fun w : V3 => dist x₀ w - dist x₀ v) :=
          Finset.mem_image.mpr ⟨w, hwT, rfl⟩
        have hle := Finset.min'_le _ _ himg
        linarith
  obtain ⟨m, hmpos, hmle⟩ := hmin
  refine ⟨min (m / 3) ((2 - dist x₀ v) / 3), lt_min (by linarith) (by linarith), ?_⟩
  intro y hy
  rw [Metric.mem_ball] at hy
  have hy1 := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 := lt_of_lt_of_le hy (min_le_right _ _)
  intro w hwS hwv
  by_cases hwF : w ∈ F
  · have hwb : dist w v < 4 := by
      have h5 := hwF.1.2
      rw [Metric.mem_ball] at h5
      exact h5
    have h1 : dist x₀ w ≤ dist x₀ y + dist y w := dist_triangle x₀ y w
    have h2 := hmle w hwF
    have h3 : dist y v ≤ dist y x₀ + dist x₀ v := dist_triangle y x₀ v
    linarith [hy1, hy2, h1, h2, h3, dist_comm x₀ y]
  · have hw4 : (4 : ℝ) ≤ dist v w := by
      by_contra hc
      exact hwF ⟨⟨hwS, by rw [Metric.mem_ball]; linarith [lt_of_not_ge hc, dist_comm v w]⟩,
        by simpa using hwv⟩
    have h1 : dist v w ≤ dist v y + dist y w := dist_triangle v y w
    have h2 : dist y v ≤ dist y x₀ + dist x₀ v := dist_triangle y x₀ v
    have h3 : dist v y = dist y v := dist_comm v y
    linarith [hy1, hy2]

/-- The shift-by-multiple quadratic identity: `‖a - s•d‖² = ‖a‖² - 2s⟪a,d⟫ +
s²‖d‖²`. -/
private theorem p16_norm_smul_sq (a d : V3) (s : ℝ) :
    ‖a - s • d‖ ^ 2 = ‖a‖ ^ 2 - 2 * s * inner ℝ a d + s ^ 2 * inner ℝ d d := by
  have h0 : ‖a - s • d‖ ^ 2 = inner ℝ (a - s • d) (a - s • d) :=
    (real_inner_self_eq_norm_sq _).symm
  rw [h0]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial, real_inner_comm, real_inner_self_eq_norm_sq]
  ring

/-- A tie point (`dist x w = dist x v`, `v ≠ w` in the packing, `x ≠ v`) is
not an interior point of the closed Voronoi cell of `v`: moving from `x`
towards `w`'s side leaves the cell (squared-distance computation along the
direction `v - w`). -/
private theorem p16_tie_not_interior {V : Set V3} {v w x : V3} {ε : ℝ}
    (hpack : Packing V) (hv : v ∈ V) (hwV : w ∈ V) (hwv : w ≠ v) (hxv : x ≠ v)
    (htie : dist x w = dist x v)
    (hball : Metric.ball x ε ⊆ voronoiClosed V v) (hε : 0 < ε) : False := by
  have hd2 : (2 : ℝ) ≤ dist v w := hpack.dist_ge_two hv hwV (Ne.symm hwv)
  have hdpos : 0 < ‖v - w‖ := by
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le (by norm_num) hd2
  have hD1 : (1 : ℝ) < ‖v - w‖ := by
    have hnd : ‖v - w‖ = dist v w := by rw [dist_eq_norm]
    rw [hnd]
    linarith
  set s : ℝ := ε / (2 * ‖v - w‖ ^ 2) with hs
  have spos : 0 < s := by positivity
  set z : V3 := x - s • (v - w) with hz
  -- z is in the ε-ball around x
  have hzball : z ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hzx : z - x = -(s • (v - w)) := by rw [hz]; abel
    rw [hzx, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos spos, hs]
    have hpos2 : (0 : ℝ) < 2 * ‖v - w‖ ^ 2 := by nlinarith [hD1]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpos2]
    exact mul_lt_mul_of_pos_left (by nlinarith [hD1]) hε
  -- the key identity: the (v-w)-components of (x - v) and (x - w) differ
  have key : inner ℝ (x - v) (v - w) - inner ℝ (x - w) (v - w) = -‖v - w‖ ^ 2 := by
    have hsubeq : ((x - v : V3) - (x - w)) = w - v := by abel
    rw [← inner_sub_left, hsubeq]
    have hneg : ((w - v : V3)) = -(v - w) := by abel
    rw [hneg, inner_neg_left, real_inner_self_eq_norm_sq]
  -- squared distances at z (the shift-by-multiple-of-a-vector quadratic identity)
  have e1 : ‖(x - w) - s • (v - w)‖ ^ 2
      = ‖x - w‖ ^ 2 - 2 * s * inner ℝ (x - w) (v - w)
        + s ^ 2 * inner ℝ (v - w) (v - w) :=
    p16_norm_smul_sq (x - w) (v - w) s
  have e2 : ‖(x - v) - s • (v - w)‖ ^ 2
      = ‖x - v‖ ^ 2 - 2 * s * inner ℝ (x - v) (v - w)
        + s ^ 2 * inner ℝ (v - w) (v - w) :=
    p16_norm_smul_sq (x - v) (v - w) s
  have hdir : inner ℝ (v - w) (v - w) = ‖v - w‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hsq2 : ‖(x - w) - s • (v - w)‖ ^ 2 < ‖(x - v) - s • (v - w)‖ ^ 2 := by
    rw [e1, e2]
    have hnormeq : ‖x - w‖ ^ 2 = ‖x - v‖ ^ 2 := by
      rw [← dist_eq_norm, ← dist_eq_norm, htie]
    rw [hnormeq, hdir]
    have hrel : inner ℝ (x - v) (v - w) = inner ℝ (x - w) (v - w) - ‖v - w‖ ^ 2 := by
      linarith [key]
    rw [hrel]
    have hne : ‖v - w‖ ≠ 0 := ne_of_gt hdpos
    have h1' : (0:ℝ) < s * ‖v - w‖ ^ 2 :=
      mul_pos spos (sq_pos_of_ne_zero hne)
    have hsterm : (0:ℝ) < 2 * s * ‖v - w‖ ^ 2 := by linarith
    nlinarith
  -- z ∉ voronoiClosed V v
  have hzc : z ∉ voronoiClosed V v := by
    intro hmem
    have hle : dist z v ≤ dist z w := hmem w hwV
    have h1 : dist z w = ‖(x - w) - s • (v - w)‖ := by
      rw [dist_eq_norm]
      exact congrArg Norm.norm (by rw [sub_right_comm])
    have h2 : dist z v = ‖(x - v) - s • (v - w)‖ := by
      rw [dist_eq_norm]
      exact congrArg Norm.norm (by rw [sub_right_comm])
    rw [h1, h2] at hle
    have hnnB : 0 ≤ ‖(x - v) - s • (v - w)‖ := norm_nonneg _
    have hcontr : ‖(x - v) - s • (v - w)‖ ^ 2 ≤ ‖(x - w) - s • (v - w)‖ ^ 2 :=
      pow_le_pow_left₀ hnnB hle 2
    exact absurd hcontr (not_le.mpr hsq2)
  exact hzc (hball hzball)


/-- The interior of the closed Voronoi cell is contained in the open cell
(ties only occur on the boundary). -/
private theorem p16_interior_subset_open (V : Set V3) (v : V3) (hpack : Packing V)
    (hsat : saturated V) (hv : v ∈ V) :
    interior (voronoiClosed V v) ⊆ voronoiOpenP16 V v := by
  intro x hx w hw hwv
  by_contra hcon
  have hc : x ∈ voronoiClosed V v := interior_subset hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hball' : Metric.ball x ε ⊆ voronoiClosed V v :=
    Set.Subset.trans hball interior_subset
  have hxv : x ≠ v := by
    intro h
    subst h
    have hxx : dist x x = 0 := dist_self x
    have dw : 0 ≤ dist x w := dist_nonneg
    have hx0 : dist x w = 0 := by linarith [hcon, hxx, dw]
    exact hwv (dist_eq_zero.mp hx0).symm
  have hle : dist x v ≤ dist x w := hc w hw
  have htie : dist x w = dist x v := le_antisymm (not_lt.mp hcon) hle
  exact p16_tie_not_interior (V := V) (v := v) (w := w) hpack hv hw hwv hxv htie hball' hε

/-- HOL `Pack2.MEASURE_VORONOI_CLOSED_OPEN`: the open and closed Voronoi cells
of a packing point have equal volume. -/
private theorem p16_measure_voronoi_closed_open (V : Set V3) (v : V3)
    (hpack : Packing V) (hsat : saturated V) (hv : v ∈ V) :
    volume.real (voronoiClosed V v) = volume.real (voronoiOpenP16 V v) := by
  classical
  have hsub : voronoiOpenP16 V v ⊆ voronoiClosed V v := by
    intro x hx w hw
    by_cases h : w = v
    · subst h; simp [voronoiClosed]
    · exact le_of_lt (hx w hw h)
  have hopen : IsOpen (voronoiOpenP16 V v) := p16_open_voronoi v V hpack hsat
  have hmeasO : MeasurableSet (voronoiOpenP16 V v) := hopen.measurableSet
  have hclos : IsClosed (voronoiClosed V v) := CLOSED_VORONOI_CLOSED V v
  have hmeasC : MeasurableSet (voronoiClosed V v) := hclos.measurableSet
  have hconv : Convex ℝ (voronoiClosed V v) := CONVEX_VORONOI_CLOSED V v
  have hbsub : voronoiClosed V v ⊆ Metric.ball v 2 := VORONOI_BALL2 V v hsat
  have hltb : volume (Metric.ball v 2) < ⊤ := by
    rw [EuclideanSpace.volume_ball_fin_three]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top
  have hltC : volume (voronoiClosed V v) < ⊤ := lt_of_le_of_lt (measure_mono hbsub) hltb
  have hltO : volume (voronoiOpenP16 V v) < ⊤ :=
    lt_of_le_of_lt (measure_mono (hsub.trans hbsub)) hltb
  -- interior(closed) ⊆ open, so closed \ open ⊆ frontier(closed) (closed set)
  have hint : interior (voronoiClosed V v) ⊆ voronoiOpenP16 V v :=
    p16_interior_subset_open V v hpack hsat hv
  have hfront : voronoiClosed V v \ voronoiOpenP16 V v ⊆ frontier (voronoiClosed V v) := by
    rw [hclos.frontier_eq]
    intro x hx
    rw [Set.mem_sdiff] at hx
    exact ⟨hx.1, fun hm => hx.2 (hint hm)⟩
  have hnull : volume (voronoiClosed V v \ voronoiOpenP16 V v) = 0 :=
    measure_mono_null hfront (Convex.addHaar_frontier volume hconv)
  -- additivity on the measurable partition
  have hsd : MeasurableSet (voronoiClosed V v \ voronoiOpenP16 V v) := hmeasC.diff hmeasO
  have hadd := measure_union_add_inter (μ := volume)
    (voronoiClosed V v \ voronoiOpenP16 V v) hmeasO
  have hun : voronoiClosed V v \ voronoiOpenP16 V v ∪ voronoiOpenP16 V v
      = voronoiClosed V v := Set.sdiff_union_of_subset hsub
  have hint0 : (voronoiClosed V v \ voronoiOpenP16 V v) ∩ voronoiOpenP16 V v = ∅ := by
    ext x; simp [Set.mem_inter_iff]
  rw [hun, hint0, measure_empty, add_zero] at hadd
  have hneD : volume (voronoiClosed V v \ voronoiOpenP16 V v) ≠ ⊤ := by
    rw [hnull]
    exact ENNReal.zero_ne_top
  rw [Measure.real_def, Measure.real_def, hadd, ENNReal.toReal_add hneD hltO.ne]
  simp only [hnull, ENNReal.toReal_zero, zero_add]

/-! ### a.e.-disjoint finite unions in `volume.real` -/

/-- a.e.-disjoint finite union in ENNReal. -/
private theorem p16_ae_biUnion {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → Set V3)
    (hm : ∀ i ∈ s, MeasurableSet (f i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → volume (f i ∩ f j) = 0) :
    volume (⋃ i ∈ s, f i) = ∑ i ∈ s, volume (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have himem : i ∈ insert i s := Finset.mem_insert_self _ _
    have hms : MeasurableSet (⋃ j ∈ s, f j) :=
      MeasurableSet.biUnion (Set.Finite.countable s.finite_toSet)
        (fun j hj => hm j (Finset.mem_insert_of_mem hj))
    have hnull : volume ((f i) ∩ ⋃ j ∈ s, f j) = 0 := by
      have heq : ((f i) ∩ ⋃ j ∈ s, f j) = ⋃ j ∈ (s : Set ι), (f i ∩ f j) := by
        ext x
        simp [Set.mem_inter_iff]
      rw [heq, MeasureTheory.measure_biUnion_null_iff
        (Set.Finite.countable s.finite_toSet)]
      intro j hj
      exact hpair i himem j (Finset.mem_insert_of_mem hj)
        (fun hcon => hi (by rw [hcon]; exact hj))
    have hadd := MeasureTheory.measure_union_add_inter (μ := volume) (f i) hms
    rw [hnull, add_zero] at hadd
    rw [Finset.set_biUnion_insert]
    rw [Finset.sum_insert hi]
    calc volume ((f i) ∪ ⋃ x ∈ (s : Set ι), f x)
        = volume ((f i) ∪ ⋃ j ∈ s, f j) := rfl
      _ = volume (f i) + volume (⋃ j ∈ s, f j) := hadd
      _ = volume (f i) + ∑ j ∈ s, volume (f j) := by
            rw [ih (fun j hj => hm j (Finset.mem_insert_of_mem hj))
              (fun j hj k hk hjk => hpair j (Finset.mem_insert_of_mem hj) k
                (Finset.mem_insert_of_mem hk) hjk)]

/-- The `volume.real` form of the a.e.-disjoint finite union identity. -/
private theorem p16_vol_biUnion_finset_real {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → Set V3) (hm : ∀ i ∈ s, MeasurableSet (f i))
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → volume (f i ∩ f j) = 0)
    (htop : ∀ i ∈ s, volume (f i) ≠ ⊤) :
    volume.real (⋃ i ∈ s, f i) = ∑ i ∈ s, volume.real (f i) := by
  have hae := p16_ae_biUnion s f hm hpair
  have hsumne : ∑ i ∈ s, volume (f i) ≠ ⊤ := ENNReal.sum_ne_top.mpr htop
  have hutop : volume (⋃ i ∈ s, f i) ≠ ⊤ := by rw [hae]; exact hsumne
  show (volume (⋃ i ∈ s, f i)).toReal = ∑ i ∈ s, (volume (f i)).toReal
  rw [hae]
  exact ENNReal.toReal_sum (f := fun i => volume (f i)) (fun i hi => htop i hi)

/-- The master bridge (HOL `MEASURE_NEGLIGIBLE_UNIONS` + `..._IMAGE` in one):
for a finite family of measurable sets given as the (injective) image of a
finite set, pairwise a.e.-disjoint off duplicates, the measure of the union
equals the `setSum` of the measures. -/
private theorem p16_measure_setSum_image {α : Type} {S : Set α} (hS : S.Finite)
    (g : α → Set V3)
    (hm : ∀ t ∈ S, MeasurableSet (g t))
    (hginj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b)
    (hd : ∀ a ∈ S, ∀ b ∈ S, g a ≠ g b → volume (g a ∩ g b) = 0)
    (htop : ∀ t ∈ S, volume (g t) ≠ ⊤) :
    volume.real (⋃₀ (g '' S)) = setSum S (fun t => volume.real (g t)) := by
  classical
  by_cases hS0 : S.Finite
  · unfold setSum
    rw [dif_pos hS0]
    have hkey : ⋃₀ (g '' S) = ⋃ t ∈ hS0.toFinset, g t := by
      ext x
      rw [Set.mem_sUnion, Set.mem_iUnion₂]
      constructor
      · rintro ⟨y, hy, hxy⟩
        obtain ⟨a, haS, rfl⟩ := hy
        exact ⟨a, (Set.Finite.mem_toFinset hS0).mpr haS, hxy⟩
      · rintro ⟨t, ht, hxy⟩
        exact ⟨g t, ⟨t, (Set.Finite.mem_toFinset hS0).mp ht, rfl⟩, hxy⟩
    rw [hkey]
    refine p16_vol_biUnion_finset_real (ι := α) (s := hS0.toFinset) (f := g)
      (fun t ht => hm t ((Set.Finite.mem_toFinset hS0).mp ht)) ?_ ?_
    · intro a ha b hb hne
      exact hd a ((Set.Finite.mem_toFinset hS0).mp ha) b
        ((Set.Finite.mem_toFinset hS0).mp hb)
        (fun hcon => hne (hginj a ((Set.Finite.mem_toFinset hS0).mp ha) b
          ((Set.Finite.mem_toFinset hS0).mp hb) hcon))
    · intro t ht
      exact htop t ((Set.Finite.mem_toFinset hS0).mp ht)
  · exact absurd hS hS0

/-- Nonzero-vector hyperplanes are null (the `NEGLIGIBLE_INTER_VORONOI_CLOSED`
core; prototype validated by the upfzbzm wave-2 scout). -/
private theorem p16_hyperplane_null (a : V3) (b : ℝ) (ha : a ≠ 0) :
    volume {x : V3 | inner ℝ x a = b} = 0 := by
  classical
  set K : Submodule ℝ V3 := (Submodule.span ℝ {a})ᗮ with hK
  have haa : (inner ℝ a a : ℝ) ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  set p : V3 := (b / inner ℝ a a) • a with hp
  have hpin : inner ℝ p a = b := by
    rw [hp, inner_smul_left, starRingEnd_apply, star_trivial]
    exact div_mul_cancel₀ b haa
  set s : AffineSubspace ℝ V3 := AffineSubspace.mk' p K with hs
  have hmem : ∀ x : V3, x ∈ s ↔ (∀ u ∈ (Submodule.span ℝ {a} : Submodule ℝ V3),
      inner ℝ u (x -ᵥ p) = 0) := by
    intro x
    simp only [hs, AffineSubspace.mem_mk', hK, Submodule.mem_orthogonal]
  have hcoe : (s : Set V3) = {x : V3 | inner ℝ x a = b} := by
    ext x
    refine (hmem x).trans ?_
    rw [Set.mem_setOf_eq]
    simp only [vsub_eq_sub]
    constructor
    · intro hx
      have hx' := hx a (Submodule.subset_span (Set.mem_singleton a))
      rw [inner_sub_right, real_inner_comm x a, real_inner_comm p a, hpin] at hx'
      linarith
    · intro hx u hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [inner_smul_left, starRingEnd_apply, star_trivial, inner_sub_right,
        real_inner_comm x a, real_inner_comm p a, hx, hpin, sub_self, mul_zero]
  have hne : s ≠ ⊤ := by
    intro h
    have hx : p + a ∈ (s : Set V3) := by rw [h]; simp
    rw [hcoe, Set.mem_setOf_eq, inner_add_left, hpin] at hx
    exact haa (by linarith)
  have key := Measure.addHaar_affineSubspace volume s hne
  rwa [hcoe] at key

/-- HOL `Pack2.NEGLIGIBLE_INTER_VORONOI_CLOSED`: the closed Voronoi cells of
two distinct packing points meet inside the bisector hyperplane
`inner x (t - s) = (‖t‖² - ‖s‖²)/2`, which is null. -/
private theorem p16_closed_voronoi_inter_null (V : Set V3) {s t : V3}
    (hs : s ∈ V) (ht : t ∈ V) (hne : s ≠ t) :
    volume (voronoiClosed V s ∩ voronoiClosed V t) = 0 := by
  have hsub : voronoiClosed V s ∩ voronoiClosed V t
      ⊆ {x : V3 | inner ℝ x (t - s) = (‖t‖ ^ 2 - ‖s‖ ^ 2) / 2} := by
    rintro x ⟨hx1, hx2⟩
    refine Set.mem_setOf_eq.mpr ?_
    have h1 : dist x s ≤ dist x t := hx1 t ht
    have h2 : dist x t ≤ dist x s := hx2 s hs
    have heq : dist x s = dist x t := le_antisymm h1 h2
    have hsq : ‖x - s‖ ^ 2 = ‖x - t‖ ^ 2 := by
      rw [← dist_eq_norm, ← dist_eq_norm, heq]
    have e1 : ‖x - s‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x s + inner ℝ s s := by
      have h := p16_norm_smul_sq x s 1
      simpa using h
    have e2 : ‖x - t‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x t + inner ℝ t t := by
      have h := p16_norm_smul_sq x t 1
      simpa using h
    have hss : inner ℝ s s = ‖s‖ ^ 2 := real_inner_self_eq_norm_sq s
    have htt : inner ℝ t t = ‖t‖ ^ 2 := real_inner_self_eq_norm_sq t
    rw [e1, e2, hss, htt] at hsq
    rw [inner_sub_right]
    linarith
  have hne0 : t - s ≠ 0 := fun hc => hne (sub_eq_zero.mp hc).symm
  exact measure_mono_null hsub (p16_hyperplane_null (t - s) _ hne0)

/-- `mcell i` caps at `i = 4` (HOL `MCELL_EXPLICIT`). -/
private theorem p16_mcell_cap4 (V : Set V3) (ul : List V3) (i : ℕ) :
    mcell i V ul = mcell (min i 4) V ul := by
  rcases lt_or_ge i 4 with h | h
  · rw [min_eq_left h.le]
  · rw [min_eq_right h, (MCELL_EXPLICIT i V ul).2.2.2.2 h]
    exact ((MCELL_EXPLICIT 4 V ul).2.2.2.2 le_rfl).symm

/-- HOL `SUM_EQ` in `setSum` form. -/
private theorem p16_setSumCongr {α : Type*} {s : Set α} {f g : α → ℝ}
    (h : ∀ a ∈ s, f a = g a) : setSum s f = setSum s g := by
  classical
  by_cases hs0 : s.Finite
  · unfold setSum
    rw [dif_pos hs0, dif_pos hs0]
    exact Finset.sum_congr rfl fun a ha =>
      h a ((Set.Finite.mem_toFinset hs0).mp ha)
  · unfold setSum
    rw [dif_neg hs0, dif_neg hs0]

/-- HOL `VOLUME_BALL` in `volume.real` form (`q ≥ 0`). -/
private theorem p16_volume_ball_real {c : V3} {q : ℝ} (hq : 0 ≤ q) :
    volume.real (Metric.ball c q) = 4 * Real.pi / 3 * q ^ 3 := by
  rw [Measure.real_def, EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hq,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ Real.pi * 4 / 3)]
  ring

private theorem p16_volume_ball_lt_top {c : V3} {q : ℝ} (hq : 0 ≤ q) :
    volume (Metric.ball c q) < ⊤ := by
  rw [EuclideanSpace.volume_ball_fin_three]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    ENNReal.ofReal_lt_top

/-- GIANT — HOL `KIZHLTL1` (KIZHLTL.hl:46-279, concl `pack_concl.hl:201-203`):
the total volume of the Marchal cells inside `ball 0 r` is at most the total
Voronoi volume of the packing points in the ball, up to `-24/3 * π * r^2`
(an explicit witness `c`). Core: `sum S vol <= vol (UNIONS S) <= vol (ball 0 r)`
(NEEDS FINITE_MCELL_SET_LEMMA/marchal3, NEEDS MEASURABLE_MCELL/Auto10,
NEEDS AJRIPQN uniqueness); the covering inequality `voronoi_closed`-union ⊇
`ball 0 (r - 2)` (NEEDS MEASURE_NEGLIGIBLE_UNIONS_IMAGE, NEEDS
MEASURABLE_VORONOI_CLOSED/NEGLIGIBLE_INTER_VORONOI_CLOSED/Pack2, NEEDS
TIWWFYQ/PackingAuto5), with `4/3 π r^3 - 24/3 π r^2 <= 4/3 π (r - 2)^3` for
`6 <= r` and the trivial-sign argument below `6`; `voronoi_open` and
`voronoi_closed` have equal volumes (NEEDS MEASURE_VORONOI_CLOSED_OPEN).

DISCHARGES: PackingAuto2.KIZHLTL1_concl (PackingAuto2.lean:808; the private
`voronoiOpenP16` copy is delta-equivalent to PackingAuto2's `voronoiOpen`). -/
theorem KIZHLTL1 : ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V →
    1 ≤ r →
    setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} volume.real +
        c * r ^ 2 ≤
      setSum (V ∩ Metric.ball 0 r) (fun u => volume.real (voronoiOpenP16 V u)) := by
  intro V
  by_cases hmain : saturated V ∧ Packing V
  · obtain ⟨hs, hp⟩ := hmain
    refine ⟨-((24 : ℝ) / 3) * Real.pi, ?_⟩
    intro r _hs' _hp' hr
    classical
    have hr0 : (0 : ℝ) ≤ r := le_trans (by norm_num) hr
    set S : Set (Set V3) := {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} with hSdef
    have hSfin : S.Finite := FINITE_MCELL_SET_LEMMA V r hp hs
    have hballfin : volume (Metric.ball (0 : V3) r) ≠ ⊤ :=
      ne_of_lt (p16_volume_ball_lt_top hr0)
    -- Step A (HL:58-121): measurability, pairwise a.e.-disjointness, boundedness
    have hmeas : ∀ X ∈ S, MeasurableSet X := by
      intro X hX
      have hX' : X ⊆ Metric.ball 0 r ∧ mcellSet V X := hX
      obtain ⟨i, ul, rfl, hb⟩ := Set.mem_setOf.mp hX'.2
      exact MEASURABLE_MCELL V ul i hs hp hb
    have hpair : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → volume (s ∩ t) = 0 := by
      intro s hs' t ht' hne
      have hsS : s ⊆ Metric.ball 0 r ∧ mcellSet V s := hs'
      have htS : t ⊆ Metric.ball 0 r ∧ mcellSet V t := ht'
      obtain ⟨i, ul, rfl, hb⟩ := Set.mem_setOf.mp hsS.2
      obtain ⟨i', ul', rfl, hb'⟩ := Set.mem_setOf.mp htS.2
      by_contra hnn
      have hcap1 : mcell i V ul = mcell (min i 4) V ul := p16_mcell_cap4 V ul i
      have hcap2 : mcell i' V ul' = mcell (min i' 4) V ul' := p16_mcell_cap4 V ul' i'
      have hmem1 : min i 4 ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
        rcases Nat.lt_or_ge i 4 with h4 | h4
        · rw [min_eq_left h4.le]; simp; omega
        · rw [min_eq_right h4]; simp
      have hmem2 : min i' 4 ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
        rcases Nat.lt_or_ge i' 4 with h4 | h4
        · rw [min_eq_left h4.le]; simp; omega
        · rw [min_eq_right h4]; simp
      have hv : ¬nullSet (mcell (min i 4) V ul ∩ mcell (min i' 4) V ul') := by
        rw [← hcap1, ← hcap2]
        exact fun hc => hnn hc
      obtain ⟨_, heq⟩ := AJRIPQN V ul ul' (min i 4) (min i' 4) hs hp hb hb' hmem1 hmem2 hv
      exact hne (by rw [hcap1, hcap2, heq])
    have htop : ∀ X ∈ S, volume X ≠ ⊤ := by
      intro X hX hc
      have hX' : X ⊆ Metric.ball 0 r ∧ mcellSet V X := hX
      have h1 : volume X ≤ volume (Metric.ball (0 : V3) r) := measure_mono hX'.1
      have h2 : volume (Metric.ball (0 : V3) r) < ⊤ := p16_volume_ball_lt_top hr0
      rw [hc] at h1
      exact absurd h2 (not_lt.2 h1)
    have hstepA : setSum S volume.real = volume.real (⋃₀ S) := by
      have hkey := p16_measure_setSum_image hSfin (g := id) hmeas
        (fun a _ b _ h => h) hpair (fun t ht => htop t ht)
      rw [Set.image_id] at hkey
      exact hkey.symm
    have hsubBall : ⋃₀ S ⊆ Metric.ball (0 : V3) r := by
      intro x hx
      obtain ⟨X, hX, hxX⟩ := hx
      exact hX.1 hxX
    have hstepB : volume.real (⋃₀ S) ≤ volume.real (Metric.ball (0 : V3) r) :=
      ENNReal.toReal_mono hballfin (measure_mono hsubBall)
    -- Step C (HL:136-238): the closed-Voronoi union over V ∩ ball(0, r)
    have hA : (V ∩ Metric.ball 0 r).Finite := hp.finite_inter_ball r
    have hC0 : setSum (V ∩ Metric.ball 0 r)
        (fun u => volume.real (voronoiOpenP16 V u))
        = setSum (V ∩ Metric.ball 0 r) (fun u => volume.real (voronoiClosed V u)) := by
      refine p16_setSumCongr fun u hu => ?_
      exact (p16_measure_voronoi_closed_open V u hp hs hu.1).symm
    have hC1 : volume.real
        (⋃₀ ((fun u => voronoiClosed V u) '' (V ∩ Metric.ball 0 r)))
        = setSum (V ∩ Metric.ball 0 r) (fun u => volume.real (voronoiClosed V u)) := by
      have hmeasC : ∀ t ∈ V ∩ Metric.ball 0 r,
          MeasurableSet ((fun u => voronoiClosed V u) t) :=
        fun t _ => (CLOSED_VORONOI_CLOSED V t).measurableSet
      have hinj : ∀ a ∈ V ∩ Metric.ball 0 r, ∀ b ∈ V ∩ Metric.ball 0 r,
          (fun u => voronoiClosed V u) a = (fun u => voronoiClosed V u) b → a = b := by
        intro a ha b hb hab
        have hamem : a ∈ voronoiClosed V a := by
          intro w _
          rw [dist_self]
          exact dist_nonneg
        have habm : a ∈ (fun u => voronoiClosed V u) b := by rw [← hab]; exact hamem
        have hz : dist a b = 0 :=
          le_antisymm (by simpa using habm a ha.1) dist_nonneg
        exact dist_eq_zero.mp hz
      have hdisj : ∀ a ∈ V ∩ Metric.ball 0 r, ∀ b ∈ V ∩ Metric.ball 0 r,
          (fun u => voronoiClosed V u) a ≠ (fun u => voronoiClosed V u) b →
            volume ((fun u => voronoiClosed V u) a ∩ (fun u => voronoiClosed V u) b) = 0 := by
        intro a ha b hb hne
        exact p16_closed_voronoi_inter_null V ha.1 hb.1 (fun hcon => hne (by rw [hcon]))
      have htopC : ∀ t ∈ V ∩ Metric.ball 0 r,
          volume ((fun u => voronoiClosed V u) t) ≠ ⊤ := by
        intro t _ hc
        have h1 : volume (voronoiClosed V t) ≤ volume (Metric.ball t 2) :=
          measure_mono (VORONOI_BALL2 V t hs)
        have h2 : volume (Metric.ball t 2) < ⊤ := p16_volume_ball_lt_top (by norm_num)
        rw [hc] at h1
        exact absurd h2 (not_lt.2 h1)
      exact p16_measure_setSum_image hA (fun u => voronoiClosed V u) hmeasC hinj hdisj htopC
    have hC2sub : Metric.ball (0 : V3) (r - 2) ⊆
        ⋃₀ ((fun u => voronoiClosed V u) '' (V ∩ Metric.ball 0 r)) := by
      intro x hx
      have hxr : dist x 0 < r - 2 := Metric.mem_ball.1 hx
      obtain ⟨v, hvV, hxv⟩ := TIWWFYQ V x hp hs
      obtain ⟨y, hyV, hyd⟩ := hs x
      have h1 : dist x v ≤ dist x y := hxv y hyV
      have t1 : dist v 0 ≤ dist v x + dist x 0 := dist_triangle v x 0
      have hvx : dist v x = dist x v := dist_comm v x
      have hcx : dist x 0 = dist 0 x := dist_comm x 0
      rw [dist_comm x 0] at hxr
      refine ⟨voronoiClosed V v, ⟨v, ⟨hvV, Metric.mem_ball.2 ?_⟩, rfl⟩, hxv⟩
      linarith
    have hC2top : volume
        (⋃₀ ((fun u => voronoiClosed V u) '' (V ∩ Metric.ball 0 r))) ≠ ⊤ := by
      intro hc
      have hsub : ⋃₀ ((fun u => voronoiClosed V u) '' (V ∩ Metric.ball 0 r)) ⊆
          Metric.ball (0 : V3) (r + 2) := by
        intro x hx
        rw [Set.mem_sUnion] at hx
        obtain ⟨Y, hY, hxY⟩ := hx
        obtain ⟨u, hu, rfl⟩ := hY
        obtain ⟨y, hyV, hyd⟩ := hs x
        have hur : dist u 0 < r := Metric.mem_ball.1 hu.2
        have hstep : dist x u ≤ dist x y := hxY y hyV
        have t1 : dist 0 x ≤ dist 0 u + dist u x := dist_triangle 0 u x
        have hux : dist u x = dist x u := dist_comm u x
        have hu0 : dist u 0 = dist 0 u := dist_comm u 0
        have hx0 : dist x 0 = dist 0 x := dist_comm x 0
        refine Metric.mem_ball.2 ?_
        linarith
      have hlt : volume
          (⋃₀ ((fun u => voronoiClosed V u) '' (V ∩ Metric.ball 0 r))) < ⊤ :=
        lt_of_le_of_lt (measure_mono hsub) (p16_volume_ball_lt_top (c := (0 : V3))
          (q := r + 2) (by linarith))
      rw [hc] at hlt
      exact lt_irrefl ⊤ hlt
    have hC2 : volume.real (Metric.ball (0 : V3) (r - 2)) ≤
        volume.real (⋃₀ ((fun u => voronoiClosed V u) '' (V ∩ Metric.ball 0 r))) :=
      ENNReal.toReal_mono hC2top (measure_mono hC2sub)
    -- Step D (HL:240-279): the volume arithmetic and assembly
    have hD1 : setSum S volume.real ≤ volume.real (Metric.ball (0 : V3) r) := by
      rw [hstepA]; exact hstepB
    have hD2 : volume.real (Metric.ball (0 : V3) r)
        + (-((24 : ℝ) / 3) * Real.pi) * r ^ 2
        ≤ setSum (V ∩ Metric.ball 0 r) (fun u => volume.real (voronoiOpenP16 V u)) := by
      rw [hC0, ← hC1]
      rcases lt_or_ge r 6 with h6 | h6
      · have h6r : (0 : ℝ) ≤ 6 - r := by linarith
        have hp6rr : (0 : ℝ) ≤ Real.pi * (6 - r) * r * r :=
          mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le h6r) hr0) hr0
        have hmono : Real.pi * r ^ 3 ≤ 6 * Real.pi * r ^ 2 := by nlinarith [hp6rr]
        rw [p16_volume_ball_real hr0]
        have hnn : 0 ≤ volume.real
            (⋃₀ ((fun u => voronoiClosed V u) '' (V ∩ Metric.ball 0 r))) :=
          measureReal_nonneg
        linarith [hmono, hnn]
      · have hr2 : (0 : ℝ) ≤ r - 2 := by linarith
        have hexp : (r - 2) ^ 3 = r ^ 3 - 6 * r ^ 2 + 12 * r - 8 := by ring
        have hkey2 : Real.pi * (32 / 3) ≤ Real.pi * (16 * r) :=
          mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
        have hballarith : volume.real (Metric.ball (0 : V3) r)
            + (-((24 : ℝ) / 3) * Real.pi) * r ^ 2
            ≤ volume.real (Metric.ball (0 : V3) (r - 2)) := by
          rw [p16_volume_ball_real hr0, p16_volume_ball_real hr2, hexp]
          linarith
        linarith [hballarith, hC2]
    linarith
  · exact ⟨0, fun r hs' hp' _ => absurd ⟨hs', hp'⟩ hmain⟩

/-! ### KIZHLTL2 support kit -/

/-- HOL `SUM_LE` in `setSum` form. -/
private theorem p16_setSum_mono {α : Type*} {s : Set α} (hs : s.Finite) (f g : α → ℝ)
    (h : ∀ a ∈ s, f a ≤ g a) : setSum s f ≤ setSum s g := by
  unfold setSum
  rw [dif_pos hs, dif_pos hs]
  exact Finset.sum_le_sum fun a ha => h a ((Set.Finite.mem_toFinset hs).mp ha)

/-- HOL `SUM_SUBSET_SIMPLE` in `setSum` form (the summand is nonnegative on `t`). -/
private theorem p16_setSum_le_of_subset {α : Type*} {s t : Set α} (hs : s.Finite)
    (ht : t.Finite) (hsub : s ⊆ t) (f : α → ℝ)
    (hnn : ∀ a ∈ t, 0 ≤ f a) : setSum s f ≤ setSum t f := by
  unfold setSum
  rw [dif_pos hs, dif_pos ht]
  have hss : hs.toFinset ⊆ ht.toFinset := fun a ha =>
    (Set.Finite.mem_toFinset ht).mpr (hsub ((Set.Finite.mem_toFinset hs).mp ha))
  have hsplit : ∑ x ∈ ht.toFinset \ hs.toFinset, f x + ∑ x ∈ hs.toFinset, f x
      = ∑ x ∈ ht.toFinset, f x := Finset.sum_sdiff hss
  have hdiffnn : 0 ≤ ∑ x ∈ ht.toFinset \ hs.toFinset, f x :=
    Finset.sum_nonneg fun x hx => hnn x
      ((Set.Finite.mem_toFinset ht).mp (Finset.mem_sdiff.mp hx).1)
  linarith [hsplit, hdiffnn]

/-- `sol` is nonnegative (unconditional; both branches of the definition). -/
private theorem p16_sol_nonneg (x : V3) (C : Set V3) : 0 ≤ sol x C := by
  unfold sol
  split
  · rename_i h
    have h1 : 0 ≤ volume.real (C ∩ Metric.ball x (Classical.choose h)) :=
      measureReal_nonneg
    exact div_nonneg (mul_nonneg (by norm_num) h1)
      (pow_nonneg (le_of_lt (Classical.choose_spec h).1) 3)
  · exact le_refl 0

/-- HOL `SUM_CONST` in `setSum` form, folded into the `Nat.card` shape
(PA19 precedent `p19_setSum_const`). -/
private theorem p16_setSum_const {α : Type*} {s : Set α} (hs : s.Finite) (c : ℝ) :
    setSum s (fun _ => c) = (Nat.card s : ℝ) * c := by
  unfold setSum
  rw [dif_pos hs, Finset.sum_const, nsmul_eq_mul]
  simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card s hs]

/-- HOL `SUM_SUM_RESTRICT` in `setSum` form (Fubini over finite sets). -/
private theorem p16_setSum_fubini {α β : Type*} {B : Set α} {A : Set β}
    (hB : B.Finite) (hA : A.Finite) (f : α → β → ℝ) :
    setSum B (fun X => setSum A (fun u => f X u))
      = setSum A (fun u => setSum B (fun X => f X u)) := by
  simp only [setSum, dif_pos hB, dif_pos hA]
  exact Finset.sum_comm

/-- Restriction of a `setSum` to a predicate-filtered sub-sum. -/
private theorem p16_setSum_filter {α : Type*} {A : Set α} (hA : A.Finite)
    (P : α → Prop) [DecidablePred P] (f : α → ℝ) :
    setSum {u | u ∈ A ∧ P u} f = setSum A (fun u => if P u then f u else 0) := by
  have hfin : ({u | u ∈ A ∧ P u} : Set α).Finite := hA.subset fun u hu => hu.1
  unfold setSum
  rw [dif_pos hfin, dif_pos hA]
  have heq : hfin.toFinset = hA.toFinset.filter P := by
    ext u
    simp [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter,
      Set.Finite.mem_toFinset]
  rw [heq, Finset.sum_filter]

/-- `Nat.card` of a finite set splits over a subset difference. -/
private theorem p16_nat_card_sdiff {s t : Set V3} (hs : s.Finite) (hsub : t ⊆ s) :
    Nat.card ↑s - Nat.card ↑t = Nat.card ↑(s \ t) := by
  classical
  have ht : t.Finite := Set.Finite.subset hs hsub
  have hsd : (s \ t).Finite := hs.sdiff
  have hsubF : ht.toFinset ⊆ hs.toFinset := fun a ha =>
    (Set.Finite.mem_toFinset hs).mpr (hsub ((Set.Finite.mem_toFinset ht).mp ha))
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_eq_toFinset_card s hs, Set.ncard_eq_toFinset_card t ht,
    Set.ncard_eq_toFinset_card (s \ t) hsd, Set.Finite.toFinset_sdiff hs ht hsd,
    Finset.card_sdiff, Finset.inter_comm, Finset.inter_eq_right.mpr hsubF]

/-- `VX` is always a finite set (empty or a list point set). -/
private theorem p16_vx_finite (V : Set V3) (X : Set V3) : (VX V X).Finite := by
  classical
  unfold VX
  split
  · exact Set.finite_empty
  · simp only []
    split
    · exact Set.finite_empty
    · refine Set.Finite.ofFinset
        (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2).toFinset
        (fun x => ?_)
      simp [setOfList]

/-- Flyspeck constant `sol0 ≥ 0` (`sol0 = 3 arccos(1/3) - π ≥ 0` since
`arccos(1/3) ≥ arccos(1/2) = π/3`). -/
private theorem p16_sol0_nonneg : 0 ≤ sol0 := by
  have h1 : (1 / 3 : ℝ) ≤ 1 / 2 := by norm_num
  have h2 : Real.arccos (1 / 2) ≤ Real.arccos (1 / 3) := Real.arccos_le_arccos h1
  have h3 : Real.arccos (1 / 2) = Real.pi / 3 :=
    Real.arccos_eq_of_eq_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
      Real.cos_pi_div_three.symm
  unfold sol0
  linarith

/-- Flyspeck constant `sol0 < π / 5` (equivalently `arccos(1/3) < 2π/5`, via
`cos(2π/5) = (√5 - 1)/4 < 1/3`). -/
private theorem p16_sol0_lt_pi_div_five : sol0 < Real.pi / 5 := by
  have hcos5 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := Real.cos_pi_div_five
  have hcos2 : Real.cos (2 * Real.pi / 5) = 2 * Real.cos (Real.pi / 5) ^ 2 - 1 := by
    have hshape : (2 : ℝ) * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
    rw [hshape]; exact Real.cos_two_mul _
  have hsqrt5 : (Real.sqrt 5 : ℝ) < 7 / 3 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hsq : ((1 + Real.sqrt 5) / 4) ^ 2 = (3 + Real.sqrt 5) / 8 := by
    have hs25 : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
      have h25 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      nlinarith [h25]
    rw [div_pow, hs25]
    ring
  have hval : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    rw [hcos2, hcos5, hsq]
    ring
  have hlt : Real.cos (2 * Real.pi / 5) < 1 / 3 := by
    rw [hval]; linarith [hsqrt5]
  have hkey : Real.arccos (1 / 3) < 2 * Real.pi / 5 := by
    calc Real.arccos (1 / 3)
        < Real.arccos (Real.cos (2 * Real.pi / 5)) :=
          Real.arccos_lt_arccos (Real.neg_one_le_cos _) hlt (by norm_num)
      _ = 2 * Real.pi / 5 :=
          Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  unfold sol0
  linarith

/-- Flyspeck constant `0 < tau0` (`tau0 = 4π - 20 sol0 > 0`). -/
private theorem p16_tau0_pos : 0 < tau0 := by
  have h := p16_sol0_lt_pi_div_five
  unfold tau0
  linarith [h, Real.pi_pos]

/-- Flyspeck constant `0 ≤ mm1` (the only sign fact KIZHLTL2 consumes). -/
private theorem p16_mm1_nonneg : 0 ≤ mm1 := by
  unfold mm1
  exact div_nonneg (mul_nonneg p16_sol0_nonneg (Real.sqrt_nonneg 8))
    (le_of_lt p16_tau0_pos)

/-- HOL KIZHLTL.hl:401-449 (KIZHLTL2's Step 8): a Marchal cell contributing a
vertex `u ∈ V ∩ ball 0 (r - 8)` lies entirely inside `ball 0 r` (`MCELL_SUBSET_BALL_4`
+ `HDTFNFZ` + triangle arithmetic; the `u ∈ VX V X` hypothesis kills the null-cell
case, which alone funds the `VX` unfolding). -/
private theorem p16_step8 (V : Set V3) (r : ℝ) (hs : saturated V) (hp : Packing V)
    (u : V3) (hu : u ∈ V ∩ Metric.ball 0 (r - 8)) (X : Set V3)
    (hX : mcellSet V X ∧ u ∈ VX V X) : X ⊆ Metric.ball 0 r := by
  obtain ⟨i, ul, hXul, hb⟩ := Set.mem_setOf.mp hX.1
  have hnull : ¬nullSet X := by
    intro hc
    have hvx0 : VX V X = ∅ := by
      unfold VX
      split
      · rfl
      · rename_i hcon
        exact absurd hc hcon
    have hX' : mcellSet V X ∧ u ∈ VX V X := hX
    rw [hvx0] at hX'
    exact absurd hX'.2 (Set.notMem_empty u)
  have hvxeq : VX V X = V ∩ X := @HDTFNFZ V ul i u X hs hp hb hXul hnull
  have huX : u ∈ X := by
    have hX' : mcellSet V X ∧ u ∈ VX V X := hX
    rw [hvxeq] at hX'
    have hx'' : u ∈ V ∧ u ∈ X := hX'.2
    exact hx''.2
  obtain ⟨p, hp4⟩ := MCELL_SUBSET_BALL_4 V X hp hs hX.1
  intro z hz
  have t1 : dist 0 z ≤ dist 0 u + dist u z := dist_triangle 0 u z
  have t2 : dist u z ≤ dist u p + dist p z := dist_triangle u p z
  have d1 : dist u p < 4 := Metric.mem_ball.1 (hp4 huX)
  have d2 : dist z p < 4 := Metric.mem_ball.1 (hp4 hz)
  have hd0u : dist u 0 < r - 8 := Metric.mem_ball.1 hu.2
  have hu0 : dist u 0 = dist 0 u := dist_comm u 0
  have hz0 : dist z 0 = dist 0 z := dist_comm z 0
  have hpz : dist p z = dist z p := dist_comm p z
  refine Metric.mem_ball.2 ?_
  linarith

/-- GIANT — HOL `KIZHLTL2` (KIZHLTL.hl:285-527, concl `pack_concl.hl:205-208`):
`CARD(V ∩ ball 0 r) * 8 * mm1 + c * r^2 <= (2 mm1 / π) * Σ total_solid V`
over the cells in `ball 0 r`. Core: total solid angles over the annulus
`A2 = V ∩ ball 0 (r - 8)` bound `4π * CARD A2` by QZYZMJC (SUM_SUM_RESTRICT
re-indexing); `CARD A1 - CARD A2 = CARD (A1 DIFF A2) <= C * r^2` (NEEDS
PACKING_BALL_BOUNDARY/marchal3, NEEDS FINITE_PACK_LEMMA, CARD_DIFF,
CARD_SUBSET); each vertex contributes `sol <= 1` scaled by the radial volume
(NEEDS URRPHBZ2/PackingAuto13, `sol_spec`); `#1.012080 < mm1`
(Flyspeck_constants.bounds) absorbs the annulus term.

DISCHARGES: PackingAuto2.KIZHLTL2_concl (PackingAuto2.lean:816). -/
theorem KIZHLTL2 : ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V →
    1 ≤ r →
    ((Nat.card ((V ∩ Metric.ball 0 r : Set V3)) : ℕ) : ℝ) * 8 * mm1 + c * r ^ 2 ≤
      (2 * mm1 / Real.pi) *
        setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} (totalSolid V) := by
  intro V
  by_cases hmain : saturated V ∧ Packing V
  · obtain ⟨hs, hp⟩ := hmain
    obtain ⟨C, hCB⟩ := PACKING_BALL_BOUNDARY V 0 0 8 hp
    refine ⟨(2 * mm1 / Real.pi) * (4 * Real.pi) * (-C), fun r _ _ hr => ?_⟩
    classical
    set B : Set (Set V3) := {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} with hBdef
    have hBfin : B.Finite := FINITE_MCELL_SET_LEMMA V r hp hs
    have hA1fin : (V ∩ Metric.ball 0 r).Finite := hp.finite_inter_ball r
    have hA2fin : (V ∩ Metric.ball 0 (r - 8)).Finite := hp.finite_inter_ball (r - 8)
    -- the annulus card bound (HL:290-302, PACKING_BALL_BOUNDARY)
    have hA2sub : (V ∩ Metric.ball 0 (r - 8)) ⊆ (V ∩ Metric.ball 0 r) := by
      intro u hu
      have h1 : dist u 0 < r - 8 := Metric.mem_ball.1 hu.2
      exact ⟨hu.1, Metric.mem_ball.2 (by linarith)⟩
    have hPB := hCB r hr
    have hadd0 : (V ∩ Metric.ball 0 (r + 0) : Set V3) = V ∩ Metric.ball 0 r := by
      rw [add_zero]
    rw [hadd0] at hPB
    have hcard : ((Nat.card ↑(V ∩ Metric.ball 0 r) - Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ)
        ≤ C * r ^ 2 := by
      have hdiff : Nat.card ↑(V ∩ Metric.ball 0 r) - Nat.card ↑(V ∩ Metric.ball 0 (r - 8))
          = Nat.card ↑((V ∩ Metric.ball 0 r) \ (V ∩ Metric.ball 0 (r - 8))) :=
        p16_nat_card_sdiff hA1fin hA2sub
      rw [hdiff]; exact hPB
    -- per-vertex QZYZMJC (HL:454-458)
    have hQZ : ∀ u ∈ (V ∩ Metric.ball 0 (r - 8)),
        setSum {X : Set V3 | mcellSet V X ∧ u ∈ VX V X} (fun X => sol u X) = 4 * Real.pi :=
      fun u hu => QZYZMJC V u hs hp hu.1
    -- the setSum re-indexing chain (HL:320-461)
    have e8set : ∀ u ∈ (V ∩ Metric.ball 0 (r - 8)),
        {X : Set V3 | X ∈ B ∧ u ∈ VX V X} = {X : Set V3 | mcellSet V X ∧ u ∈ VX V X} := by
      intro u hu
      apply Set.eq_of_subset_of_subset
      · intro X hX
        have hX' : X ∈ B ∧ u ∈ VX V X := hX
        have hx'' : mcellSet V X ∧ u ∈ VX V X := ⟨hX'.1.2, hX'.2⟩
        exact hx''
      · intro X hX
        have hX' : mcellSet V X ∧ u ∈ VX V X := hX
        have hstep : X ⊆ Metric.ball 0 r := p16_step8 V r hs hp u hu X hX'
        have hx'' : X ∈ B ∧ u ∈ VX V X := ⟨⟨hstep, hX'.1⟩, hX'.2⟩
        exact hx''
    have e8 : setSum (V ∩ Metric.ball 0 (r - 8))
        (fun u => setSum {X : Set V3 | X ∈ B ∧ u ∈ VX V X} (fun X => sol u X))
        = setSum (V ∩ Metric.ball 0 (r - 8))
            (fun u => setSum {X : Set V3 | mcellSet V X ∧ u ∈ VX V X}
              (fun X => sol u X)) := by
      refine p16_setSumCongr fun u hu => ?_
      rw [e8set u hu]
    have e7a : setSum (V ∩ Metric.ball 0 (r - 8))
        (fun u => setSum {X : Set V3 | X ∈ B ∧ u ∈ VX V X} (fun X => sol u X))
        = setSum (V ∩ Metric.ball 0 (r - 8))
            (fun u => setSum B (fun X => if u ∈ VX V X then sol u X else 0)) :=
      p16_setSumCongr fun u _ =>
        p16_setSum_filter hBfin (fun X => u ∈ VX V X) (fun X => sol u X)
    have e7b : setSum (V ∩ Metric.ball 0 (r - 8))
        (fun u => setSum B (fun X => if u ∈ VX V X then sol u X else 0))
        = setSum B (fun X => setSum (V ∩ Metric.ball 0 (r - 8))
            (fun u => if u ∈ VX V X then sol u X else 0)) :=
      (p16_setSum_fubini hBfin hA2fin
        (fun X u => if u ∈ VX V X then sol u X else 0)).symm
    have e7c : setSum B (fun X => setSum (V ∩ Metric.ball 0 (r - 8))
        (fun u => if u ∈ VX V X then sol u X else 0))
        = setSum B (fun X => setSum {u : V3 | u ∈ V ∩ Metric.ball 0 (r - 8) ∧ u ∈ VX V X}
            (fun u => sol u X)) :=
      p16_setSumCongr fun X _ =>
        (p16_setSum_filter hA2fin (fun u => u ∈ VX V X) (fun u => sol u X)).symm
    have e6 : setSum B (fun X => setSum {u : V3 | u ∈ V ∩ Metric.ball 0 (r - 8) ∧ u ∈ VX V X}
        (fun u => sol u X))
        ≤ setSum B (fun X => setSum (VX V X) (fun u => sol u X)) := by
      refine p16_setSum_mono hBfin _ _ fun X _ => ?_
      have hfin : ({u : V3 | u ∈ V ∩ Metric.ball 0 (r - 8) ∧ u ∈ VX V X}).Finite :=
        Set.Finite.subset hA2fin fun u hu => hu.1
      exact p16_setSum_le_of_subset hfin (p16_vx_finite V X) (fun u hu => hu.2)
        (fun u => sol u X) (fun u hu => p16_sol_nonneg u X)
    have hchain : ((Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ) * (4 * Real.pi)
        ≤ setSum B (fun X => setSum (VX V X) (fun u => sol u X)) := by
      have hstep : setSum (V ∩ Metric.ball 0 (r - 8)) (fun _ => (4 * Real.pi : ℝ))
          ≤ setSum B (fun X => setSum (VX V X) (fun u => sol u X)) := by
        calc setSum (V ∩ Metric.ball 0 (r - 8)) (fun _ => (4 * Real.pi : ℝ))
            = setSum (V ∩ Metric.ball 0 (r - 8))
                (fun u => setSum {X : Set V3 | mcellSet V X ∧ u ∈ VX V X}
                  (fun X => sol u X)) := by
              refine p16_setSumCongr fun u hu => ?_
              rw [hQZ u hu]
          _ = setSum (V ∩ Metric.ball 0 (r - 8))
                (fun u => setSum {X : Set V3 | X ∈ B ∧ u ∈ VX V X}
                  (fun X => sol u X)) := e8.symm
          _ = setSum B (fun X => setSum {u : V3 | u ∈ V ∩ Metric.ball 0 (r - 8) ∧ u ∈ VX V X}
                  (fun u => sol u X)) := e7a.trans (e7b.trans e7c)
          _ ≤ setSum B (fun X => setSum (VX V X) (fun u => sol u X)) := e6
      rw [p16_setSum_const hA2fin (4 * Real.pi)] at hstep
      exact hstep
    -- final arithmetic (HL:463-527): only the sign of mm1 enters
    have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hmm1 : 0 ≤ mm1 := p16_mm1_nonneg
    have hscale0 : 0 ≤ 2 * mm1 / Real.pi := by
      refine div_nonneg (by linarith) Real.pi_pos.le
    have hkeyeq : (2 * mm1 / Real.pi) * (4 * Real.pi) = 8 * mm1 := by
      field_simp
      ring
    have hscaled : ((Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ) * 8 * mm1
        ≤ (2 * mm1 / Real.pi) * setSum B (fun X => setSum (VX V X) (fun u => sol u X)) := by
      have h1 := mul_le_mul_of_nonneg_left hchain hscale0
      have h2 : (2 * mm1 / Real.pi)
          * (((Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ) * (4 * Real.pi))
          = ((Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ) * 8 * mm1 := by
        field_simp
        ring
      rw [h2] at h1
      exact h1
    have hN2N1 : (Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ)
        ≤ Nat.card ↑(V ∩ Metric.ball 0 r) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hA2sub hA1fin
    have hN : ((Nat.card ↑(V ∩ Metric.ball 0 r) - Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ)
        = ((Nat.card ↑(V ∩ Metric.ball 0 r) : ℕ) : ℝ)
          - ((Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ) :=
      Nat.cast_sub hN2N1
    have h8mm1 : 0 ≤ 8 * mm1 := by linarith
    have hfinal : ((Nat.card ↑(V ∩ Metric.ball 0 r) : ℕ) : ℝ) * (8 * mm1)
        ≤ ((Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ) * (8 * mm1)
          + (C * r ^ 2) * (8 * mm1) := by
      have h1 : ((Nat.card ↑(V ∩ Metric.ball 0 r) : ℕ) : ℝ)
          ≤ ((Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ) + C * r ^ 2 := by
        have h1' := hcard
        rw [hN] at h1'
        linarith
      nlinarith [mul_le_mul_of_nonneg_right h1 h8mm1]
    calc ((Nat.card ((V ∩ Metric.ball 0 r : Set V3)) : ℕ) : ℝ) * 8 * mm1
        + ((2 * mm1 / Real.pi) * (4 * Real.pi) * (-C)) * r ^ 2
        ≤ ((Nat.card ↑(V ∩ Metric.ball 0 (r - 8)) : ℕ) : ℝ) * 8 * mm1 := by
          have hcr : ((2 * mm1 / Real.pi) * (4 * Real.pi) * (-C)) * r ^ 2
              = -(C * r ^ 2) * (8 * mm1) := by
            rw [hkeyeq]; ring
          linarith [hfinal, hcr]
      _ ≤ (2 * mm1 / Real.pi) *
          setSum {X : Set V3 | X ≤ Metric.ball 0 r ∧ mcellSet V X} (totalSolid V) := by
          exact hscaled
  · exact ⟨0, fun r hs' hp' _ => absurd ⟨hs', hp'⟩ hmain⟩

/-- GIANT — HOL `KIZHLTL3_concl` (pack_concl.hl:210-220): the general-`f`
edge-dihedral bound with `dist < sqrt 8`. NOTE: no HL proof exists anywhere in
the local tree — `KIZHLTL.hl` proves only the `lmfun`/`2 * h0` specialization
`KIZHLTL4` (below), and `UPFZBZM_support_lemmas.hl:71` merely restates a
`KIZHLTL3_new_concl`; stated faithfully here (mirroring the PackingAuto2
interface encoding of the `\{u,v}` pattern lambda) and sorried.

DISCHARGES: PackingAuto2.KIZHLTL3_concl (PackingAuto2.lean:824). -/
theorem KIZHLTL3 : ∀ (V : Set V3) (f : ℝ → ℝ), ∃ c : ℝ, ∀ r : ℝ,
    saturated V → Packing V → 1 ≤ r →
    (∃ c1 : ℝ, ∀ x : ℝ, 2 ≤ x ∧ x < Real.sqrt 8 → |f x| ≤ c1) →
    ((8 * mm2 / Real.pi) *
          setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
            (fun X => setSum (edgeX V X) fun e =>
              let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
              dihX V X (q.1, q.2) * f (hl [q.1, q.2]))
        + c * r ^ 2 ≤
      8 * mm2 * setSum (V ∩ Metric.ball 0 r)
        (fun u => setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v < Real.sqrt 8}
          (fun v => f (hl [u, v])))) := by
  sorry

/-! ### KIZHLTL4 support kit -/

/-! == NEW KIT for KIZHLTL4 == -/

/-- Flyspeck constant `0 ≤ mm2` (PA19's `ZERO_LE_MM2_LEMMA` lives downstream —
PA19 imports this file, so the sign fact is re-derived here by exact algebra:
`sol0 ≥ π/6` ⟺ `arccos(1/3) ≥ 7π/18` ⟺ `cos(7π/18) = sin(π/9) ≥ 1/3`, the
last via the triple-angle identity `sin π/3 = 3 sin(π/9) - 4 sin(π/9)³` and the
factorization `g(1/3) - g(s) = (1/3 - s)(3 - 4(s² + s/3 + 1/9))` for
`g = 3s - 4s³`.) -/
private theorem p16_mm2_nonneg : 0 ≤ mm2 := by
  have hpos : (0:ℝ) < Real.pi / 9 := by linarith [Real.pi_pos]
  have hlt : Real.pi / 9 < Real.pi := by linarith [Real.pi_pos]
  have hs0 : 0 ≤ Real.sin (Real.pi / 9) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
  have htri : Real.sin (Real.pi / 3)
      = 3 * Real.sin (Real.pi / 9) - 4 * Real.sin (Real.pi / 9) ^ 3 := by
    have hshape : Real.pi / 3 = 3 * (Real.pi / 9) := by ring
    rw [hshape, Real.sin_three_mul]
  have hval : Real.sqrt 3 / 2
      = 3 * Real.sin (Real.pi / 9) - 4 * Real.sin (Real.pi / 9) ^ 3 := by
    rw [← Real.sin_pi_div_three]; exact htri
  have hsq3 : (23:ℝ) / 27 < Real.sqrt 3 / 2 := by
    have h46sq : ((46:ℝ) / 27) ^ 2 < 3 := by norm_num
    have h46 := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ ((46:ℝ) / 27) ^ 2) h46sq
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (46:ℝ) / 27)] at h46
    linarith
  have hge : (1:ℝ) / 3 ≤ Real.sin (Real.pi / 9) := by
    by_contra hcon
    have hf1 : (0:ℝ) < 1 / 3 - Real.sin (Real.pi / 9) := by linarith
    have hsq : Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9) < 1 / 9 := by
      have h1 : Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
          ≤ Real.sin (Real.pi / 9) * (1 / 3) :=
        mul_le_mul_of_nonneg_left (le_of_not_ge hcon) hs0
      have h2 : Real.sin (Real.pi / 9) * (1 / 3) < (1 / 3) * (1 / 3) :=
        mul_lt_mul_of_pos_right (lt_of_not_ge hcon) (by norm_num)
      linarith
    have hfac : 23 / 27 - (3 * Real.sin (Real.pi / 9)
          - 4 * Real.sin (Real.pi / 9) ^ 3)
        = (1 / 3 - Real.sin (Real.pi / 9)) *
            (3 - 4 * (Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
              + Real.sin (Real.pi / 9) / 3 + 1 / 9)) := by ring
    have hprod : (0:ℝ) < (1 / 3 - Real.sin (Real.pi / 9)) *
        (3 - 4 * (Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
          + Real.sin (Real.pi / 9) / 3 + 1 / 9)) := by
      have h1 : (0:ℝ) < 1 / 3 - Real.sin (Real.pi / 9) := by linarith
      have hT : Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
          + Real.sin (Real.pi / 9) / 3 + 1 / 9 < 1 / 3 := by linarith
      have h2 : (0:ℝ) < 3 - 4 * (Real.sin (Real.pi / 9) * Real.sin (Real.pi / 9)
          + Real.sin (Real.pi / 9) / 3 + 1 / 9) := by linarith [hT]
      exact mul_pos h1 h2
    have hlt23 : 3 * Real.sin (Real.pi / 9) - 4 * Real.sin (Real.pi / 9) ^ 3
        < 23 / 27 := by linarith
    linarith [hsq3, hval, hlt23]
  have hshape : 7 * Real.pi / 18 = Real.pi / 2 - Real.pi / 9 := by ring
  have hcos : (1:ℝ) / 3 ≤ Real.cos (7 * Real.pi / 18) := by
    rw [hshape, Real.cos_pi_div_two_sub]
    exact hge
  have hkey : 7 * Real.pi / 18 ≤ Real.arccos (1 / 3) := by
    have h1 := Real.arccos_le_arccos hcos
    rw [Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at h1
    exact h1
  have hkey' : (7:ℝ) * Real.pi / 6 ≤ 3 * Real.arccos (1 / 3) := by
    have h1 : (7:ℝ) * Real.pi / 18 * 3 ≤ Real.arccos (1 / 3) * 3 :=
      mul_le_mul_of_nonneg_right hkey (le_of_lt (by norm_num : (0:ℝ) < 3))
    linarith
  have hsol0 : Real.pi / 6 ≤ sol0 := by
    unfold sol0
    linarith
  have htau : (0:ℝ) < 6 * tau0 := by linarith [p16_tau0_pos]
  unfold mm2
  refine div_nonneg (mul_nonneg ?_ (Real.sqrt_nonneg 2)) (le_of_lt htau)
  linarith

/-- The epsilon-fixed pair representation of an edge (PA19
`p19_epsilon_pair` template). -/
private theorem p16_epsilon_pair {e : Set V3} (h : ∃ p : V3 × V3, e = {p.1, p.2}) :
    {(Classical.epsilon fun w : V3 × V3 => e = {w.1, w.2}).1,
      (Classical.epsilon fun w : V3 × V3 => e = {w.1, w.2}).2} = e :=
  Eq.symm (Classical.epsilon_spec_aux (by infer_instance)
    (fun w : V3 × V3 => e = {w.1, w.2}) h)

/-- The KIZHLTL4 inner summand function: the HL `\{u,v}. if {u,v} IN edgeX V X
then dihX V X (u,v) * lmfun (hl [u;v]) else &0` pattern lambda (epsilon
encoding, guard on the edge set). -/
private noncomputable def p16_gammaE (V X : Set V3) (f : ℝ → ℝ) (e : Set V3) : ℝ :=
  if e ∈ edgeX V X then
    dihX V X ((Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}).1,
      (Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}).2) *
      f (hl [(Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}).1,
        (Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}).2])
  else 0

/-- `p16_gammaE` is nonnegative on Marchal cells for a pointwise-nonnegative
weight (`DIHX_RANGE` + `hf`; replaces the HOL `gamma_y_pos_le`, whose PA15
`gammaY` uses the private `pairOf`). -/
private theorem p16_gammaE_nonneg (V X : Set V3) (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (e : Set V3) (hm : mcellSet V X) (he : e ∈ edgeX V X) : 0 ≤ p16_gammaE V X f e := by
  unfold p16_gammaE
  rw [if_pos he]
  exact mul_nonneg (DIHX_RANGE V X _ _).1 (hf _)

/-- A `setSum` over a finite support with vanishing summands is zero. -/
private theorem p16_setSum_eq_zero {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ)
    (h : ∀ a ∈ s, f a = 0) : setSum s f = 0 := by
  unfold setSum
  rw [dif_pos hs, Finset.sum_eq_zero fun a ha => h a ((Set.Finite.mem_toFinset hs).mp ha)]

/-- Sum transfer across an equality of summation domains. -/
private theorem p16_setSum_domain {α : Type*} {s t : Set α} (heq : s = t) (f : α → ℝ) :
    setSum s f = setSum t f := by
  rw [heq]

/-- HOL `SUM_SUPERSET` (equality form) in `setSum` form. -/
private theorem p16_setSum_superset_eq {α : Type*} {s t : Set α} (hs : s.Finite)
    (ht : t.Finite) (hsub : s ⊆ t) (f : α → ℝ)
    (hz : ∀ a ∈ t, a ∉ s → f a = 0) : setSum s f = setSum t f := by
  have hsd : ht.toFinset \ hs.toFinset ⊆ ht.toFinset := fun a ha =>
    (Finset.mem_sdiff.mp ha).1
  have hsplit : ∑ x ∈ ht.toFinset \ hs.toFinset, f x + ∑ x ∈ hs.toFinset, f x
      = ∑ x ∈ ht.toFinset, f x := Finset.sum_sdiff
      (fun a ha => (Set.Finite.mem_toFinset ht).mpr
        (hsub ((Set.Finite.mem_toFinset hs).mp ha)))
  have hzero : ∑ x ∈ ht.toFinset \ hs.toFinset, f x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have h1 : x ∈ t := (Set.Finite.mem_toFinset ht).mp (Finset.mem_sdiff.mp hx).1
    have h2 : x ∉ s := by
      intro hcon
      exact absurd ((Set.Finite.mem_toFinset hs).mpr hcon) (Finset.mem_sdiff.mp hx).2
    exact hz x h1 h2
  unfold setSum
  rw [dif_pos hs, dif_pos ht]
  linarith [hsplit, hzero]

/-- HOL `SUM_LMUL` in `setSum` form. -/
private theorem p16_setSum_lmull {α : Type*} {s : Set α} (hs : s.Finite) (c : ℝ)
    (f : α → ℝ) : setSum s (fun x => c * f x) = c * setSum s f := by
  unfold setSum
  rw [dif_pos hs, dif_pos hs, Finset.mul_sum]

/-- HOL `SUM_SUM_PRODUCT` (ordered-pair reindexing) for a rectangular product. -/
private theorem p16_setSum_prod {A U : Set V3} (hA : A.Finite) (hU : U.Finite)
    (F : V3 × V3 → ℝ) :
    setSum (A ×ˢ U) F = setSum A (fun u => setSum U (fun v => F (u, v))) := by
  unfold setSum
  rw [dif_pos (hA.prod hU), dif_pos hA]
  simp only [dif_pos hU]
  rw [← Set.Finite.toFinset_prod hA hU]
  exact Finset.sum_product _ _ _

/-- A pointwise-nonnegative summand gives a nonnegative `setSum` (junk `0`
included). -/
private theorem p16_setSum_nonneg {α : Type*} {s : Set α} (f : α → ℝ)
    (h : ∀ a ∈ s, 0 ≤ f a) : 0 ≤ setSum s f := by
  unfold setSum
  split
  · rename_i hs
    exact Finset.sum_nonneg fun a ha => h a ((Set.Finite.mem_toFinset hs).mp ha)
  · exact le_refl 0

/-- `radV {u, v} = hl [u, v]` (the pair circumradius is the half-distance). -/
private theorem p16_radV_pair (u v : V3) : radV {u, v} = hl [u, v] := by
  unfold hl
  congr 1
  ext x
  simp [setOfList]

/-- DISCHARGED — HOL `KIZHLTL4` (KIZHLTL.hl:533-546 concl, 548-1032 proof): the
`lmfun` specialization of the edge bound, `dist <= 2 * h0` (with `c = 0` in
the HL proof's annulus budget `8 * mm2 * (0)`). The inner edge sum keeps the
HL `\{u,v}. if {u,v} IN edgeX V X then ... else &0` guard verbatim (encoded
by the gammaX epsilon convention; the guard-form summand is `p16_gammaE`).
Proof chain (port of the HL steps): cell-edge double sum reindexes over
`T1` = pairs of `V ∩ ball 0 r` (filter + Fubini), restricts to `T2` (edges
with `hl ≤ h0`; off-`T2` summands vanish because `lmfun` cuts off at `h0`),
each `T2` edge contributes `2π · lmfun (radV e)` by `GRUTOTI1_concl` (the
PackingAuto2 interface shim, discharged by PackingAuto23's `GRUTOTI`), and the
final unordered→ordered-pair comparison runs PA15 `SUM_PAIR_2_SET` + a
product-set reindexing (`p16_setSum_prod`) + `radV {u,v} = hl [u,v]`
(`HL_2`). Consumed upstream pieces: PA15 `FINITE_MCELL_SET_LEMMA`,
`FINITE_EDGE_X2` / `DIHX_SYM` / `SUM_PAIR_2_SET` (the three ★ stars — consumed
directly since PackingAuto15 is imported; the parallel lane's proofs land
in-place, no `_p16` copies needed), PA10 `HDTFNFZ`, PA2 `GRUTOTI1_concl`.
`0 ≤ mm2` is re-derived locally (`p16_mm2_nonneg`, exact triple-angle
algebra) because PA19's `ZERO_LE_MM2_LEMMA` lives downstream (PA19 imports
this file). NOT needed (contrary to the earlier header estimate):
`MCELL_SUBSET_BALL_4` / `PACKING_BALL_BOUNDARY` / `QZYZMJC`.

DISCHARGES: none (`KIZHLTL4` is local to KIZHLTL.hl with no `pack_concl`
interface; it feeds UPFZBZM (UPFZBZM.hl:122) downstream). -/

theorem KIZHLTL4 : ∀ V : Set V3, ∃ c : ℝ, ∀ r : ℝ, saturated V → Packing V →
    1 ≤ r →
    (8 * mm2 / Real.pi) *
        setSum {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
          (fun X => setSum (edgeX V X) fun e =>
            let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
            if {q.1, q.2} ∈ edgeX V X then
              dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
            else 0)
      + c * r ^ 2 ≤
      8 * mm2 * setSum (V ∩ Metric.ball 0 r)
        (fun u => setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
          (fun v => lmfun (hl [u, v]))) := by
  intro V
  by_cases hmain : saturated V ∧ Packing V
  · obtain ⟨hs, hp⟩ := hmain
    refine ⟨0, fun r _ _ _hr => ?_⟩
    classical
    set S1 : Set (Set V3) := {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}
      with hS1def
    set V1 : Set V3 := V ∩ Metric.ball 0 r with hV1def
    set T1 : Set (Set V3) := {e : Set V3 | ∃ u ∈ V1, ∃ v ∈ V1, e = {u, v}}
      with hT1def
    set T2 : Set (Set V3) :=
      {e : Set V3 | ∃ m ∈ V1, ∃ n ∈ V1, m ≠ n ∧ dist m n ≤ 2 * h0 ∧ e = {m, n}}
      with hT2def
    have hS1fin : S1.Finite := FINITE_MCELL_SET_LEMMA V r hp hs
    have hV1fin : V1.Finite := hp.finite_inter_ball r
    have hT1fin : T1.Finite := FINITE_SET_PRODUCT_KY_LEMMA V1 hV1fin
    have hT2sub : T2 ⊆ T1 := by
      intro e he
      obtain ⟨m, hm, n, hn, _hne, _hd, hme⟩ := he
      exact ⟨m, hm, n, hn, hme⟩
    have hT2fin : T2.Finite := Set.Finite.subset hT1fin hT2sub
    have hVXsub : ∀ X : Set V3, mcellSet V X → (VX V X : Set V3) ⊆ V ∩ X := by
      intro X hm z hz
      obtain ⟨i, ul, hXm, hb⟩ := Set.mem_setOf.mp hm
      by_cases hnull : nullSet X
      · have h0 : (VX V X : Set V3) = ∅ := by
          unfold VX
          split
          · rfl
          · rename_i hcon
            exact absurd hnull hcon
        rw [h0] at hz
        exact absurd hz (Set.notMem_empty z)
      · have heq := @HDTFNFZ V ul i z X hs hp hb hXm hnull
        rw [heq] at hz
        exact hz
    have hEsubT1 : ∀ X : Set V3, X ∈ S1 → ∀ e ∈ edgeX V X, e ∈ T1 := by
      intro X hX e he
      obtain ⟨u, v, huv, hu, hv, _hne⟩ := he
      have huVX : u ∈ V ∩ X := hVXsub X hX.2 hu
      have hvVX : v ∈ V ∩ X := hVXsub X hX.2 hv
      rw [huv]
      exact ⟨u, ⟨huVX.1, hX.1 huVX.2⟩, v, ⟨hvVX.1, hX.1 hvVX.2⟩, rfl⟩
    have hinner : ∀ X ∈ S1,
        setSum (edgeX V X) (fun e =>
            let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
            if {q.1, q.2} ∈ edgeX V X then
              dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
            else 0)
        = setSum {e : Set V3 | e ∈ T1 ∧ e ∈ edgeX V X}
            (fun e => p16_gammaE V X lmfun e) := by
      intro X hX
      have hdom : (edgeX V X : Set (Set V3)) = {e : Set V3 | e ∈ T1 ∧ e ∈ edgeX V X} := by
        apply Set.eq_of_subset_of_subset
        · intro e he
          exact ⟨hEsubT1 X hX e he, he⟩
        · intro e he
          exact he.2
      have hcongr : setSum (edgeX V X) (fun e =>
            let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
            if {q.1, q.2} ∈ edgeX V X then
              dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
            else 0)
          = setSum (edgeX V X) (fun e => p16_gammaE V X lmfun e) := by
        refine p16_setSumCongr fun e he => ?_
        obtain ⟨u, v, huv, _hu, _hv, _hne⟩ := id he
        have hguard : {(Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}).1,
            (Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}).2} ∈ edgeX V X := by
          rw [p16_epsilon_pair (e := e) ⟨(u, v), huv⟩]
          exact he
        rw [if_pos hguard]
        unfold p16_gammaE
        exact (if_pos he).symm
      rw [hcongr]
      exact p16_setSum_domain hdom (fun e => p16_gammaE V X lmfun e)
    have hstep1 : setSum S1 (fun X => setSum (edgeX V X) (fun e =>
            let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
            if {q.1, q.2} ∈ edgeX V X then
              dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
            else 0))
        = setSum S1 (fun X => setSum {e : Set V3 | e ∈ T1 ∧ e ∈ edgeX V X}
            (fun e => p16_gammaE V X lmfun e)) :=
      p16_setSumCongr fun X hX => hinner X hX
    have hstep2 : setSum S1 (fun X => setSum {e : Set V3 | e ∈ T1 ∧ e ∈ edgeX V X}
          (fun e => p16_gammaE V X lmfun e))
        = setSum T1 (fun e => setSum {X : Set V3 | X ∈ S1 ∧ e ∈ edgeX V X}
            (fun X => p16_gammaE V X lmfun e)) := by
      rw [p16_setSumCongr (fun X _ =>
          p16_setSum_filter hT1fin (fun e => e ∈ edgeX V X)
            (fun e => p16_gammaE V X lmfun e))]
      try simp only []
      rw [p16_setSum_fubini hS1fin hT1fin (fun X e => if e ∈ edgeX V X then
          p16_gammaE V X lmfun e else 0)]
      try simp only []
      rw [p16_setSumCongr (fun e _ =>
          (p16_setSum_filter hS1fin (fun X => e ∈ edgeX V X)
            (fun X => p16_gammaE V X lmfun e)).symm)]
    have hstep3 : setSum T1 (fun e => setSum {X : Set V3 | X ∈ S1 ∧ e ∈ edgeX V X}
          (fun X => p16_gammaE V X lmfun e))
        = setSum T2 (fun e => setSum {X : Set V3 | X ∈ S1 ∧ e ∈ edgeX V X}
            (fun X => p16_gammaE V X lmfun e)) := by
      refine (p16_setSum_superset_eq hT2fin hT1fin hT2sub _ ?_).symm
      intro e he1 he2
      obtain ⟨u, hu, v, hv, huv⟩ := he1
      have hkey : u = v ∨ 2 * h0 < dist u v := by
        by_contra hcon
        exact he2 ⟨u, hu, v, hv, fun hc => hcon (Or.inl hc),
          le_of_not_gt (fun hc => hcon (Or.inr hc)), huv⟩
      have hfin : ({X : Set V3 | X ∈ S1 ∧ e ∈ edgeX V X}).Finite :=
        Set.Finite.subset hS1fin fun X hX => hX.1
      refine p16_setSum_eq_zero hfin _ fun X hX => ?_
      obtain ⟨_hXS, hed⟩ := hX
      by_cases hcuv : u = v
      · have hne : ¬(e ∈ edgeX V X) := by
          rintro ⟨p, q, hpq, _hp, _hq, hpqne⟩
          rw [huv, hcuv] at hpq
          rcases Set.pair_eq_pair_iff.mp hpq with ⟨r1, r2⟩ | ⟨r1, r2⟩
          · exact hpqne (by rw [← r1, ← r2])
          · exact hpqne (by rw [← r1, ← r2])
        unfold p16_gammaE
        rw [if_neg hne]
      · have hdist : 2 * h0 < dist u v := by
          rcases hkey with h | h
          · exact absurd h hcuv
          · exact h
        have hlE : hl [(Classical.epsilon fun w : V3 × V3 => e = {w.1, w.2}).1,
            (Classical.epsilon fun w : V3 × V3 => e = {w.1, w.2}).2] = dist u v / 2 := by
          rw [HL_2]
          have heps := p16_epsilon_pair (e := e) ⟨(u, v), huv⟩
          rcases Set.pair_eq_pair_iff.mp (heps.trans huv) with ⟨r1, r2⟩ | ⟨r1, r2⟩
          · rw [r1, r2]
          · rw [r1, r2, dist_comm]
        unfold p16_gammaE
        rw [if_pos hed, hlE,
          show lmfun (dist u v / 2) = 0 from by
            unfold lmfun
            split_ifs with hle
            · exact absurd hle (by linarith)
            · rfl]
        ring
    have hstep4 : setSum T2 (fun e => setSum {X : Set V3 | X ∈ S1 ∧ e ∈ edgeX V X}
          (fun X => p16_gammaE V X lmfun e))
        ≤ setSum T2 (fun e => setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X}
            (fun X => p16_gammaE V X lmfun e)) := by
      refine p16_setSum_mono hT2fin _ _ fun e he => ?_
      obtain ⟨m, hm, n, hn, hne, hdist, hme⟩ := he
      have hf1 : ({X : Set V3 | X ∈ S1 ∧ e ∈ edgeX V X}).Finite :=
        Set.Finite.subset hS1fin fun X hX => hX.1
      have hf2 : ({X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X}).Finite :=
        FINITE_EDGE_X2 V e m n hp hs hme
      exact p16_setSum_le_of_subset hf1 hf2 (fun X hX => ⟨hX.1.2, hX.2⟩)
        (fun X => p16_gammaE V X lmfun e)
        (fun X hX => p16_gammaE_nonneg V X lmfun lmfun_pos_le e hX.1 hX.2)
    have hstep5 : setSum T2 (fun e => setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X}
          (fun X => p16_gammaE V X lmfun e))
        = setSum T2 (fun e => 2 * Real.pi * lmfun (radV e)) := by
      refine p16_setSumCongr fun e he => ?_
      obtain ⟨m, hm, n, hn, hne, hdist, hme⟩ := he
      subst hme
      have hXfin : ({X : Set V3 | mcellSet V X ∧ {m, n} ∈ edgeX V X}).Finite :=
        FINITE_EDGE_X2 V {m, n} m n hp hs rfl
      have hperX : ∀ X ∈ {X : Set V3 | mcellSet V X ∧ {m, n} ∈ edgeX V X},
          p16_gammaE V X lmfun {m, n} = dihX V X (m, n) * lmfun (hl [m, n]) := by
        intro X hX
        obtain ⟨hmset, hed⟩ := hX
        unfold p16_gammaE
        rw [if_pos hed]
        obtain ⟨p, q, hpq, _hp, _hq, _hpqne⟩ := id hed
        have heps := p16_epsilon_pair (e := {m, n}) ⟨(p, q), hpq⟩
        rcases Set.pair_eq_pair_iff.mp heps with ⟨r1, r2⟩ | ⟨r1, r2⟩
        · congr 1
          · rw [r1, r2]
          · rw [r1, r2]
        · congr 1
          · rw [r1, r2, DIHX_SYM V X m n hp hs hmset hed]
          · rw [r1, r2, HL_2, HL_2, dist_comm]
      rw [p16_setSumCongr hperX,
        p16_setSumCongr
          (fun X _ => mul_comm (dihX V X (m, n)) (lmfun (hl [m, n]))),
        p16_setSum_lmull hXfin (lmfun (hl [m, n])) (fun X => dihX V X (m, n)),
        GRUTOTI1_concl V m n {m, n} hs hp hm.1 hn.1 hne
          (by rw [HL_2]; linarith [H0_LT_SQRT2, hdist]) rfl,
        p16_radV_pair m n]
      ring
    have hstep6 : (8 * mm2 / Real.pi) * setSum T2 (fun e => 2 * Real.pi * lmfun (radV e))
        = 8 * mm2 * (2 * setSum T2 (fun e => lmfun (radV e))) := by
      have hp0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have hsc : (8 * mm2 / Real.pi) * (2 * Real.pi) = 16 * mm2 := by
        field_simp
        ring
      rw [p16_setSum_lmull hT2fin (2 * Real.pi) (fun e => lmfun (radV e)),
        ← mul_assoc (8 * mm2 / Real.pi) (2 * Real.pi)
          (setSum T2 (fun e => lmfun (radV e))), hsc]
      ring
    have hscale : 0 ≤ 8 * mm2 / Real.pi :=
      div_nonneg (by linarith [p16_mm2_nonneg]) Real.pi_pos.le
    have h8nn : 0 ≤ 8 * mm2 := by linarith [p16_mm2_nonneg]
    have hmc1 : (8 * mm2 / Real.pi) * setSum S1 (fun X => setSum (edgeX V X)
            (fun e =>
              let q := Classical.epsilon fun u : V3 × V3 => e = {u.1, u.2}
              if {q.1, q.2} ∈ edgeX V X then
                dihX V X (q.1, q.2) * lmfun (hl [q.1, q.2])
              else 0))
        = (8 * mm2 / Real.pi) * setSum T1 (fun e =>
              setSum {X : Set V3 | X ∈ S1 ∧ e ∈ edgeX V X}
                (fun X => p16_gammaE V X lmfun e)) := by
      rw [hstep1, hstep2]
    have hmc2 : (8 * mm2 / Real.pi) * setSum T1 (fun e =>
            setSum {X : Set V3 | X ∈ S1 ∧ e ∈ edgeX V X}
              (fun X => p16_gammaE V X lmfun e))
        ≤ 8 * mm2 * (2 * setSum T2 (fun e => lmfun (radV e))) := by
      calc (8 * mm2 / Real.pi) * setSum T1 (fun e =>
                setSum {X : Set V3 | X ∈ S1 ∧ e ∈ edgeX V X}
                  (fun X => p16_gammaE V X lmfun e))
          ≤ (8 * mm2 / Real.pi) * setSum T2 (fun e =>
                setSum {X : Set V3 | mcellSet V X ∧ e ∈ edgeX V X}
                  (fun X => p16_gammaE V X lmfun e)) :=
            mul_le_mul_of_nonneg_left (le_trans (le_of_eq hstep3) hstep4) hscale
        _ = (8 * mm2 / Real.pi) * setSum T2 (fun e => 2 * Real.pi * lmfun (radV e)) := by
              rw [hstep5]
        _ = 8 * mm2 * (2 * setSum T2 (fun e => lmfun (radV e))) := hstep6
    set OPB : Set (V3 × V3) :=
      {p : V3 × V3 | p.1 ∈ V1 ∧ p.2 ∈ V ∧ p.2 ≠ p.1 ∧ dist p.1 p.2 ≤ 2 * h0}
      with hOPBdef
    have hsubV2 : ∀ p : V3 × V3, p.1 ∈ V1 → p.2 ∈ V → p.2 ≠ p.1 →
        dist p.1 p.2 ≤ 2 * h0 → p.2 ∈ V ∩ Metric.ball 0 (r + 2 * h0) := by
      rintro ⟨p1, p2⟩ h1 h2 _hne hd
      have hd' : dist p1 p2 ≤ 2 * h0 := hd
      have hb : p2 ∈ Metric.ball 0 (r + 2 * h0) := by
        have ht : dist 0 p2 ≤ dist 0 p1 + dist p1 p2 := dist_triangle 0 p1 p2
        have hlt : dist p1 0 < r := Metric.mem_ball.1 h1.2
        have hc : dist p1 0 = dist 0 p1 := dist_comm p1 0
        have hc2 : dist p2 0 = dist 0 p2 := dist_comm p2 0
        exact Metric.mem_ball.2 (by linarith)
      exact Set.mem_inter h2 hb
    have hoprod : setSum OPB (fun p => lmfun (radV {p.1, p.2}))
        = setSum V1 (fun u => setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
            (fun v => lmfun (radV {u, v}))) := by
      have hV2fin : (V ∩ Metric.ball 0 (r + 2 * h0)).Finite := hp.finite_inter_ball _
      have hseteq : OPB = {p : V3 × V3 |
          p ∈ V1 ×ˢ (V ∩ Metric.ball 0 (r + 2 * h0)) ∧
            p.2 ≠ p.1 ∧ dist p.1 p.2 ≤ 2 * h0} := by
        ext p
        simp only [hOPBdef, Set.mem_setOf_eq]
        constructor
        · intro hP
          have hP' := Set.mem_setOf.mp hP
          exact ⟨Set.mem_prod.mpr ⟨hP'.1, hsubV2 p hP'.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2⟩,
            hP'.2.2.1, hP'.2.2.2⟩
        · intro hP
          have hP' := Set.mem_setOf.mp hP
          obtain ⟨h1, h2⟩ := Set.mem_prod.mp hP'.1
          exact ⟨h1, h2.1, hP'.2.1, hP'.2.2⟩
      rw [hseteq, p16_setSum_filter (hV1fin.prod hV2fin)
        (fun p : V3 × V3 => p.2 ≠ p.1 ∧ dist p.1 p.2 ≤ 2 * h0)
        (fun p => lmfun (radV {p.1, p.2}))]
      try simp only []
      rw [p16_setSum_prod hV1fin hV2fin (fun p : V3 × V3 =>
          if p.2 ≠ p.1 ∧ dist p.1 p.2 ≤ 2 * h0 then lmfun (radV {p.1, p.2}) else 0)]
      try simp only []
      refine p16_setSumCongr fun u hu => ?_
      rw [← p16_setSum_filter hV2fin (fun v => v ≠ u ∧ dist u v ≤ 2 * h0)
        (fun v => lmfun (radV {u, v}))]
      have hveq : ({v : V3 | v ∈ V ∩ Metric.ball 0 (r + 2 * h0) ∧ v ≠ u ∧ dist u v ≤ 2 * h0})
          = {v : V3 | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0} := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨⟨hV, _hB⟩, hQ⟩
          exact ⟨hV, hQ⟩
        · rintro ⟨hV, hQ⟩
          obtain ⟨_hne, hd⟩ := hQ
          have hb : v ∈ Metric.ball 0 (r + 2 * h0) := by
            have ht : dist 0 v ≤ dist 0 u + dist u v := dist_triangle 0 u v
            have hlt : dist u 0 < r := Metric.mem_ball.1 hu.2
            have hc : dist u 0 = dist 0 u := dist_comm u 0
            have hc2 : dist v 0 = dist 0 v := dist_comm v 0
            exact Metric.mem_ball.2 (by linarith)
          exact ⟨Set.mem_inter hV hb, _hne, hd⟩
      rw [hveq]
    have hfinalkey : 2 * setSum T2 (fun e => lmfun (radV e))
        ≤ setSum V1 (fun u => setSum {v | v ∈ V ∧ v ≠ u ∧ dist u v ≤ 2 * h0}
          (fun v => lmfun (hl [u, v]))) := by
      have hV2fin : (V ∩ Metric.ball 0 (r + 2 * h0)).Finite := hp.finite_inter_ball _
      have hOPA : ({p : V3 × V3 | p.1 ∈ V1 ∧ p.2 ∈ V1 ∧ p.1 ≠ p.2 ∧
          dist p.1 p.2 ≤ 2 * h0}).Finite :=
        Set.Finite.subset (hV1fin.prod hV1fin) fun p hp => ⟨hp.1, hp.2.1⟩
      have hOPB : OPB.Finite :=
        Set.Finite.subset (hV1fin.prod hV2fin) fun p hp => by
          have h1 : p.1 ∈ V1 := hp.1
          have h2 : p.2 ∈ V := hp.2.1
          have h3 : p.2 ≠ p.1 := hp.2.2.1
          have h4 : dist p.1 p.2 ≤ 2 * h0 := hp.2.2.2
          have hb : p.2 ∈ Metric.ball 0 (r + 2 * h0) := by
            have ht : dist 0 p.2 ≤ dist 0 p.1 + dist p.1 p.2 := dist_triangle 0 p.1 p.2
            have hlt : dist p.1 0 < r := Metric.mem_ball.1 h1.2
            have hc : dist p.1 0 = dist 0 p.1 := dist_comm p.1 0
            have hc2 : dist p.2 0 = dist 0 p.2 := dist_comm p.2 0
            exact Metric.mem_ball.2 (by linarith)
          exact ⟨h1, Set.mem_inter h2 hb⟩
      rw [hT2def, ← SUM_PAIR_2_SET (fun e => lmfun (radV e)) V1 (2 * h0) hV1fin]
      refine le_trans (p16_setSum_le_of_subset hOPA hOPB ?_
        (fun p => lmfun (radV {p.1, p.2})) (fun p _ => lmfun_pos_le _)) ?_
      · intro p hp
        exact ⟨hp.1, hp.2.1.1, Ne.symm hp.2.2.1, hp.2.2.2⟩
      · rw [hoprod]
        exact p16_setSum_mono hV1fin _ _ fun u _ =>
          le_of_eq (p16_setSumCongr (fun v _ => congrArg lmfun (p16_radV_pair u v)))
    rw [zero_mul, add_zero, hmc1]
    have hfinal := mul_le_mul_of_nonneg_left hfinalkey h8nn
    exact le_trans hmc2 hfinal
  · exact ⟨0, fun r hs' hp' _ => absurd ⟨hs', hp'⟩ hmain⟩
