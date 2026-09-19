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
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto12
import Mathlib

set_option maxHeartbeats 5000000

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
  sorry

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
  sorry

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

/-- GIANT — HOL `KIZHLTL4` (KIZHLTL.hl:533-546 concl, 548-1032 proof): the
`lmfun` specialization of the edge bound, `dist <= 2 * h0` (with `c = 0` in
the HL proof's annulus budget `8 * mm2 * (0)`). The inner edge sum keeps the
HL `\{u,v}. if {u,v} IN edgeX V X then ... else &0` guard verbatim (encoded
by the gammaX epsilon convention); the reordering
`sum S1 (sum (edgeX) (g X)) = sum (pairs) (sum over cells)` uses NEEDS
DIHX_SYM (marchal3.hl — parallel-owned Auto15, `_p16` copy at fill-in),
NEEDS FINITE_MCELL_SET_LEMMA / MCELL_SUBSET_BALL_4 / PACKING_BALL_BOUNDARY
(marchal3.hl), NEEDS FINITE_LIST_KY_LEMMA_2, and the bound `|lmfun|` against
the `V∩ball 0 r`-edge sum reuses the KIZHLTL3 architecture.

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
  sorry
