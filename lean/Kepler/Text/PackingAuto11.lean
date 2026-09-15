/-
Packing chapter, LEPJBDJ lane: a Marchal cell meets the packing exactly in
the vertices of its truncation simplex.

HOL source: Flyspeck `scripts/packing/LEPJBDJ.hl` (module `Lepjbdj`, VU KHAC
KY, Book lemma LEPJBDJ, chapter Packing / Marchal cells; 927 lines, 2
`prove_by_refinement` items, needs `marchal_cells_2.hl`). The two
conclusions:
- `LEPJBDJ` (concl HL:29-32, proof HL:43-907): for a saturated packing `V`,
  a `barV V 3` list `ul`, `1 <= k <= 4` with `mcell k V ul <> {}`,
  `V INTER mcell k V ul = set_of_list (truncate_simplex (k-1) ul)`.
- `LEPJBDJ_0` (concl HL:34-39, proof HL:913-925): under the same `V`, `ul`
  hypotheses, `V INTER mcell 0 V ul = {}` — the radial sliver `mcell0` is
  the Rogers simplex minus the `sqrt 2`-ball around `HD ul`, and `V` meets
  the Rogers simplex only in `HD ul`.

DISCHARGES convention: both conclusions are stated — with `sorry` bodies —
as the pack_concl interfaces `LEPJBDJ_concl` / `LEPJBDJ_0_concl` of
Kepler.Text.PackingAuto2 (PackingAuto2.lean:764-772). The theorems below
carry the identical statements; at merge time the `sorry` bodies of the
PackingAuto2 interfaces are replaced by `exact LEPJBDJ` / `exact LEPJBDJ_0`
and the interface docstrings deleted.

Role in the eventually-radial/limit machinery: the Marchal-cell measure
work (URRPHBZ1-3) needs each cell to be `EventuallyRadial` at its packing
points — in a small ball around `v ∈ V` the cell is a cone over finitely
many tangent directions. LEPJBDJ is the combinatorial input: it pins down
exactly WHICH packing points lie in a given cell (precisely the first `k`
truncation vertices; none for the `k = 0` sliver), so the radial
directions at a cell's packing points are finite data, and the "limit"
expression of the cell near `v` reduces to finitely many `rcone`/wedge
conditions. LEPJBDJ_0 kills the `mcell 0` annular sliver, which has no
packing points at all.

Encoding notes.
- HOL `real^3` ↔ `V3` (Kepler.Geom); HOL `packing` ↔ `Packing`
  (Kepler.Statement: any two distinct centers are at distance `≥ 2`).
- HOL `saturated`/`barV`/`truncate_simplex`/`omega_list_n`/`omega_list`/
  `set_of_list`/`voronoi_closed`/`voronoi_list`/`hl`/`rogers`/`mcell`/
  `mcell{0..4}`/`mxi`/`rcone_ge`/`rcone_gt` ↔ the same-name defs of
  Kepler.Text.PackingAuto2 (`hdV` = HOL `HD` on `real^3` lists).
- HOL `between s (a,b)` ↔ `s ∈ segment ℝ a b` (Mathlib CLOSED segment,
  endpoints allowed; the azure-tree `segment[a;b]` of Polytope.lean is the
  OPEN segment and is NOT what `between` means).
- HOL `cball`/`ball` ↔ `Metric.closedBall`/`Metric.ball`; `dist (u,v)` ↔
  `dist u v`; `norm` ↔ `‖·‖`.
- `mcell 0/1/2/3` unfold by `rfl`, `mcell k` for `k ≥ 4` via `mcellExplicit`
  below (HOL `MCELL_EXPLICIT`, marchal2.hl:262).

Private-lemma accounting (the supporting chain of LEPJBDJ.hl). Proved here
(modulo the giants): `mcellExplicit` (marchal2.hl:262 `MCELL_EXPLICIT`),
`hlPair` (LEPJBDJ.hl:131-142: `hl` of a pair, via Rogers `HL_EQ_DIST0` +
`CIRCUMCENTER_2`), `k1Case` (HL:66-123), `mcell4Nonempty` (HL:713-722),
`k4Sup` (HL:668-669), `k4Subset` (HL:674-712, modulo `simplexFurthestLt2`),
`mcell3Nonempty` + `k3Sup` (HL:728-738) and the `k3Case` assembly. Giants
with faithful statements, `sorry`-ed: `rogersInterVLemma` (marchal2.hl:626
`ROGERS_INTER_V_LEMMA`), `simplexFurthestLt2` (marchal2.hl:2393
`SIMPLEX_FURTHEST_LT_2`), `mxiExplicit` (marchal2.hl:2516 `MXI_EXPLICIT`),
`k2Case` (LEPJBDJ.hl:126-656: the projection/Pythagoras wedge argument) and
`k3Subset` (LEPJBDJ.hl:740-906: the `mxi`-Voronoi exclusion argument).
Both main theorems are assembled honestly from these pieces.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Private supporting chain (LEPJBDJ.hl / marchal2.hl) -/

/-- HOL `MCELL_EXPLICIT` (marchal2.hl:262): dispatch of `mcell` on the
index — the four base cells by `rfl`, and `mcell k = mcell4` for `k ≥ 4`. -/
private theorem mcellExplicit (k : ℕ) (V : Set V3) (ul : List V3) :
    mcell 0 V ul = mcell0 V ul ∧ mcell 1 V ul = mcell1 V ul ∧
      mcell 2 V ul = mcell2 V ul ∧ mcell 3 V ul = mcell3 V ul ∧
      (4 ≤ k → mcell k V ul = mcell4 V ul) := by
  refine ⟨rfl, rfl, rfl, rfl, fun hk => ?_⟩
  simp only [mcell, if_neg (by omega : ¬(k = 0)), if_neg (by omega : ¬(k = 1)),
    if_neg (by omega : ¬(k = 2)), if_neg (by omega : ¬(k = 3))]

/-- LEPJBDJ.hl:131-142: `hl` of a pair is half the distance between the two
points (Rogers `HL_EQ_DIST0` + `CIRCUMCENTER_2`). -/
private theorem hlPair (V : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hb : barV V 1 [u0, u1]) : hl [u0, u1] = dist u0 u1 / 2 := by
  have hhd : hdV [u0, u1] = u0 := rfl
  have hc : setOfList [u0, u1] = {u0, u1} := by
    ext x
    simp [setOfList]
  rw [HL_EQ_DIST0 V 1 [u0, u1] hp hb, hc, CIRCUMCENTER_2, hhd, dist_midpoint_left,
    Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < 2 by norm_num)]
  ring

/-- The `k = 1` case (LEPJBDJ.hl:66-123): `V INTER mcell 1 V [u0;u1;u2;u3]
= {u0}`. Membership in the cell forces `dist x u0 ≤ sqrt 2 < 2`, so the
packing property collapses every `V`-point of the cell to `u0`; `u0` itself
lies in the Rogers simplex (as `omega_list_n V ul 0`), the `sqrt 2`-ball
(dist-refl) and outside the strict radial cone (its defining inequality
degenerates to `0 > 0`). -/
private theorem k1Case (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hb : barV V 3 [u0, u1, u2, u3]) (hne : mcell 1 V [u0, u1, u2, u3] ≠ ∅) :
    V ∩ mcell 1 V [u0, u1, u2, u3] = setOfList (truncateSimplex 0 [u0, u1, u2, u3]) := by
  have hVsub := BARV_SUBSET V 3 [u0, u1, u2, u3] hb
  have htr0 : truncateSimplex 0 [u0, u1, u2, u3] = [u0] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_0 u0 u1 u2 u3).2.2.2
  rw [htr0]
  have hhd : hdV [u0, u1, u2, u3] = u0 := rfl
  have hcond : Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
    by_contra hc
    apply hne
    rw [(mcellExplicit 1 V [u0, u1, u2, u3]).2.1, mcell1, if_neg hc]
  have hcell : mcell 1 V [u0, u1, u2, u3] =
      (rogers V [u0, u1, u2, u3] ∩ Metric.closedBall (hdV [u0, u1, u2, u3])
        (Real.sqrt 2)) \
        rconeGt (hdV [u0, u1, u2, u3]) (hdV [u0, u1, u2, u3].tail)
          (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2) := by
    rw [(mcellExplicit 1 V [u0, u1, u2, u3]).2.1, mcell1, if_pos hcond]
  have hu0V : u0 ∈ V := hVsub (by simp [setOfList])
  have hu0R : u0 ∈ rogers V [u0, u1, u2, u3] :=
    subset_convexHull ℝ _ (Set.mem_image_of_mem (omegaListN V [u0, u1, u2, u3])
      (show (0 : ℕ) ∈ {j : ℕ | j < [u0, u1, u2, u3].length} by simp))
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨hxV, hx⟩
    rw [hcell, Set.mem_sdiff, Set.mem_inter_iff, Metric.mem_closedBall, hhd] at hx
    obtain ⟨⟨-, hxB⟩, -⟩ := hx
    have hxu : x = u0 := by
      by_contra hxn
      have h2 := Packing.dist_ge_two hp hxV hu0V hxn
      have h3 : Real.sqrt 2 < (2 : ℝ) := by
        have h4 : (4:ℝ) = (2:ℝ)^2 := by norm_num
        have h5 := Real.sqrt_lt_sqrt (show (0:ℝ) ≤ (2:ℝ) by norm_num)
          (show (2:ℝ) < (4:ℝ) by norm_num)
        rw [h4, Real.sqrt_sq (show (0:ℝ) ≤ (2:ℝ) by norm_num)] at h5
        exact h5
      linarith
    simp [setOfList, hxu]
  · rintro x hx
    have hxu : x = u0 := by simpa [setOfList] using hx
    rw [hxu]
    refine ⟨hu0V, ?_⟩
    rw [hcell]
    refine ⟨⟨hu0R, ?_⟩, ?_⟩
    · simp [Metric.mem_closedBall, hhd]
    · intro hmem
      simp only [rconeGt, Set.mem_setOf_eq, hhd, sub_self, dist_self,
        zero_mul] at hmem
      norm_num at hmem

/-- GIANT (marchal2.hl:2393 `SIMPLEX_FURTHEST_LT_2`): for a finite set, any
hull point outside the set is strictly closer to `a` than some set point.
(True: `x ↦ ‖x - a‖` is convex, so `‖x - a‖ ≤ max_{y ∈ s} ‖y - a‖`; equality
forces all active vertices on one ray of `a`, hence all equal to `x`,
contradicting `x ∉ s`.) -/
private theorem simplexFurthestLt2 (a : V3) (s : Set V3) (hfin : s.Finite)
    (x : V3) (hx : x ∈ convexHull ℝ s) (hxs : x ∉ s) :
    ∃ y ∈ s, ‖x - a‖ < ‖y - a‖ := by
  sorry

/-- The `mcell 4` nonemptiness bridge (LEPJBDJ.hl:713-722): a nonempty
`mcell 4` forces `hl ul < sqrt 2` (otherwise `mcell4` is definitionally
empty). -/
private theorem mcell4Nonempty (V : Set V3) (u0 u1 u2 u3 : V3)
    (hne : mcell 4 V [u0, u1, u2, u3] ≠ ∅) :
    hl [u0, u1, u2, u3] < Real.sqrt 2 := by
  by_contra hc
  apply hne
  rw [(mcellExplicit 4 V [u0, u1, u2, u3]).2.2.2.2 (by norm_num : (4:ℕ) ≤ 4),
    mcell4, if_neg hc]

/-- The `k = 4` superset direction (LEPJBDJ.hl:668-669): all four list
points are `V`-points (`barV`) and lie in the Delaunay hull. -/
private theorem k4Sup (V : Set V3) (u0 u1 u2 u3 : V3) (_hp : Packing V)
    (hb : barV V 3 [u0, u1, u2, u3]) (hlt : hl [u0, u1, u2, u3] < Real.sqrt 2) :
    setOfList [u0, u1, u2, u3] ⊆ V ∩ mcell 4 V [u0, u1, u2, u3] := by
  have hVsub := BARV_SUBSET V 3 [u0, u1, u2, u3] hb
  intro x hx
  exact ⟨hVsub hx, by
    rw [(mcellExplicit 4 V [u0, u1, u2, u3]).2.2.2.2 (by norm_num), mcell4,
      if_pos hlt]
    exact subset_convexHull ℝ _ hx⟩

/-- The `k = 4` subset direction (LEPJBDJ.hl:674-712): a `V`-point in the
Delaunay hull which is not a vertex would be strictly closer than every
vertex to `s3 = omega_list V ul`; but `s3` lies in the Voronoi list, hence
in every `voronoi_closed V y` with `y` a vertex, and `x ∈ V` gives
`dist s3 y ≤ dist s3 x` — a contradiction. -/
private theorem k4Subset (V : Set V3) (u0 u1 u2 u3 : V3) (_hp : Packing V)
    (hb : barV V 3 [u0, u1, u2, u3]) (hlt : hl [u0, u1, u2, u3] < Real.sqrt 2) :
    V ∩ mcell 4 V [u0, u1, u2, u3] ⊆ setOfList [u0, u1, u2, u3] := by
  have hVsub := BARV_SUBSET V 3 [u0, u1, u2, u3] hb
  rintro x ⟨hxV, hxHull⟩
  rw [(mcellExplicit 4 V [u0, u1, u2, u3]).2.2.2.2 (by norm_num), mcell4,
    if_pos hlt] at hxHull
  by_contra hxS
  have hfin : (setOfList [u0, u1, u2, u3]).Finite :=
    Set.Finite.ofFinset (insert u0 (insert u1 (insert u2 {u3})))
      (by intro x; simp [setOfList])
  obtain ⟨y, hyS, hydist⟩ :=
    simplexFurthestLt2 (omegaList V [u0, u1, u2, u3]) (setOfList [u0, u1, u2, u3])
      hfin x hxHull hxS
  have hyV : y ∈ V := hVsub hyS
  have havo : omegaList V [u0, u1, u2, u3] ∈ voronoiList V [u0, u1, u2, u3] :=
    OMEGA_LIST_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 hb
  have hmem : omegaList V [u0, u1, u2, u3] ∈ voronoiClosed V y :=
    Set.mem_sInter.mp havo (voronoiClosed V y)
      (Set.mem_setOf.mpr ⟨y, hyS, rfl⟩)
  have hyC : ∀ w ∈ V,
      dist (omegaList V [u0, u1, u2, u3]) y ≤ dist (omegaList V [u0, u1, u2, u3]) w :=
    Set.mem_setOf.mp hmem
  have h1 := hyC y hyV
  have h2 := hyC x hxV
  have e1 : dist (omegaList V [u0, u1, u2, u3]) y = ‖y - omegaList V [u0, u1, u2, u3]‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  have e2 : dist (omegaList V [u0, u1, u2, u3]) x = ‖x - omegaList V [u0, u1, u2, u3]‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- The `mcell 3` nonemptiness bridge (LEPJBDJ.hl:734): a nonempty `mcell 3`
forces `hl (truncate_simplex 2 ul) < sqrt 2 <= hl ul`. -/
private theorem mcell3Nonempty (V : Set V3) (u0 u1 u2 u3 : V3)
    (hne : mcell 3 V [u0, u1, u2, u3] ≠ ∅) :
    hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
  by_contra hc
  apply hne
  rw [(mcellExplicit 3 V [u0, u1, u2, u3]).2.2.2.1, mcell3, if_neg hc]

/-- The `k = 3` superset direction (LEPJBDJ.hl:734-738): `u0, u1, u2` are
`V`-points and lie in `convex hull ({u0,u1,u2} ∪ {mxi V ul})`. -/
private theorem k3Sup (V : Set V3) (u0 u1 u2 u3 : V3)
    (hb : barV V 3 [u0, u1, u2, u3])
    (hc1 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2)
    (hc2 : Real.sqrt 2 ≤ hl [u0, u1, u2, u3]) :
    setOfList [u0, u1, u2] ⊆ V ∩ mcell 3 V [u0, u1, u2, u3] := by
  have hVsub := BARV_SUBSET V 3 [u0, u1, u2, u3] hb
  have htr2 : truncateSimplex 2 [u0, u1, u2, u3] = [u0, u1, u2] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have hcell : mcell 3 V [u0, u1, u2, u3] =
      convexHull ℝ (setOfList [u0, u1, u2] ∪ {mxi V [u0, u1, u2, u3]}) := by
    rw [(mcellExplicit 3 V [u0, u1, u2, u3]).2.2.2.1, mcell3, if_pos ⟨hc1, hc2⟩,
      htr2]
  intro x hx
  have hxIn4 : x ∈ setOfList [u0, u1, u2, u3] := by
    have h2 : x ∈ [u0, u1, u2] := Set.mem_setOf.mp hx
    refine Set.mem_setOf.mpr ?_
    rw [show ([u0, u1, u2, u3] : List V3) = [u0, u1, u2] ++ [u3] from rfl]
    exact List.mem_append.mpr (Or.inl h2)
  exact ⟨hVsub hxIn4, by
    rw [hcell]
    exact subset_convexHull ℝ _ (Set.mem_union_left _ hx)⟩

/-- GIANT (LEPJBDJ.hl:740-906, `k = 3` subset direction): a `V`-point in
`mcell 3` is one of `u0, u1, u2`. Via `mxiExplicit`, `m = mxi V ul` sits on
the segment `omega_list_n V ul 2`–`omega_list_n V ul 3` at distance
`sqrt 2` from `u0`, hence (Voronoi-list membership of the omega points and
convexity of the Voronoi list) `m ∉ V`; `simplexFurthestLt2`
on `S = {u0,u1,u2,m}` then exhibits a vertex `y ∈ S` with
`norm (x - m) < norm (y - m) ≤ sqrt 2` (each of `u0,u1,u2` is at distance
`sqrt 2` from `m` by the Voronoi inequality and the cycling
`dist s u_i ≤ dist s u_{i+1}`), while `x ∈ V` and `m ∈ voronoi_closed V u0`
give `norm (x - m) ≥ sqrt 2` — a contradiction. -/
private theorem k3Subset (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 [u0, u1, u2, u3])
    (hc1 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2)
    (hc2 : Real.sqrt 2 ≤ hl [u0, u1, u2, u3]) :
    V ∩ mcell 3 V [u0, u1, u2, u3] ⊆ setOfList [u0, u1, u2] := by
  sorry

/-- Assembly of the `k = 3` case from the nonemptiness bridge and the two
inclusions (LEPJBDJ.hl:728-906). -/
private theorem k3Case (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 [u0, u1, u2, u3])
    (hne : mcell 3 V [u0, u1, u2, u3] ≠ ∅) :
    V ∩ mcell 3 V [u0, u1, u2, u3] = setOfList [u0, u1, u2] := by
  obtain ⟨hc1, hc2⟩ := mcell3Nonempty V u0 u1 u2 u3 hne
  exact Set.Subset.antisymm (k3Subset V u0 u1 u2 u3 hp hs hb hc1 hc2)
    (k3Sup V u0 u1 u2 u3 hb hc1 hc2)

/-- GIANT — the `k = 2` case (LEPJBDJ.hl:126-656). Core (HL:131-541): for
`x ∈ V ∩ mcell 2` the orthogonal projection `v = proj_point (u1 - u0)
(x - u0)` of `x` onto the edge line satisfies `between (v + u0) (u0, u1)`
(collinearity plus exclusion of the two outside cases through the
`rcone_ge` defining inequalities), hence two Pythagoras splits at `v + u0`
(HL:317-340), and — combining each `rcone_ge` membership with the packing
bound `2 ≤ dist (x, u_i)` and `a = hl [u0;u1] / sqrt 2 < 1` — the bounds
`sqrt 2 ≤ dist (v + u0, u0)` and `sqrt 2 ≤ dist (v + u0, u1)` (HL:343-521).
Since `v + u0` is between `u0` and `u1`, `dist (u0,u1) = dist (v+u0,u0) +
dist (v+u0,u1) ≥ 2 sqrt 2 = 2 * hl [u0;u1]`, contradicting `hl [u0;u1] <
sqrt 2`. HL:544-645 discharges the reverse inclusion: the endpoints
trivially satisfy the `rcone_ge`s, and the wedge `aff_ge {u0,u1}
{mxi, omega_list_n V ul 3}` contains them by the indicator-function
witness `f = λt. if t = x then 1 else 0` (`SUM_UNION_LZERO`,
`SUM_DIS2`). -/
private theorem k2Case (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 [u0, u1, u2, u3])
    (hne : mcell 2 V [u0, u1, u2, u3] ≠ ∅) :
    V ∩ mcell 2 V [u0, u1, u2, u3] = setOfList (truncateSimplex 1 [u0, u1, u2, u3]) := by
  sorry

/-! ## GIANT: the Rogers-simplex / packing intersection (marchal2.hl) -/

/-- GIANT (marchal2.hl:626 `ROGERS_INTER_V_LEMMA`): a packing point in the
Rogers simplex of a `barV V 3` list is its first vertex. -/
private theorem rogersInterVLemma (V : Set V3) (ul : List V3) (v : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) (hv : v ∈ V)
    (hr : v ∈ rogers V ul) : v = hdV ul := by
  sorry

/-- GIANT (marchal2.hl:2516 `MXI_EXPLICIT`): under the `mcell3` regime the
`mxi` point is realized on the segment from `omega_list_n V ul 2` to
`omega_list_n V ul 3` at distance `sqrt 2` from `u0` (existence of such a
point: `SEGMENT_INTER_CBALL_LEMMA`; identification with `mxi` via its
`@`-definition). -/
private theorem mxiExplicit (V : Set V3) (u0 u1 u2 u3 : V3)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 [u0, u1, u2, u3])
    (hc1 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2)
    (hc2 : Real.sqrt 2 ≤ hl [u0, u1, u2, u3]) :
    ∃ s : V3, s ∈ segment ℝ (omegaListN V [u0, u1, u2, u3] 2)
        (omegaListN V [u0, u1, u2, u3] 3) ∧
      dist u0 s = Real.sqrt 2 ∧ mxi V [u0, u1, u2, u3] = s := by
  sorry

/-! ## The two LEPJBDJ conclusions -/

/-- HOL `LEPJBDJ` (LEPJBDJ.hl:29-32; proof HL:43-907): the packing points
of a nonempty Marchal cell are exactly the first `k` truncation vertices.

DISCHARGES: `LEPJBDJ_concl` (Kepler.Text.PackingAuto2.lean:764), whose
`sorry` body is to be replaced by `exact LEPJBDJ` at merge time. -/
theorem LEPJBDJ (V : Set V3) (ul : List V3) (k : ℕ) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) (h1 : 1 ≤ k) (h4 : k ≤ 4)
    (hne : mcell k V ul ≠ ∅) :
    V ∩ mcell k V ul = setOfList (truncateSimplex (k - 1) ul) := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  subst hul
  match k, h1, h4 with
  | 0, h1', _ => exact absurd h1' (by omega)
  | 1, _, _ => exact k1Case V u0 u1 u2 u3 hp hb hne
  | 2, _, _ => exact k2Case V u0 u1 u2 u3 hp hs hb hne
  | 3, _, _ =>
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2]
      exact k3Case V u0 u1 u2 u3 hp hs hb hne
  | 4, _, _ =>
      rw [TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3]
      refine Set.Subset.antisymm ?_
        (k4Sup V u0 u1 u2 u3 hp hb (mcell4Nonempty V u0 u1 u2 u3 hne))
      intro x hx
      exact k4Subset V u0 u1 u2 u3 hp hb (mcell4Nonempty V u0 u1 u2 u3 hne) hx
  | (n + 5), _, h4' => exact absurd h4' (by omega)

/-- HOL `LEPJBDJ_0` (LEPJBDJ.hl:34-39; proof HL:913-925): the radial sliver
`mcell 0` (Rogers simplex minus the `sqrt 2`-ball around `HD ul`) contains
no packing points: a `V`-point of the Rogers simplex equals `HD ul` by
`rogersInterVLemma`, but then it lies in the ball it was removed from.

DISCHARGES: `LEPJBDJ_0_concl` (Kepler.Text.PackingAuto2.lean:770), whose
`sorry` body is to be replaced by `exact LEPJBDJ_0` at merge time. -/
theorem LEPJBDJ_0 (V : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) : V ∩ mcell 0 V ul = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro x hx
  obtain ⟨hxV, hx0⟩ := hx
  have hrogers : x ∈ rogers V ul \ Metric.ball (hdV ul) (Real.sqrt 2) := hx0
  obtain ⟨hxr, hxb⟩ := hrogers
  have hxhd : x = hdV ul := rogersInterVLemma V ul x hs hp hb hxV hxr
  apply hxb
  rw [hxhd, Metric.mem_ball, dist_self]
  exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

end Kepler.Text
