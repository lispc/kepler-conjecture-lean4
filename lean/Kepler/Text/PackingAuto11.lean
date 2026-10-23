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
(in full): `mcellExplicit` (marchal2.hl:262 `MCELL_EXPLICIT`),
`hlPair` (LEPJBDJ.hl:131-142: `hl` of a pair, via Rogers `HL_EQ_DIST0` +
`CIRCUMCENTER_2`), `k1Case` (HL:66-123), `mcell4Nonempty` (HL:713-722),
`k4Sup` (HL:668-669), `k4Subset` (HL:674-712, incl. `simplexFurthestLt2`),
`mcell3Nonempty` + `k3Sup` (HL:728-738) and the `k3Case` assembly. The
giant `simplexFurthestLt2` (marchal2.hl:2393 `SIMPLEX_FURTHEST_LT_2`) is
also FULLY PROVED here (strict convexity of closed balls + finset induction
on the hull), and `mxiExplicit` (marchal2.hl:2516 `MXI_EXPLICIT`) is fully
assembled via the pack_concl bank leaf `MXI_EXISTS_concl` (PackingAuto2;
identical to PackingAuto12.MXI_EXPLICIT); that public interface still has a
placeholder body, but `LEPJBDJ` no longer consumes `mxiExplicit`.
The three former giants are now proved with the standard three dependency
basis:
`rogersInterVLemma` (marchal2.hl:626 `ROGERS_INTER_V_LEMMA`, via the clean
`GLTVHUM` cover), `k2Case` (LEPJBDJ.hl:126-656: projection-free
`rcone_ge`/packing metric argument, core `p11_k2_core`) and `k3Subset`
(LEPJBDJ.hl:740-906: the `mxi`-Voronoi exclusion argument). Both main
theorems are assembled from these pieces.
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

FULLY PROVED. Let `y0 ∈ s` maximize `‖· - a‖`. By finset induction on the
hull (`convexHull_insert` = `convexJoin` with a singleton), every hull point
`p` satisfies `p ∈ s` or `‖p - a‖ < ‖y0 - a‖`: the two-point step uses the
segment weight decomposition and, for an interior point of a nontrivial
segment, the strict convexity of closed balls
(`strictConvex_closedBall` via the inner-product `UniformConvexSpace`
instance) to move strictly inside the `y0`-ball. Since `x ∉ s`, the strict
bound holds with witness `y0`. -/
private theorem simplexFurthestLt2 (a : V3) (s : Set V3) (hfin : s.Finite)
    (x : V3) (hx : x ∈ convexHull ℝ s) (hxs : x ∉ s) :
    ∃ y ∈ s, ‖x - a‖ < ‖y - a‖ := by
  classical
  have hne : s.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty.mp hc, convexHull_empty] at hx
    exact hx
  have htne : hfin.toFinset.Nonempty := by
    rw [← Finset.coe_nonempty, hfin.coe_toFinset]
    exact hne
  obtain ⟨y0, hy0, hmax⟩ := Finset.exists_max_image hfin.toFinset (fun y => ‖y - a‖) htne
  have key : ∀ t' : Finset V3, (∀ z ∈ t', z ∈ hfin.toFinset) →
      ∀ p ∈ convexHull ℝ ((t' : Set V3)), p ∈ s ∨ ‖p - a‖ < ‖y0 - a‖ := by
    intro t'
    induction t' using Finset.induction_on with
    | empty =>
      intro _ p hp
      rw [Finset.coe_empty, convexHull_empty] at hp
      exact hp.elim
    | @insert u t' hnu ih =>
      intro hsub p hp
      have hu : u ∈ s := by
        rw [← hfin.coe_toFinset]
        exact hsub _ (Finset.mem_insert_self u t')
      have huM : ‖u - a‖ ≤ ‖y0 - a‖ := hmax u (hsub _ (Finset.mem_insert_self u t'))
      have hsub' : ∀ z ∈ t', z ∈ hfin.toFinset := fun z hz => hsub z (Finset.mem_insert_of_mem hz)
      rw [Finset.coe_insert] at hp
      by_cases hte : (t' : Set V3).Nonempty
      · rw [convexHull_insert hte, mem_convexJoin] at hp
        obtain ⟨u', hu'1, q, hq2, hpq⟩ := hp
        have hu'eq : u' = u := by simpa using hu'1
        rw [hu'eq] at hpq
        obtain hq' : q ∈ s ∨ ‖q - a‖ < ‖y0 - a‖ := ih hsub' q hq2
        have hqM : ‖q - a‖ ≤ ‖y0 - a‖ := by
          rcases hq' with h | h
          · exact hmax q (Finset.mem_coe.mp (by rw [hfin.coe_toFinset]; exact h))
          · exact h.le
        obtain ⟨c, d, hc0, hd0, hcd, hpeq⟩ := hpq
        by_cases huq : u = q
        · rw [huq, ← add_smul, hcd, one_smul] at hpeq
          exact Or.inl (by rw [← hpeq, ← huq]; exact hu)
        by_cases hp'u : p = u
        · exact Or.inl (hp'u ▸ hu)
        by_cases hp'q : p = q
        · rcases hq' with h | h
          · exact Or.inl (by rw [hp'q]; exact h)
          · exact Or.inr (by rw [hp'q]; exact h)
        · have hcpos : 0 < c := by
            rcases lt_or_eq_of_le hc0 with e | e
            · exact e
            · exact absurd (by
                have d1 : d = 1 := by linarith
                rw [← hpeq, ← e, zero_smul, zero_add, d1, one_smul]) hp'q
          have hdpos : 0 < d := by
            rcases lt_or_eq_of_le hd0 with e | e
            · exact e
            · exact absurd (by
                have c1 : c = 1 := by linarith
                rw [← hpeq, ← e, zero_smul, add_zero, c1, one_smul]) hp'u
          have hpopen : p ∈ openSegment ℝ u q := ⟨c, d, hcpos, hdpos, hcd, hpeq⟩
          have hmemU : u ∈ Metric.closedBall a ‖y0 - a‖ := by
            rw [Metric.mem_closedBall, dist_eq_norm]
            exact huM
          have hmemQ : q ∈ Metric.closedBall a ‖y0 - a‖ := by
            rw [Metric.mem_closedBall, dist_eq_norm]
            exact hqM
          have hsub2 := (strictConvex_closedBall (𝕜 := ℝ) a ‖y0 - a‖).openSegment_subset
            hmemU hmemQ huq hpopen
          rw [interior_closedBall', Metric.mem_ball, dist_eq_norm] at hsub2
          exact Or.inr hsub2
      · have htempty : (t' : Set V3) = ∅ := by
          simpa using hte
        rw [htempty] at hp
        rw [show ((insert u (∅ : Set V3)) : Set V3) = {u} from by simp,
          convexHull_singleton] at hp
        exact Or.inl (hp ▸ hu)
  have hx' : x ∈ convexHull ℝ ((hfin.toFinset : Set V3)) := by
    rw [hfin.coe_toFinset]
    exact hx
  rcases key hfin.toFinset (fun _ hz => hz) x hx' with h | h
  · exact absurd h hxs
  · exact ⟨y0, by rw [← hfin.coe_toFinset]; exact hy0, h⟩

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

/-- A segment whose endpoint distances from `x` straddle `r` crosses the
sphere of radius `r` (chain-copy of PackingAuto12 `SEGMENT_INTER_CBALL_LEMMA`,
marchal2.hl:2481; PA11 cannot import PA12). -/
private theorem p11_segmentInterCball (x : V3) (r : ℝ) (a b : V3)
    (h1 : dist x a ≤ r) (h2 : r ≤ dist x b) :
    ∃ c : V3, c ∈ segment ℝ a b ∧ dist x c = r := by
  have hcont : ContinuousOn (fun t : ℝ => dist x (AffineMap.lineMap a b t))
      (uIcc (0:ℝ) 1) :=
    (Continuous.dist continuous_const AffineMap.lineMap_continuous).continuousOn
  have h0 : dist x (AffineMap.lineMap a b (0:ℝ)) = dist x a := by
    simp [AffineMap.lineMap_apply]
  have h1v : dist x (AffineMap.lineMap a b (1:ℝ)) = dist x b := by
    simp [AffineMap.lineMap_apply]
  have key : r ∈ uIcc (dist x (AffineMap.lineMap a b (0:ℝ)))
      (dist x (AffineMap.lineMap a b (1:ℝ))) := by
    rw [h0, h1v]
    exact mem_uIcc_of_le h1 h2
  obtain ⟨t, ht, hval⟩ := intermediate_value_uIcc hcont key
  have hI : t ∈ Icc (0:ℝ) 1 := by
    rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  exact ⟨AffineMap.lineMap a b t, lineMap_mem_segment ℝ a b hI, hval⟩

/-- GIANT (LEPJBDJ.hl:740-906, `k = 3` subset direction): a `V`-point in
`mcell 3` is one of `u0, u1, u2`. Via the `mxi` construction, `m = mxi V ul`
sits on the segment `omega_list_n V ul 2`–`omega_list_n V ul 3` at distance
`sqrt 2` from `u0` (existence re-derived here from the clean omega/Voronoi
kit rather than the pack_concl interface), hence (Voronoi-list membership of
the omega points and convexity of the Voronoi list) `m ∉ V`;
`simplexFurthestLt2`
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
  have hVsub := BARV_SUBSET V 3 [u0, u1, u2, u3] hb
  have hu0V : u0 ∈ V := hVsub (by simp [setOfList])
  have hu1V : u1 ∈ V := hVsub (by simp [setOfList])
  have hu2V : u2 ∈ V := hVsub (by simp [setOfList])
  have htr2 : truncateSimplex 2 [u0, u1, u2, u3] = [u0, u1, u2] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have htr3 : truncateSimplex 3 [u0, u1, u2, u3] = [u0, u1, u2, u3] :=
    TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3
  intro x hx
  obtain ⟨hxV, hxcell⟩ := hx
  by_cases hxS : x ∈ setOfList [u0, u1, u2]
  · exact hxS
  · exfalso
    have hbar2 : barV V 2 [u0, u1, u2] := by
      have h := TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, u2, u3] hb (by omega)
      rwa [htr2] at h
    have hl2' : hl [u0, u1, u2] < Real.sqrt 2 := by rw [← htr2]; exact hc1
    have hcc2 : omegaListN V [u0, u1, u2, u3] 2 =
        circumcenter (setOfList [u0, u1, u2]) := by
      rw [OMEGA_LIST_TRUNCATE_2 V u0 u1 u2 u3,
        XNHPWAB1 V [u0, u1, u2] 2 hp hbar2 hl2']
    have hd0 : dist u0 (omegaListN V [u0, u1, u2, u3] 2)
        = hl (truncateSimplex 2 [u0, u1, u2, u3]) := by
      rw [htr2, hcc2, HL_EQ_DIST0 V 2 [u0, u1, u2] hp hbar2]
      have hhd : hdV [u0, u1, u2] = u0 := rfl
      rw [hhd, dist_comm]
    have hlt2 : dist u0 (omegaListN V [u0, u1, u2, u3] 2) < Real.sqrt 2 := by
      rw [hd0]; exact hc1
    have homega3 : omegaList V [u0, u1, u2, u3] =
        omegaListN V [u0, u1, u2, u3] 3 := rfl
    have hge3 : Real.sqrt 2 ≤ dist u0 (omegaListN V [u0, u1, u2, u3] 3) := by
      have h := WAUFCHE1 V [u0, u1, u2, u3] 3 hp hb
      rw [homega3, show hdV [u0, u1, u2, u3] = u0 from rfl, dist_comm] at h
      linarith
    obtain ⟨c, hcseg, hcdist⟩ :=
      p11_segmentInterCball u0 (Real.sqrt 2)
        (omegaListN V [u0, u1, u2, u3] 2) (omegaListN V [u0, u1, u2, u3] 3)
        (le_of_lt hlt2) hge3
    have hnotle : ¬(Real.sqrt 2 ≤ hl (truncateSimplex 2 [u0, u1, u2, u3])) :=
      not_le.mpr hc1
    have hmxiP : (mxi V [u0, u1, u2, u3] ∈ convexHull ℝ
          {omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} ∧
        dist (mxi V [u0, u1, u2, u3]) (hdV [u0, u1, u2, u3]) = Real.sqrt 2) := by
      unfold mxi
      rw [if_neg hnotle]
      exact Classical.epsilon_spec
        (show ∃ y : V3, y ∈ convexHull ℝ
            {omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} ∧
          dist y (hdV [u0, u1, u2, u3]) = Real.sqrt 2 from
          ⟨c, by rw [convexHull_pair]; exact hcseg, by rw [dist_comm]; exact hcdist⟩)
    have hbase : dist (mxi V [u0, u1, u2, u3]) u0 = Real.sqrt 2 := by
      rw [← show hdV [u0, u1, u2, u3] = u0 from rfl]
      exact hmxiP.2
    have hs2 : omegaListN V [u0, u1, u2, u3] 2 ∈ voronoiList V [u0, u1, u2] := by
      have h := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 2 hb (by norm_num)
      rwa [htr2] at h
    have hs3' : omegaListN V [u0, u1, u2, u3] 3 ∈
        voronoiList V [u0, u1, u2, u3] := by
      have h := OMEGA_LIST_N_IN_VORONOI_LIST V [u0, u1, u2, u3] 3 3 hb le_rfl
      rwa [htr3] at h
    have hsub : setOfList [u0, u1, u2] ⊆ setOfList [u0, u1, u2, u3] := by
      intro z hz
      simp [setOfList] at hz ⊢
      tauto
    have hs3 : omegaListN V [u0, u1, u2, u3] 3 ∈ voronoiList V [u0, u1, u2] :=
      VORONOI_SET_SUBSET V (setOfList [u0, u1, u2]) (setOfList [u0, u1, u2, u3])
        hsub hs3'
    have hsvl : mxi V [u0, u1, u2, u3] ∈ voronoiList V [u0, u1, u2] :=
      convexHull_min (by
        intro z hz
        rcases hz with rfl | rfl
        · exact hs2
        · exact hs3) (CONVEX_VORONOI_LIST V [u0, u1, u2]) hmxiP.1
    have hvc_mem : ∀ y ∈ ({u0, u1, u2} : Set V3),
        mxi V [u0, u1, u2, u3] ∈ voronoiClosed V y := by
      intro y hy
      exact Set.mem_sInter.mp hsvl (voronoiClosed V y)
        (Set.mem_setOf.mpr ⟨y, by simpa [setOfList] using hy, rfl⟩)
    have hvc0 : mxi V [u0, u1, u2, u3] ∈ voronoiClosed V u0 := hvc_mem u0 (by simp)
    have hvc1 : mxi V [u0, u1, u2, u3] ∈ voronoiClosed V u1 := hvc_mem u1 (by simp)
    have hvc2 : mxi V [u0, u1, u2, u3] ∈ voronoiClosed V u2 := hvc_mem u2 (by simp)
    have h01 : dist (mxi V [u0, u1, u2, u3]) u0 ≤
        dist (mxi V [u0, u1, u2, u3]) u1 := Set.mem_setOf.mp hvc0 u1 hu1V
    have h12 : dist (mxi V [u0, u1, u2, u3]) u1 ≤
        dist (mxi V [u0, u1, u2, u3]) u2 := Set.mem_setOf.mp hvc1 u2 hu2V
    have h20 : dist (mxi V [u0, u1, u2, u3]) u2 ≤
        dist (mxi V [u0, u1, u2, u3]) u0 := Set.mem_setOf.mp hvc2 u0 hu0V
    have hd1 : dist (mxi V [u0, u1, u2, u3]) u1 = Real.sqrt 2 :=
      le_antisymm (by linarith [h12, h20, hbase]) (by linarith [h01, hbase])
    have hd2 : dist (mxi V [u0, u1, u2, u3]) u2 = Real.sqrt 2 :=
      le_antisymm (by linarith [h20, hbase]) (by linarith [h01, h12, hbase])
    have hmV : mxi V [u0, u1, u2, u3] ∉ V := by
      intro hmV'
      have hle := Set.mem_setOf.mp hvc0 _ hmV'
      rw [dist_self] at hle
      linarith [hbase, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
    have hcell : mcell 3 V [u0, u1, u2, u3] =
        convexHull ℝ (setOfList [u0, u1, u2] ∪ {mxi V [u0, u1, u2, u3]}) := by
      rw [(mcellExplicit 3 V [u0, u1, u2, u3]).2.2.2.1, mcell3, if_pos ⟨hc1, hc2⟩,
        htr2]
    rw [hcell] at hxcell
    have hS : ({u0, u1, u2, mxi V [u0, u1, u2, u3]} : Set V3) =
        setOfList [u0, u1, u2] ∪ {mxi V [u0, u1, u2, u3]} := by
      ext z
      simp [setOfList]
      tauto
    rw [← hS] at hxcell
    have hfin : ({u0, u1, u2, mxi V [u0, u1, u2, u3]} : Set V3).Finite :=
      Set.Finite.ofFinset (insert u0 (insert u1 (insert u2 {mxi V [u0, u1, u2, u3]})))
        (by intro z; simp)
    have hxS' : x ∉ ({u0, u1, u2, mxi V [u0, u1, u2, u3]} : Set V3) := by
      intro hxS''
      rcases hxS'' with h | h | h | h
      · exact hxS (by rw [h]; simp [setOfList])
      · exact hxS (by rw [h]; simp [setOfList])
      · exact hxS (by rw [h]; simp [setOfList])
      · exact hmV (h ▸ hxV)
    obtain ⟨y, hyS, hxy⟩ := simplexFurthestLt2 (mxi V [u0, u1, u2, u3])
      ({u0, u1, u2, mxi V [u0, u1, u2, u3]} : Set V3) hfin x hxcell hxS'
    have hbound : ‖y - mxi V [u0, u1, u2, u3]‖ ≤ Real.sqrt 2 := by
      have e0 : ‖u0 - mxi V [u0, u1, u2, u3]‖ =
          dist (mxi V [u0, u1, u2, u3]) u0 := by
        rw [dist_comm]
        exact (dist_eq_norm u0 (mxi V [u0, u1, u2, u3])).symm
      have e1 : ‖u1 - mxi V [u0, u1, u2, u3]‖ =
          dist (mxi V [u0, u1, u2, u3]) u1 := by
        rw [dist_comm]
        exact (dist_eq_norm u1 (mxi V [u0, u1, u2, u3])).symm
      have e2 : ‖u2 - mxi V [u0, u1, u2, u3]‖ =
          dist (mxi V [u0, u1, u2, u3]) u2 := by
        rw [dist_comm]
        exact (dist_eq_norm u2 (mxi V [u0, u1, u2, u3])).symm
      rcases hyS with h | h | h | h
      · rw [h, e0]
        exact hbase.le
      · rw [h, e1]
        exact hd1.le
      · rw [h, e2]
        exact hd2.le
      · rw [h]
        simp only [sub_self, norm_zero]
        exact Real.sqrt_nonneg 2
    have hlt : ‖x - mxi V [u0, u1, u2, u3]‖ < Real.sqrt 2 :=
      lt_of_lt_of_le hxy hbound
    have hge : Real.sqrt 2 ≤ ‖x - mxi V [u0, u1, u2, u3]‖ := by
      have hle : dist (mxi V [u0, u1, u2, u3]) u0 ≤
          dist (mxi V [u0, u1, u2, u3]) x := Set.mem_setOf.mp hvc0 x hxV
      have ex : dist (mxi V [u0, u1, u2, u3]) x =
          ‖x - mxi V [u0, u1, u2, u3]‖ := by
        rw [dist_comm]
        exact dist_eq_norm x (mxi V [u0, u1, u2, u3])
      linarith
    linarith

/-- Assembly of the `k = 3` case from the nonemptiness bridge and the two
inclusions (LEPJBDJ.hl:728-906). -/
private theorem k3Case (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 [u0, u1, u2, u3])
    (hne : mcell 3 V [u0, u1, u2, u3] ≠ ∅) :
    V ∩ mcell 3 V [u0, u1, u2, u3] = setOfList [u0, u1, u2] := by
  obtain ⟨hc1, hc2⟩ := mcell3Nonempty V u0 u1 u2 u3 hne
  exact Set.Subset.antisymm (k3Subset V u0 u1 u2 u3 hp hs hb hc1 hc2)
    (k3Sup V u0 u1 u2 u3 hb hc1 hc2)

/-- A vertex of `s` lies in `affGe s t` for finite `s ∪ t` (chain-copy of
PackingAuto12 `p12_mem_affGe_vertex`; PA11 cannot import PA12). -/
private theorem p11_mem_affGe_vertex {s t : Set V3} (hfin : (s ∪ t).Finite) {v : V3}
    (hv : v ∈ s) : v ∈ affGe s t := by
  have hvF : v ∈ hfin.toFinset := by
    simpa [Set.Finite.mem_toFinset] using Set.mem_union_left _ hv
  refine ⟨fun p => if p = v then 1 else 0, hfin, ?_, ?_, ?_⟩
  · show v = ∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0) • p
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v →
        (if p = v then (1:ℝ) else 0) • p = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp
  · intro p hp
    by_cases hpv : p = v <;> simp [hpv]
  · show (∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0)) = 1
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v →
        (if p = v then (1:ℝ) else 0) = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp

/-- Metric core of the `k = 2` subset direction (LEPJBDJ.hl:169-541), in a
projection-free form: with `L = dist u0 u1`, `A = (x-u0)·(u1-u0)` and
`t = A/L²`, putting `s = tL` and `w = (1-t)L` the two `rcone_ge` memberships
give `s ≥ dist x u0 · a` and `w ≥ dist x u1 · a`; since `s + w = L`, the
packing bound `2 ≤ dist` and `a = L/(2√2)` force `L ≥ 2L/√2`, impossible. -/
private lemma p11_k2_core (u0 u1 x : V3)
    (hLpos : 0 < dist u0 u1)
    (h0ge : 2 ≤ dist x u0) (h1ge : 2 ≤ dist x u1)
    (a : ℝ) (ha0 : 0 < a)
    (haL : a = dist u0 u1 / (2 * Real.sqrt 2))
    (hr0 : (x - u0) ⬝ᵥ (u1 - u0) ≥ dist x u0 * dist u1 u0 * a)
    (hr1 : (x - u1) ⬝ᵥ (u0 - u1) ≥ dist x u1 * dist u0 u1 * a) :
    False := by
  set L : ℝ := dist u0 u1 with hL
  set d0 : ℝ := dist x u0 with hd0
  set d1 : ℝ := dist x u1 with hd1
  set A : ℝ := (x - u0) ⬝ᵥ (u1 - u0) with hA
  have hLpos' : 0 < L := hLpos
  have hLne : L ≠ 0 := hLpos'.ne'
  have hd0ge : 2 ≤ d0 := h0ge
  have hd1ge : 2 ≤ d1 := h1ge
  have hd10 : dist u1 u0 = L := by rw [dist_comm]
  set t : ℝ := A / (L * L) with ht
  set s : ℝ := t * L with hs
  set w : ℝ := (1 - t) * L with hw
  have hr0' : A ≥ d0 * L * a := by
    have h := hr0
    rwa [hd10] at h
  have hr1' : (x - u1) ⬝ᵥ (u0 - u1) ≥ d1 * L * a := hr1
  have hAeq : A = s * L := by
    rw [hs, ht]
    field_simp [hLne]
  have hsw : s + w = L := by
    rw [hs, hw]
    ring
  have hAin : inner ℝ (x - u0) (u1 - u0) = A := by
    rw [hA]; exact inner_eq_dot _ _
  have hLsq : inner ℝ (u1 - u0) (u1 - u0) = L * L := by
    have h1 : inner ℝ (u1 - u0) (u1 - u0) = (u1 - u0) ⬝ᵥ (u1 - u0) :=
      inner_eq_dot _ _
    rw [h1]
    have h2 : (u1 - u0) ⬝ᵥ (u1 - u0) = ‖u1 - u0‖ ^ 2 := (norm_sq_eq_dot _).symm
    rw [h2, hL, dist_eq_norm]
    rw [show ‖u0 - u1‖ = ‖u1 - u0‖ from norm_sub_rev u0 u1]
    ring
  have hBeq : (x - u1) ⬝ᵥ (u0 - u1) = w * L := by
    have hdot : inner ℝ (x - u1) (u0 - u1) = L * L - A := by
      have e1 : x - u1 = (x - u0) - (u1 - u0) := by abel
      have e2 : u0 - u1 = -(u1 - u0) := by abel
      rw [e1, e2, inner_sub_left, inner_neg_right, inner_neg_right, hAin, hLsq]
      ring
    calc (x - u1) ⬝ᵥ (u0 - u1) = inner ℝ (x - u1) (u0 - u1) :=
          (inner_eq_dot _ _).symm
      _ = L * L - A := hdot
      _ = w * L := by
          rw [hAeq]
          nlinarith [hsw]
  have hs_ge : s ≥ d0 * a := by
    have h : L * (d0 * a) ≤ L * s := by
      have h' : s * L ≥ d0 * L * a := by rw [← hAeq]; exact hr0'
      nlinarith [h']
    exact (mul_le_mul_iff_right₀ hLpos').mp h
  have hw_ge : w ≥ d1 * a := by
    have h : L * (d1 * a) ≤ L * w := by
      have h' : w * L ≥ d1 * L * a := by rw [← hBeq]; exact hr1'
      nlinarith [h']
    exact (mul_le_mul_iff_right₀ hLpos').mp h
  have hsum : L ≥ (d0 + d1) * a := by
    have h : s + w ≥ d0 * a + d1 * a := add_le_add hs_ge hw_ge
    linarith
  have h4 : (d0 + d1) * a ≥ 4 * a := by nlinarith [hd0ge, hd1ge, ha0]
  have hLge : L ≥ 4 * a := le_trans h4 hsum
  have haL' : a = L / (2 * Real.sqrt 2) := by rw [haL, hL]
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h4' : 4 * (L / (2 * Real.sqrt 2)) ≤ L := by
    rw [haL'] at hLge
    exact hLge
  have hmul : L * Real.sqrt 2 ≥ 2 * L := by
    have h' : 4 * (L / (2 * Real.sqrt 2)) * Real.sqrt 2 ≤ L * Real.sqrt 2 :=
      mul_le_mul_of_nonneg_right h4' hspos.le
    have he : 4 * (L / (2 * Real.sqrt 2)) * Real.sqrt 2 = 2 * L := by
      field_simp [hspos.ne']
      ring
    linarith
  have hs2ge : 2 ≤ Real.sqrt 2 := by
    have h : L * 2 ≤ L * Real.sqrt 2 := by linarith
    exact (mul_le_mul_iff_right₀ hLpos').mp h
  have hs2lt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  linarith

/-- GIANT — the `k = 2` case (LEPJBDJ.hl:126-656). Subset direction
(HL:169-541), projection-free: for `x ∈ V ∩ mcell 2` with `x ∉ {u0,u1}` the
two `rcone_ge` memberships and the packing bound `2 ≤ dist (x, u_i)` force
`dist (u0,u1) ≥ 2√2` (`p11_k2_core`), while the nonemptiness guard gives
`hl [u0;u1] < √2`, i.e. `dist (u0,u1) < 2√2`. Reverse inclusion
(HL:544-645): `u0,u1` satisfy the two `rcone_ge`s (`0 ≥ 0` at the base point,
`L² ≥ L²a` at the other since `a < 1`) and lie in the wedge
`aff_ge {u0,u1} {mxi, omega_list_n V ul 3}` as vertices (indicator weights). -/
private theorem k2Case (V : Set V3) (u0 u1 u2 u3 : V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 [u0, u1, u2, u3])
    (hne : mcell 2 V [u0, u1, u2, u3] ≠ ∅) :
    V ∩ mcell 2 V [u0, u1, u2, u3] = setOfList (truncateSimplex 1 [u0, u1, u2, u3]) := by
  have htr1 : truncateSimplex 1 [u0, u1, u2, u3] = [u0, u1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2
  have hcond : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
      Real.sqrt 2 ≤ hl [u0, u1, u2, u3] := by
    by_contra hc
    exact hne (by rw [(mcellExplicit 2 V [u0, u1, u2, u3]).2.2.1, mcell2, if_neg hc])
  obtain ⟨hc1, hc2⟩ := hcond
  have hcell : mcell 2 V [u0, u1, u2, u3] =
      (rconeGe u0 u1 (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2) ∩
        rconeGe u1 u0 (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2)) ∩
      affGe {u0, u1} {mxi V [u0, u1, u2, u3], omegaListN V [u0, u1, u2, u3] 3} := by
    rw [(mcellExplicit 2 V [u0, u1, u2, u3]).2.2.1, mcell2, if_pos ⟨hc1, hc2⟩]
    dsimp only [hdV]
    simp only [List.headD_cons, List.tail_cons]
  have hVsub := BARV_SUBSET V 3 [u0, u1, u2, u3] hb
  have hu0V : u0 ∈ V := hVsub (by simp [setOfList])
  have hu1V : u1 ∈ V := hVsub (by simp [setOfList])
  have hb1 : barV V 1 [u0, u1] := by
    have h := TRUNCATE_SIMPLEX_BARV V 1 3 [u0, u1, u2, u3] hb (by omega)
    rwa [htr1] at h
  have hne01 : u0 ≠ u1 := by
    intro he
    have hv1 : voronoiNondg V [u0, u1] :=
      hb.2 [u0, u1] ⟨⟨[u2, u3], rfl⟩, by simp⟩
    have hv0 : voronoiNondg V [u0] :=
      hb.2 [u0] ⟨⟨[u1, u2, u3], rfl⟩, by simp⟩
    have hset : setOfList [u0, u1] = setOfList [u0] := by
      rw [he]; simp [setOfList]
    have hvl : voronoiList V [u0, u1] = voronoiList V [u0] := by
      rw [voronoiList, voronoiList, hset]
    have h1 : affDim (voronoiList V [u0, u1]) + 2 = 4 := hv1.2.2
    have h0 : affDim (voronoiList V [u0]) + 1 = 4 := hv0.2.2
    rw [hvl] at h1
    linarith
  have hLpos : 0 < dist u0 u1 := dist_pos.mpr hne01
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ha0 : 0 < hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2 := by
    rw [htr1, hlPair V u0 u1 hp hb1]
    exact div_pos (div_pos hLpos (by norm_num)) hspos
  have haL : hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2 =
      dist u0 u1 / (2 * Real.sqrt 2) := by
    rw [htr1, hlPair V u0 u1 hp hb1]
    ring
  have ha_lt_one : hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2 < 1 := by
    rw [div_lt_one hspos]
    exact hc1
  have hLsq : (u1 - u0) ⬝ᵥ (u1 - u0) = dist u0 u1 * dist u0 u1 := by
    have h2 : (u1 - u0) ⬝ᵥ (u1 - u0) = ‖u1 - u0‖ ^ 2 := (norm_sq_eq_dot _).symm
    rw [h2, dist_eq_norm]
    rw [show ‖u0 - u1‖ = ‖u1 - u0‖ from norm_sub_rev u0 u1]
    ring
  have hLsq' : (u0 - u1) ⬝ᵥ (u0 - u1) = dist u0 u1 * dist u0 u1 := by
    have h2 : (u0 - u1) ⬝ᵥ (u0 - u1) = ‖u0 - u1‖ ^ 2 := (norm_sq_eq_dot _).symm
    rw [h2, dist_eq_norm]
    ring
  have hfinaff : ({u0, u1} ∪
      {mxi V [u0, u1, u2, u3], omegaListN V [u0, u1, u2, u3] 3} : Set V3).Finite :=
    Set.Finite.ofFinset
      (insert u0 (insert u1 (insert (mxi V [u0, u1, u2, u3])
        {omegaListN V [u0, u1, u2, u3] 3})))
      (by
        intro z
        simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_union,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto)
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxV, hxcell⟩ := hx
    rw [htr1]
    by_cases hxS : x ∈ setOfList [u0, u1]
    · exact hxS
    · exfalso
      have hx0 : x ≠ u0 := by
        intro h
        exact hxS (by rw [h]; simp [setOfList])
      have hx1 : x ≠ u1 := by
        intro h
        exact hxS (by rw [h]; simp [setOfList])
      rw [hcell] at hxcell
      obtain ⟨⟨hr0, hr1⟩, -⟩ := hxcell
      simp only [rconeGe, Set.mem_setOf_eq] at hr0 hr1
      have h0ge : 2 ≤ dist x u0 := Packing.dist_ge_two hp hxV hu0V hx0
      have h1ge : 2 ≤ dist x u1 := Packing.dist_ge_two hp hxV hu1V hx1
      exact p11_k2_core u0 u1 x hLpos h0ge h1ge
        (hl (truncateSimplex 1 [u0, u1, u2, u3]) / Real.sqrt 2) ha0 haL hr0 hr1
  · intro x hx
    rw [htr1] at hx
    have hx01 : x = u0 ∨ x = u1 := by simpa [setOfList] using hx
    rcases hx01 with hx0 | hx1
    · rw [hx0]
      refine ⟨hu0V, ?_⟩
      rw [hcell]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp [rconeGe]
      · simp only [rconeGe, Set.mem_setOf_eq, hLsq']
        have hnn : 0 ≤ dist u0 u1 * dist u0 u1 := mul_nonneg dist_nonneg dist_nonneg
        nlinarith [ha_lt_one, hnn]
      · exact p11_mem_affGe_vertex hfinaff (by simp)
    · rw [hx1]
      refine ⟨hu1V, ?_⟩
      rw [hcell]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [rconeGe, Set.mem_setOf_eq]
        rw [show dist u1 u0 = dist u0 u1 from dist_comm u1 u0]
        rw [hLsq]
        have hnn : 0 ≤ dist u0 u1 * dist u0 u1 := mul_nonneg dist_nonneg dist_nonneg
        nlinarith [ha_lt_one, hnn]
      · simp [rconeGe]
      · exact p11_mem_affGe_vertex hfinaff (by simp)

/-! ## GIANT: the Rogers-simplex / packing intersection (marchal2.hl) -/

/-- GIANT (marchal2.hl:626 `ROGERS_INTER_V_LEMMA`): a packing point in the
Rogers simplex of a `barV V 3` list is its first vertex. -/
private theorem rogersInterVLemma (V : Set V3) (ul : List V3) (v : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) (hv : v ∈ V)
    (hr : v ∈ rogers V ul) : v = hdV ul := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  subst hul
  have hVsub := BARV_SUBSET V 3 [u0, u1, u2, u3] hb
  have hu0V : u0 ∈ V := hVsub (by simp [setOfList])
  have htr0 : truncateSimplex 0 [u0, u1, u2, u3] = [u0] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_0 u0 u1 u2 u3).2.2.2
  have hvc : v ∈ voronoiClosed V u0 :=
    (GLTVHUM V u0 v ⟨hp, hs⟩ hu0V).mpr ⟨[u0, u1, u2, u3], hb, hr, htr0⟩
  have hle : dist v u0 ≤ dist v v := Set.mem_setOf.mp hvc v hv
  have hd0 : dist v u0 = 0 := le_antisymm (by simpa using hle) dist_nonneg
  have hvu : v = u0 := dist_eq_zero.mp hd0
  simpa [hdV] using hvu

/-- Two-point hull = segment (verbatim = PackingAuto12 `p12_hull_pair`). -/
private theorem p11_hull_pair (a b : V3) :
    convexHull ℝ ({a, b} : Set V3) = segment ℝ a b := by
  refine Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · refine convexHull_min (fun w hw => ?_) (convex_segment (𝕜 := ℝ) a b) hz
    rcases hw with rfl | hw'
    · exact left_mem_segment ℝ _ _
    · rw [hw']
      exact right_mem_segment ℝ _ _
  · rcases hz with ⟨u, w, hu, hw, huw, rfl⟩
    have hconv := convex_convexHull (𝕜 := ℝ) (s := ({a, b} : Set V3))
    exact hconv (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
      hu hw huw

/-- GIANT (marchal2.hl:2516 `MXI_EXPLICIT`): under the `mcell3` regime the
`mxi` point is realized on the segment from `omega_list_n V ul 2` to
`omega_list_n V ul 3` at distance `sqrt 2` from `u0`.

FULLY ASSEMBLED (2026-10-08) by consuming the pack_concl bank leaf
`MXI_EXISTS_concl` (PackingAuto2, the DISCHARGES-convention interface; the
identical assembly is PackingAuto12.MXI_EXPLICIT): the existence half
(HL SEGMENT_INTER_CBALL_LEMMA) and the `mxi` identification live behind that
interface; here only the two-point hull = segment reading and the
`hdV`/`dist`-comm bookkeeping are discharged. -/
private theorem mxiExplicit (V : Set V3) (u0 u1 u2 u3 : V3)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 [u0, u1, u2, u3])
    (hc1 : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2)
    (hc2 : Real.sqrt 2 ≤ hl [u0, u1, u2, u3]) :
    ∃ s : V3, s ∈ segment ℝ (omegaListN V [u0, u1, u2, u3] 2)
        (omegaListN V [u0, u1, u2, u3] 3) ∧
      dist u0 s = Real.sqrt 2 ∧ mxi V [u0, u1, u2, u3] = s := by
  have hm := MXI_EXISTS_concl V [u0, u1, u2, u3] hs hp hb hc1 hc2
  rw [show hdV [u0, u1, u2, u3] = u0 from rfl] at hm
  refine ⟨mxi V [u0, u1, u2, u3], ?_, ?_, rfl⟩
  · rw [← p11_hull_pair]
    exact hm.1
  · rw [dist_comm]
    exact hm.2

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
