/-
Packing chapter, Marchal-cells capstones: EMNWUUS, NJIUTIU, TEZFFSK.

HOL sources: Flyspeck `scripts/packing/EMNWUUS.hl` (525 lines, theorems
`EMNWUUS1`/`EMNWUUS2`), `scripts/packing/NJIUTIU.hl` (581 lines; supporting
lemmas `CLOSEST_POINT_SUBSET_lemma`, `AFF_DEPENDENT_AFF_DIM_4`, main theorem
`NJIUTIU`), `scripts/packing/TEZFFSK.hl` (586 lines, theorem `TEZFFSK`).
All by VU KHAC KY, chapter "Packing (Marchal Cells)", 2010. These prove the
pack_concl capstone interfaces: `EMNWUUS1`/`EMNWUUS2` discharge the
sorry'd `EMNWUUS1_concl`/`EMNWUUS2_concl` of PackingAuto2 (statement-identical
delegation `:= EMNWUUS1_concl` is forbidden — the proofs are re-ported here);
`NJIUTIU`/`TEZFFSK` have no pack_concl interfaces and are stated from the
inline `NJIUTIU_concl`/`TEZFFSK_concl` of their HL modules.

Proof status.
- `EMNWUUS1`, `EMNWUUS2`: FULLY PROVED (no `sorry`), following the HL
  refinement scripts. `EMNWUUS2` forward: `mcell1..3` are empty because their
  guards demand `sqrt 2 <= hl ul`; `mcell0` is empty because every hull point
  `omega_list_n V ul i` sits at circumradius distance
  `hl (truncate_simplex i ul) <= hl ul < sqrt 2` from `HD ul`
  (BALL_CONVEX_HULL_LEMMA). Backward: for `sqrt 2 <= hl ul` the omega point
  lies in `rogers \ ball(HD ul, sqrt 2)` (WAUFCHE1), so `mcell0 != {}`.
- `CLOSEST_POINT_SUBSET_lemma`, `AFF_DEPENDENT_AFF_DIM_4` (NJIUTIU supports),
  `NJIUTIU`, `TEZFFSK`: stated faithfully, proofs skeletoned with the
  tractable reductions discharged and the geometric core `sorry`'d (see the
  per-theorem notes).

Encoding notes (following PackingAuto2/8 conventions).
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler.Geom);
  `truncate_simplex`/`omega_list_n`/`omega_list`/`barV`/`hl`/`saturated`/
  `set_of_list`/`rogers`/`mcell i` ↔ the Kepler.Text.PackingAuto2 defs;
  `initial_sublist` ↔ `initialSublist`; `aff_dim` ↔ `affDim` (Polytope);
  `affine_dependent` ↔ `affineDependent` (PackingAuto2, family indexed by
  `↥S`); `circumcenter`/`radV` on `Set V3` (HOL `{a,b}` ↔ `{a, b}`).
- HOL `dist (x,y)` ↔ `dist x y`; `ball (x,r)` ↔ `Metric.ball x r`;
  `sqrt (&2)` ↔ `Real.sqrt 2`; `HD ul` ↔ `hdV ul`.
- HL Rogers helpers used below are the PackingAuto6/7 ports (`OAPVION2`,
  `XNHPWAB4`, `WAUFCHE1`, `BARV_AFFINE_INDEPENDENT`,
  `ROGERS_AFF_DIM_FULL`, `HL_DECREASE`); the `set_of_list = {a,b,...}`
  set-literal identifications are discharged by the private
  `setOfList_pair/three/four` and `not_affineDependent_subset` helpers.
- `truncate_simplex k ul` on a 4-point `barV V 3` list ↔ the explicit
  prefixes of PackingAuto8 `TRUNCATE_SIMPLEX_EXPLICIT_{0..3}`; the omega
  points reduce to circumcenters via PackingAuto8 `OMEGA_LIST_i_EXPLICIT`
  (whose own Rogers dependencies travel through the pack_concl interfaces).
- Imports: `Kepler.Text.PackingAuto2` (defs + concl interfaces),
  `Kepler.Text.PackingAuto5` (truncation/initial-sublist kit),
  `Kepler.Text.PackingAuto6/7` (Rogers ports), `Kepler.Text.PackingAuto8`
  (marchal1 truncation bridge), `Kepler.Text.Polytope` (`affDim`), `Mathlib`.
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

/-! ## Support: affine-dependence restriction to subsets -/

private theorem not_affineDependent_subset {S T : Set V3} (hsub : S ⊆ T)
    (hT : ¬ affineDependent T) : ¬ affineDependent S := by
  intro hS
  refine hS ?_
  have hinj : Function.Injective (fun x : S => (⟨(x : V3), hsub x.2⟩ : T)) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    simp only [Subtype.mk.injEq] at h
    exact SetCoe.ext h
  exact (not_not.mp hT).comp_embedding ⟨_, hinj⟩

/-! ## EMNWUUS (EMNWUUS.hl) -/

private theorem setOfList_pair (a b : V3) : setOfList [a, b] = {a, b} := by
  ext x; simp [setOfList]

private theorem setOfList_three (a b c : V3) : setOfList [a, b, c] = {a, b, c} := by
  ext x; simp [setOfList]

private theorem setOfList_four (a b c d : V3) : setOfList [a, b, c, d] = {a, b, c, d} := by
  ext x; simp [setOfList]

-- DISCHARGES: PackingAuto2.EMNWUUS1_concl

/-- HOL `EMNWUUS1` (EMNWUUS.hl:56): `mcell4` is nonempty exactly when the
tetrahedron has circumradius below `sqrt 2`. -/
theorem EMNWUUS1 (V : Set V3) (ul : List V3) (_hs : saturated V) (_hP : Packing V)
    (_hbar : barV V 3 ul) : hl ul < Real.sqrt 2 ↔ mcell4 V ul ≠ ∅ := by
  unfold mcell4
  by_cases hlt : hl ul < Real.sqrt 2
  · rw [if_pos hlt]
    refine iff_of_true hlt ?_
    have hmem : hdV ul ∈ setOfList ul := BARV_IMP_HD_IN_SET_OF_LIST V 3 ul _hbar
    intro hcon
    have h2 : hdV ul ∈ (∅ : Set V3) := by
      rw [← hcon]
      exact subset_convexHull ℝ _ hmem
    exact Set.notMem_empty _ h2
  · rw [if_neg hlt]
    refine iff_of_false (fun hc => hlt hc) ?_
    intro h
    exact h rfl

-- DISCHARGES: PackingAuto2.EMNWUUS2_concl

/-- HOL `EMNWUUS2` (EMNWUUS.hl:81): a `barV V 3` simplex has circumradius
below `sqrt 2` iff all four inner Marchal cells (`mcell0`..`mcell3`) are
empty. -/
theorem EMNWUUS2 (V : Set V3) (ul : List V3) (hs : saturated V) (hP : Packing V)
    (hbar : barV V 3 ul) :
    hl ul < Real.sqrt 2 ↔
      mcell0 V ul = ∅ ∧ mcell1 V ul = ∅ ∧ mcell2 V ul = ∅ ∧ mcell3 V ul = ∅ := by
  obtain ⟨u0, u1, u2, u3, hul4⟩ := BARV_3_EXPLICIT V ul hbar
  rw [hul4] at hbar ⊢
  have hrad : ∀ S : Set V3, ¬ affineDependent S → ∀ w ∈ S, radV S = dist (circumcenter S) w :=
    OAPVION2
  constructor
  · -- Forward: every hull point is within hl ul < sqrt 2 of u0, so mcell0 is
    -- empty; mcell1..3 are empty because their guards need sqrt 2 <= hl ul.
    intro hlt
    have hbarind : ¬ affineDependent ({u0, u1, u2, u3} : Set V3) := by
      have h := BARV_AFFINE_INDEPENDENT V [u0, u1, u2, u3] 3 hP hbar
      rwa [setOfList_four] at h
    have hltR : radV {u0, u1, u2, u3} < Real.sqrt 2 := by
      simpa only [hl, setOfList_four] using hlt
    have d0 : dist (hdV [u0, u1, u2, u3]) (omegaListN V [u0, u1, u2, u3] 0) < Real.sqrt 2 := by
      rw [show omegaListN V [u0, u1, u2, u3] 0 = hdV [u0, u1, u2, u3] from rfl, dist_self]
      exact Real.sqrt_pos.mpr (by norm_num)
    have hchain1 := XNHPWAB4 V [u0, u1, u2, u3] 3 hP hbar hlt 1 3 (by omega) (by omega)
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2,
      TRUNCATE_SIMPLEX_REFL 3 [u0, u1, u2, u3] hbar.1] at hchain1
    simp only [hl, setOfList_pair, setOfList_four] at hchain1
    have hsub1 : ({u0, u1} : Set V3) ⊆ {u0, u1, u2, u3} := by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto
    have d1 : dist (hdV [u0, u1, u2, u3]) (omegaListN V [u0, u1, u2, u3] 1) < Real.sqrt 2 := by
      rw [OMEGA_LIST_1_EXPLICIT u0 u1 u2 u3 V [u0, u1, u2, u3] hs hP hbar hlt rfl,
        show hdV [u0, u1, u2, u3] = u0 from rfl,
        dist_comm u0 (circumcenter {u0, u1}),
        ← hrad {u0, u1} (not_affineDependent_subset hsub1 hbarind) u0 (by simp)]
      exact hchain1.trans hltR
    have hchain2 := XNHPWAB4 V [u0, u1, u2, u3] 3 hP hbar hlt 2 3 (by omega) (by omega)
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2,
      TRUNCATE_SIMPLEX_REFL 3 [u0, u1, u2, u3] hbar.1] at hchain2
    simp only [hl, setOfList_three, setOfList_four] at hchain2
    have hsub2 : ({u0, u1, u2} : Set V3) ⊆ {u0, u1, u2, u3} := by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto
    have d2 : dist (hdV [u0, u1, u2, u3]) (omegaListN V [u0, u1, u2, u3] 2) < Real.sqrt 2 := by
      rw [OMEGA_LIST_2_EXPLICIT u0 u1 u2 u3 V [u0, u1, u2, u3] hs hP hbar hlt rfl,
        show hdV [u0, u1, u2, u3] = u0 from rfl,
        dist_comm u0 (circumcenter {u0, u1, u2}),
        ← hrad {u0, u1, u2} (not_affineDependent_subset hsub2 hbarind) u0 (by simp)]
      exact hchain2.trans hltR
    have d3 : dist (hdV [u0, u1, u2, u3]) (omegaListN V [u0, u1, u2, u3] 3) < Real.sqrt 2 := by
      rw [OMEGA_LIST_3_EXPLICIT u0 u1 u2 u3 V [u0, u1, u2, u3] hs hP hbar hlt rfl,
        show hdV [u0, u1, u2, u3] = u0 from rfl,
        dist_comm u0 (circumcenter {u0, u1, u2, u3}),
        ← hrad {u0, u1, u2, u3} hbarind u0 (by simp)]
      exact hltR
    have hkey : ∀ y ∈ omegaListN V [u0, u1, u2, u3] '' {j : ℕ | j < [u0, u1, u2, u3].length},
        dist (hdV [u0, u1, u2, u3]) y < Real.sqrt 2 := by
      rintro y ⟨i, hi, rfl⟩
      have hi4 : i < 4 := hi
      interval_cases i
      · exact d0
      · exact d1
      · exact d2
      · exact d3
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold mcell0 rogers
      rw [Set.sdiff_eq_empty]
      intro p hp
      refine Metric.mem_ball.2 ?_
      rw [dist_comm]
      exact BALL_CONVEX_HULL_LEMMA _ _ _ _ hkey hp
    · unfold mcell1
      rw [if_neg (show ¬(Real.sqrt 2 ≤ hl [u0, u1, u2, u3]) from not_le.2 hlt)]
    · unfold mcell2
      rw [if_neg (show ¬(hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [u0, u1, u2, u3]) from fun hc => not_le.2 hlt hc.2)]
    · unfold mcell3
      rw [if_neg (show ¬(hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2 ∧
        Real.sqrt 2 ≤ hl [u0, u1, u2, u3]) from fun hc => not_le.2 hlt hc.2)]
  · -- Backward: for sqrt 2 <= hl ul the omega point lies in mcell0.
    intro hcells
    obtain ⟨h0, h1, h2, h3⟩ := hcells
    by_contra hc
    push Not at hc
    have hmem : omegaList V [u0, u1, u2, u3] ∈ mcell0 V [u0, u1, u2, u3] := by
      unfold mcell0 rogers
      refine ⟨subset_convexHull ℝ _ (Set.mem_image_of_mem _ (by simp)), ?_⟩
      intro hball
      rw [Metric.mem_ball] at hball
      have hw := WAUFCHE1 V [u0, u1, u2, u3] 3 hP hbar
      linarith
    rw [h0] at hmem
    exact Set.notMem_empty _ hmem

/-! ## NJIUTIU (NJIUTIU.hl) -/

-- DISCHARGES: (NJIUTIU.hl:38 supporting lemma; no pack_concl interface)

/-- HOL `CLOSEST_POINT_SUBSET_lemma` (NJIUTIU.hl:38): if the closest point of
`S` from `x` already lies in the closed convex subset `P` of `S`, then it is
also the closest point of `P`.

PROOF STATUS: skeleton. The `closestPoint` epsilon only unfolds to
`(y IN P /\ !z. z IN P ==> dist(x,y) <= dist(x,z))`; equating the two
projections needs uniqueness of the metric projection, i.e. HOL
`CLOSEST_POINT_LT` (strict convexity of the squared norm on the convex
set `P`), whose Rogers/Multivariate machinery is not yet ported. -/
theorem CLOSEST_POINT_SUBSET_lemma (a x : V3) (S P : Set V3)
    (_ha : a = closestPoint S x) (_haP : a ∈ P) (_hsub : P ⊆ S)
    (_hc : Convex ℝ P) (_hPc : IsClosed P) (_hSc : IsClosed S) (_hne : P ≠ ∅) :
    a = closestPoint P x := by
  sorry

-- DISCHARGES: (NJIUTIU.hl:64 supporting lemma; no pack_concl interface)

/-- HOL `AFF_DEPENDENT_AFF_DIM_4` (NJIUTIU.hl:64): an affinely dependent
4-point set spans dimension at most 2.

PROOF STATUS: skeleton. HL splits on which of `a b c d` is the dependent
point and applies `AFF_DIM_INSERT` + `AFF_DIM_LE_CARD`; the Mathlib-side
exchange (`AffineIndependent` family on `↥S` vs `vectorSpan` finrank, i.e.
`affDim (insert x s) = affDim s` when `x ∈ affineSpan s`) is not yet wired. -/
theorem AFF_DEPENDENT_AFF_DIM_4 (a b c d : V3) (h : affineDependent {a, b, c, d}) :
    affDim {a, b, c, d} ≤ 2 := by
  sorry

-- DISCHARGES: (NJIUTIU.hl:149; concl NJIUTIU.hl:27-33 — no pack_concl interface)

/-- HOL `NJIUTIU` (NJIUTIU.hl:149): two `barV V 3` lists whose Rogers
simplices coincide and are full-dimensional have identical omega chains.

PROOF STATUS: skeleton, following the HL refinement script. `ROGERS_AFF_DIM_FULL`
forces the four omega points of `ul` (and of `vl`) pairwise distinct;
`ROGERS_EXPLICIT` rewrites `rogers V ul` as the hull of
`{HD ul, ω1, ω2, ω3}`, and `AFF_DEPENDENT_AFF_DIM_4` with the shared
3-dimensional hull yields `HD ul = HD vl` (HL: `CONVEX_HULL_EQ_EQ_SET_EQ`,
not yet ported). Each `ω_{i+1}` is then recovered as the closest point of
the convex hull of the Voronoi face `voronoi_list V (truncate_simplex (i+1) ul)`
via `CLOSEST_POINT_SUBSET_lemma`, `CONVEX_VORONOI_LIST` and
`CLOSED_VORONOI_LIST` — determined by the shared hull `W`. -/
theorem NJIUTIU (V : Set V3) (ul vl : List V3) (hs : saturated V) (hP : Packing V)
    (hul : barV V 3 ul) (hvl : barV V 3 vl) (hrogers : rogers V ul = rogers V vl)
    (hdim : affDim (rogers V ul) = 3) :
    ∀ i : ℕ, i ≤ 3 → omegaListN V ul i = omegaListN V vl i := by
  obtain ⟨u0, u1, u2, u3, hul4⟩ := BARV_3_EXPLICIT V ul hul
  obtain ⟨v0, v1, v2, v3, hvl4⟩ := BARV_3_EXPLICIT V vl hvl
  -- the four omega points of each list are pairwise distinct (HL:200-253)
  have hdist := ROGERS_AFF_DIM_FULL V ul hul hdim
  have hdimv : affDim (rogers V vl) = 3 := by rw [← hrogers]; exact hdim
  have hdistv := ROGERS_AFF_DIM_FULL V vl hvl hdimv
  -- NJIUTIU core (HL:278-577): closest-point descent through the shared hull.
  sorry

/-! ## TEZFFSK (TEZFFSK.hl) -/

-- DISCHARGES: (TEZFFSK.hl:38; concl TEZFFSK.hl:31-36 — no pack_concl interface)

/-- HOL `TEZFFSK` (TEZFFSK.hl:38): two `barV V 3` lists with the same
full-dimensional Rogers simplex share every truncation whose circumradius
drops below `sqrt 2`. -/
theorem TEZFFSK (V : Set V3) (ul vl : List V3) (k : ℕ) (hs : saturated V)
    (hP : Packing V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (hrogers : rogers V ul = rogers V vl) (hdim : affDim (rogers V ul) = 3)
    (hk : k ≤ 3) (hlt : hl (truncateSimplex k ul) < Real.sqrt 2) :
    truncateSimplex k ul = truncateSimplex k vl := by
  obtain ⟨u0, u1, u2, u3, hul4⟩ := BARV_3_EXPLICIT V ul hul
  obtain ⟨v0, v1, v2, v3, hvl4⟩ := BARV_3_EXPLICIT V vl hvl
  -- the omega chains agree (HL:87-96, via NJIUTIU)
  have homega : ∀ i : ℕ, i ≤ 3 → omegaListN V ul i = omegaListN V vl i :=
    NJIUTIU V ul vl hs hP hul hvl hrogers hdim
  -- the sqrt 2-smallness propagates to all truncations below k (HL:52-68,160-175)
  have hmono : ∀ i : ℕ, i ≤ k → hl (truncateSimplex i ul) < Real.sqrt 2 := by
    intro i hik
    have h1 : truncateSimplex i (truncateSimplex k ul) = truncateSimplex i ul :=
      TRUNCATE_TRUNCATE_SIMPLEX ul i k hik (by have := hul.1; omega)
    have hb : barV V k (truncateSimplex k ul) :=
      TRUNCATE_SIMPLEX_BARV V k 3 ul hul (by omega)
    have h3 := HL_DECREASE V (truncateSimplex k ul) k i hP hb (by omega)
    rw [h1] at h3
    linarith
  -- TEZFFSK core (HL:120-581): NJIUTIU + WAUFCHE2 + XYOFCGX force u_i = v_i.
  sorry

end Kepler.Text
