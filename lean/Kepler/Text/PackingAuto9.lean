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
- `CLOSEST_POINT_SUBSET_lemma`, `AFF_DEPENDENT_AFF_DIM_4` (NJIUTIU supports):
  FULLY PROVED (no `sorry`). The former by metric-projection existence on the
  closed set (compactness) plus uniqueness on the convex subset via the
  strict-convexity midpoint argument (`norm_midpoint_lt_iff`); the latter via
  Mathlib's `finrank_vectorSpan_le_iff_not_affineIndependent` bridge on the
  coerced 4-point family (card ≤ 4 splits).
- `NJIUTIU`, `TEZFFSK`: stated faithfully, the tractable reductions
  discharged (omega points pairwise distinct via `ROGERS_AFF_DIM_FULL`;
  TEZFFSK's `hl`-monotone propagation via `HL_DECREASE`) and the geometric
  cores `sorry`'d (see the per-theorem NEEDS notes).

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

FULLY PROVED. The selected `closestPoint` only carries its defining
property when the target predicate is satisfiable; closedness of `S`
(compactness argument, as in the Rogers ports) provides a genuine minimizer
`y`, so `ε` lands on `a` and `a` minimizes over `S`. Then `a` and
`closestPoint P x` both minimize over the convex set `P`; were they distinct,
the midpoint would sit strictly closer by strict convexity of the norm
(`norm_midpoint_lt_iff`, via the inner-product `UniformConvexSpace`
instance) — contradiction. -/
theorem CLOSEST_POINT_SUBSET_lemma (a x : V3) (S P : Set V3)
    (_ha : a = closestPoint S x) (_haP : a ∈ P) (_hsub : P ⊆ S)
    (_hc : Convex ℝ P) (_hPc : IsClosed P) (_hSc : IsClosed S) (_hne : P ≠ ∅) :
    a = closestPoint P x := by
  have hSne : S.Nonempty := ⟨a, _hsub _haP⟩
  obtain ⟨y, hy, hmin⟩ : ∃ y ∈ S, ∀ z ∈ S, dist x y ≤ dist x z := by
    obtain ⟨s0, hs0⟩ := hSne
    have hcomp : IsCompact (S ∩ Metric.closedBall x (dist s0 x)) :=
      IsCompact.inter_left (isCompact_closedBall x (dist s0 x)) _hSc
    have hne2 : (S ∩ Metric.closedBall x (dist s0 x)).Nonempty :=
      ⟨s0, hs0, Metric.mem_closedBall.2 le_rfl⟩
    obtain ⟨y, hy, hmin⟩ := hcomp.exists_isMinOn hne2
      (Continuous.continuousOn (Continuous.dist continuous_const continuous_id))
    simp only [IsMinOn, IsMinFilter, Filter.eventually_principal] at hmin
    refine ⟨y, hy.1, fun z hz => ?_⟩
    by_cases hz' : z ∈ Metric.closedBall x (dist s0 x)
    · exact hmin z ⟨hz, hz'⟩
    · have hy' : dist x y ≤ dist x s0 := by
        simpa using hmin s0 ⟨hs0, Metric.mem_closedBall.2 le_rfl⟩
      rw [Metric.mem_closedBall, not_le, dist_comm s0 x, dist_comm z x] at hz'
      exact hy'.trans (le_of_lt hz')
  have h' : closestPoint S x ∈ S ∧ ∀ z ∈ S, dist x (closestPoint S x) ≤ dist x z :=
    Classical.epsilon_spec (p := fun y : V3 => y ∈ S ∧ ∀ z ∈ S, dist x y ≤ dist x z)
      ⟨y, hy, hmin⟩
  rw [← _ha] at h'
  have hq : a ∈ P ∧ ∀ z ∈ P, dist x a ≤ dist x z :=
    ⟨_haP, fun z hz => h'.2 z (_hsub hz)⟩
  have hcspec : closestPoint P x ∈ P ∧ ∀ z ∈ P, dist x (closestPoint P x) ≤ dist x z :=
    Classical.epsilon_spec (p := fun y : V3 => y ∈ P ∧ ∀ z ∈ P, dist x y ≤ dist x z) ⟨a, hq⟩
  by_contra hne'
  have hab : dist x a = dist x (closestPoint P x) :=
    le_antisymm (hq.2 _ hcspec.1) (hcspec.2 a _haP)
  rw [dist_eq_norm, dist_eq_norm] at hab
  have hmid : midpoint ℝ a (closestPoint P x) ∈ P := Convex.midpoint_mem _hc _haP hcspec.1
  have hkey : dist x a ≤ dist x (midpoint ℝ a (closestPoint P x)) := hq.2 _ hmid
  rw [dist_eq_norm, dist_eq_norm] at hkey
  have hhalf : (⅟2 : ℝ) = 1 / 2 := by norm_num
  have hsplit : x - midpoint ℝ a (closestPoint P x)
      = (1 / 2 : ℝ) • ((x - a) + (x - closestPoint P x)) := by
    show (x : V3) -ᵥ midpoint ℝ a (closestPoint P x)
        = (1 / 2 : ℝ) • ((x : V3) -ᵥ a + ((x : V3) -ᵥ closestPoint P x))
    rw [vsub_midpoint, ← smul_add, ← hhalf]
  have hstrict : dist x (midpoint ℝ a (closestPoint P x)) < dist x a := by
    rw [dist_eq_norm, dist_eq_norm, hsplit, norm_midpoint_lt_iff hab]
    exact fun hcon => hne' (sub_right_injective (b := x) hcon)
  exact absurd hstrict (not_lt.2 hkey)

-- DISCHARGES: (NJIUTIU.hl:64 supporting lemma; no pack_concl interface)

/-- HOL `AFF_DEPENDENT_AFF_DIM_4` (NJIUTIU.hl:64): an affinely dependent
4-point set spans dimension at most 2.

FULLY PROVED. The coerced family `fun x : ↥{a,b,c,d} => (x : V3)` has
`Fintype.card` between 1 and 4. For card ≤ 2 (resp. = 3),
`finrank_vectorSpan_range_le` alone bounds the dimension by 1 (resp. 2); for
card = 4 Mathlib's `finrank_vectorSpan_le_iff_not_affineIndependent` (n = 2)
converts the affine dependence into the dimension bound directly. -/
theorem AFF_DEPENDENT_AFF_DIM_4 (a b c d : V3) (h : affineDependent {a, b, c, d}) :
    affDim {a, b, c, d} ≤ 2 := by
  have hne : ({a, b, c, d} : Set V3).Nonempty := ⟨a, by simp⟩
  rw [affDim, if_neg (nonempty_iff_ne_empty.1 hne)]
  haveI : Finite ({a, b, c, d} : Set V3) := Set.toFinite _ |>.to_subtype
  haveI hfintype : Fintype ({a, b, c, d} : Set V3) := Fintype.ofFinite _
  haveI hcpos : 0 < Fintype.card ({a, b, c, d} : Set V3) := Fintype.card_pos
  have hc4 : Fintype.card ({a, b, c, d} : Set V3) ≤ 4 := by
    rw [Set.fintypeCard_eq_ncard]
    have hle1 := Set.ncard_insert_le a (insert b (insert c {d} : Set V3))
    have hle2 := Set.ncard_insert_le b (insert c {d} : Set V3)
    have hle3 := Set.ncard_insert_le c ({d} : Set V3)
    have h1 := Set.ncard_singleton (α := V3) d
    omega
  have hrange : Set.range (fun x : ({a, b, c, d} : Set V3) => (x : V3)) = {a, b, c, d} := by
    ext y
    constructor
    · rintro ⟨⟨z, hz⟩, rfl⟩
      exact hz
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨⟨y, by simp⟩, rfl⟩
      · exact ⟨⟨y, by simp⟩, rfl⟩
      · exact ⟨⟨y, by simp⟩, rfl⟩
      · exact ⟨⟨y, by simp⟩, rfl⟩
  by_cases hc2 : Fintype.card ({a, b, c, d} : Set V3) ≤ 2
  · have hle := finrank_vectorSpan_range_le (k := ℝ) (V := V3) (P := V3)
      (fun x : ({a, b, c, d} : Set V3) => (x : V3))
      (n := Fintype.card ({a, b, c, d} : Set V3) - 1) (by omega)
    rw [hrange] at hle
    omega
  · by_cases hc3 : Fintype.card ({a, b, c, d} : Set V3) = 3
    · have hle := finrank_vectorSpan_range_le (k := ℝ) (V := V3) (P := V3)
        (fun x : ({a, b, c, d} : Set V3) => (x : V3)) (n := 2) hc3
      rw [hrange] at hle
      exact_mod_cast hle
    · have hc3' : Fintype.card ({a, b, c, d} : Set V3) = 4 := by omega
      have hkey := finrank_vectorSpan_le_iff_not_affineIndependent
        (k := ℝ) (V := V3) (P := V3) (fun x : ({a, b, c, d} : Set V3) => (x : V3)) (n := 2) hc3'
      have hnot : ¬ AffineIndependent ℝ (fun x : ({a, b, c, d} : Set V3) => (x : V3)) := h
      rw [hrange] at hkey
      exact_mod_cast (hkey.2 hnot)

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
-- NEEDS: NJIUTIU geometric core (HL:278-577). Remaining: port the HL
-- `CONVEX_HULL_EQ_EQ_SET_EQ` step (two 4-point sets with equal convex hulls
-- and equal affDim 3 have equal vertex sets, forcing `hdV ul = hdV vl`), then
-- the closest-point descent recovering each `ω_{i+1}` as the projection of
-- `ω_i` onto the shared Voronoi face via `CLOSEST_POINT_SUBSET_lemma` +
-- `CONVEX_VORONOI_LIST` + `CLOSED_VORONOI_LIST` (PA6/PA12/PA14 ports).
-- Independently: the file's own NJIUTIU supports above are proved, and the
-- downstream pack_concl consumers do not depend on NJIUTIU/TEZFFSK bodies.

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
-- NEEDS: TEZFFSK geometric core (HL:120-581). Assuming the omega-chain
-- agreement (`NJIUTIU` above), remains: combine `WAUFCHE2`/`XYOFCGX`-style
-- uniqueness ports to force each vertex `u_i = v_i` of the truncation. The
-- reductions inside the proof (chain agreement via NJIUTIU; monotone
-- sqrt-2-smallness of truncations via `HL_DECREASE` + `TRUNCATE_TRUNCATE_
-- SIMPLEX`) are fully discharged; only the final vertex-identification
-- `sorry` remains. Depends on the NJIUTIU NEEDS above at merge time.

end Kepler.Text
