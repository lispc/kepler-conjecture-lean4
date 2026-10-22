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

private theorem p9_rogers_explicit (V : Set V3) (ul : List V3) (hb : barV V 3 ul) :
    rogers V ul = convexHull ℝ {hdV ul, omegaListN V ul 1, omegaListN V ul 2,
      omegaListN V ul 3} := by
  have h4 : ul.length = 4 := by rw [hb.1]
  have hset : omegaListN V ul '' {j : ℕ | j < ul.length}
      = {hdV ul, omegaListN V ul 1, omegaListN V ul 2, omegaListN V ul 3} := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [h4] at hj
      interval_cases j
      · simp [hdV, omegaListN]
      · simp
      · simp
      · simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, by omega, rfl⟩
      · exact ⟨2, by omega, rfl⟩
      · exact ⟨3, by omega, rfl⟩
  rw [rogers, hset]

private theorem p9_affDim_convexHull (s : Set V3) : affDim (convexHull ℝ s) = affDim s := by
  by_cases hs : s = ∅
  · rw [hs, convexHull_empty, affDim_empty]
  · have hne : (convexHull ℝ s).Nonempty := Set.Nonempty.convexHull (Set.nonempty_iff_ne_empty.2 hs)
    rw [affDim, if_neg (Set.nonempty_iff_ne_empty.1 hne), affDim, if_neg hs]
    rw [← direction_affineSpan (k := ℝ) (s := convexHull ℝ s),
      affineSpan_convexHull, direction_affineSpan (k := ℝ) (s := s)]

private theorem p9_rogers_aff_ind (V : Set V3) (ul : List V3) (hb : barV V 3 ul)
    (hdim : affDim (rogers V ul) = 3) :
    ¬ affineDependent ({hdV ul, omegaListN V ul 1, omegaListN V ul 2,
      omegaListN V ul 3} : Set V3) := by
  intro hdep
  have hle := AFF_DEPENDENT_AFF_DIM_4 (hdV ul) (omegaListN V ul 1)
    (omegaListN V ul 2) (omegaListN V ul 3) hdep
  have h1 : affDim (rogers V ul)
      = affDim ({hdV ul, omegaListN V ul 1, omegaListN V ul 2,
          omegaListN V ul 3} : Set V3) := by
    rw [p9_rogers_explicit V ul hb, p9_affDim_convexHull]
  omega

private theorem p9_barv_imp_u0_in_V (V : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) (hul : ul = [u0, u1, u2, u3]) :
    u0 ∈ V := by
  have hv : voronoiNondg V ul :=
    hb.2 ul ⟨⟨[], by rw [List.append_nil]⟩, by rw [hul]; exact Nat.succ_pos 3⟩
  have hsub : setOfList ul ⊆ V := hv.2.1
  have hmem : u0 ∈ setOfList ul := by rw [hul]; simp [setOfList]
  exact hsub hmem

private theorem p9_rogersInV_of_gltvhum (V : Set V3) (ul : List V3) (v : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hv : v ∈ V) (hr : rogers V ul v) : v = hdV ul := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  have hu0 : u0 ∈ V := p9_barv_imp_u0_in_V V ul u0 u1 u2 u3 hs hp hb hul
  have htr : truncateSimplex 0 ul = [u0] := by
    rw [hul]; exact (TRUNCATE_SIMPLEX_EXPLICIT_0 u0 u1 u2 u3).2.2.2
  have hgl := (GLTVHUM_concl V u0 v ⟨hp, hs⟩ hu0).2 ⟨ul, hb, hr, htr⟩
  have hle : dist v u0 ≤ dist v v := hgl v hv
  rw [dist_self] at hle
  have hdist : dist v u0 = 0 := le_antisymm hle dist_nonneg
  have hveq : v = u0 := dist_eq_zero.mp hdist
  rw [hveq, hul]
  rfl

private theorem p9_vertex_set_eq (V : Set V3) (ul vl : List V3) (hs : saturated V)
    (hP : Packing V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (hrogers : rogers V ul = rogers V vl) (hdim : affDim (rogers V ul) = 3) :
    ({hdV ul, omegaListN V ul 1, omegaListN V ul 2, omegaListN V ul 3} : Set V3) =
    ({hdV vl, omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3} : Set V3) := by
  have hdimv : affDim (rogers V vl) = 3 := by rw [← hrogers]; exact hdim
  have hnd_u := p9_rogers_aff_ind V ul hul hdim
  have hnd_v := p9_rogers_aff_ind V vl hvl hdimv
  refine (CONVEX_HULL_EQ_EQ_SET_EQ _ _ hnd_u hnd_v).1 ?_
  rw [← p9_rogers_explicit V ul hul, ← p9_rogers_explicit V vl hvl]
  exact hrogers

private theorem p9_hd_eq (V : Set V3) (ul vl : List V3) (hs : saturated V) (hP : Packing V)
    (hul : barV V 3 ul) (hvl : barV V 3 vl) (hrogers : rogers V ul = rogers V vl) :
    hdV ul = hdV vl := by
  have hmem : hdV ul ∈ rogers V ul := by
    rw [p9_rogers_explicit V ul hul]
    exact subset_convexHull ℝ _ (by simp [hdV, omegaListN])
  have hmem' : hdV ul ∈ rogers V vl := by rw [← hrogers]; exact hmem
  have hV : hdV ul ∈ V :=
    BARV_SUBSET V 3 ul hul (HD_IN_SET_OF_LIST ul (by rw [hul.1]; norm_num))
  exact p9_rogersInV_of_gltvhum V vl (hdV ul) hs hP hvl hV hmem'

private theorem p9_voronoiList_truncate_mono (V : Set V3) (ul : List V3) (i j : ℕ)
    (hij : i ≤ j) (hlen : j + 1 ≤ ul.length) :
    voronoiList V (truncateSimplex j ul) ⊆ voronoiList V (truncateSimplex i ul) := by
  have hiniti : initialSublist (truncateSimplex i ul) (truncateSimplex j ul) := by
    have htt := TRUNCATE_TRUNCATE_SIMPLEX ul i j hij hlen
    have hlenj : i + 1 ≤ (truncateSimplex j ul).length := by
      rw [LENGTH_TRUNCATE_SIMPLEX j ul hlen]; omega
    have h := ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST i
      (truncateSimplex i (truncateSimplex j ul)) (truncateSimplex j ul)).1
      ⟨rfl, hlenj⟩).1
    rwa [htt] at h
  have hsub : setOfList (truncateSimplex i ul) ⊆ setOfList (truncateSimplex j ul) :=
    SET_OF_LIST_INITIAL_SUBLIST_SUBSET hiniti
  intro x hx
  rw [voronoiList, voronoiSet] at hx ⊢
  intro t ht
  obtain ⟨w, hw, rfl⟩ := ht
  exact hx _ ⟨w, hsub hw, rfl⟩


private theorem p9_omega_descent_step (V : Set V3) (ul vl : List V3) (hs : saturated V)
    (hP : Packing V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (hW : ({hdV ul, omegaListN V ul 1, omegaListN V ul 2, omegaListN V ul 3} : Set V3) =
           {hdV vl, omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3})
    (hdimu : affDim (rogers V ul) = 3) (hdimv : affDim (rogers V vl) = 3)
    (i : ℕ) (hi : i < 3)
    (hpre : ∀ j, j ≤ i → omegaListN V ul j = omegaListN V vl j) :
    omegaListN V ul (i + 1) = omegaListN V vl (i + 1) := by
  have hdistu := ROGERS_AFF_DIM_FULL V ul hul hdimu
  have hdistv := ROGERS_AFF_DIM_FULL V vl hvl hdimv
  have hul4 : ul.length = 4 := by rw [hul.1]
  have hvl4 : vl.length = 4 := by rw [hvl.1]
  set W : Set V3 := {hdV ul, omegaListN V ul 1, omegaListN V ul 2, omegaListN V ul 3} with hWdefu
  have hWdefv : W = {hdV vl, omegaListN V vl 1, omegaListN V vl 2, omegaListN V vl 3} := hW
  have himg : (omegaListN V ul '' Set.Iio (i + 1)) = (omegaListN V vl '' Set.Iio (i + 1)) := by
    ext y
    constructor
    · rintro ⟨j, hj, hjy⟩
      have hj' : j < i + 1 := hj
      exact ⟨j, hj, (hpre j (by omega)).symm.trans hjy⟩
    · rintro ⟨j, hj, hjy⟩
      have hj' : j < i + 1 := hj
      exact ⟨j, hj, (hpre j (by omega)).trans hjy⟩
  have hWfin : W.Finite := by
    rw [hWdefu]
    exact (((Set.finite_singleton (omegaListN V ul 3)).insert (omegaListN V ul 2)).insert
      (omegaListN V ul 1)).insert (hdV ul)
  have hmemW_u : ∀ k ≤ 3, omegaListN V ul k ∈ W := by
    intro k hk
    rw [hWdefu]
    interval_cases k <;> simp [omegaListN]
  have hmemW_v : ∀ k ≤ 3, omegaListN V vl k ∈ W := by
    intro k hk
    rw [hWdefv]
    interval_cases k <;> simp [omegaListN]
  have hcell_u : ∀ k, i + 1 ≤ k → k ≤ 3 →
      omegaListN V ul k ∈ voronoiList V (truncateSimplex (i + 1) ul) := by
    intro k hk hk3
    exact p9_voronoiList_truncate_mono V ul (i + 1) k hk (by rw [hul4]; omega)
      (OMEGA_LIST_N_IN_VORONOI_LIST V ul 3 k hul hk3)
  have hcell_v : ∀ k, i + 1 ≤ k → k ≤ 3 →
      omegaListN V vl k ∈ voronoiList V (truncateSimplex (i + 1) vl) := by
    intro k hk hk3
    exact p9_voronoiList_truncate_mono V vl (i + 1) k hk (by rw [hvl4]; omega)
      (OMEGA_LIST_N_IN_VORONOI_LIST V vl 3 k hvl hk3)
  have hmemPu : omegaListN V ul (i + 1) ∈
      convexHull ℝ (W \ (omegaListN V ul '' Set.Iio (i + 1))) := by
    refine subset_convexHull ℝ _ ⟨hmemW_u (i + 1) (by omega), ?_⟩
    rintro ⟨j, hj, hjy⟩
    have hj' : j < i + 1 := hj
    exact hdistu (i + 1) j (by omega) (by omega) (by omega) hjy.symm
  have hPu_sub : convexHull ℝ (W \ (omegaListN V ul '' Set.Iio (i + 1))) ⊆
      voronoiList V (truncateSimplex (i + 1) ul) := by
    refine convexHull_min ?_ (CONVEX_VORONOI_LIST V _)
    rintro y ⟨hyW, hyn⟩
    rw [hWdefu] at hyW
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyW
    rcases hyW with h0 | h1 | h2 | h3
    · exfalso
      exact hyn ⟨0, Set.mem_Iio.2 (by omega), by rw [h0]; rfl⟩
    · subst h1
      have hk : i + 1 ≤ 1 := by
        by_contra hcon
        exact hyn ⟨1, Set.mem_Iio.2 (by omega), rfl⟩
      exact hcell_u 1 hk (by norm_num)
    · subst h2
      have hk : i + 1 ≤ 2 := by
        by_contra hcon
        exact hyn ⟨2, Set.mem_Iio.2 (by omega), rfl⟩
      exact hcell_u 2 hk (by norm_num)
    · subst h3
      have hk : i + 1 ≤ 3 := by
        by_contra hcon
        exact hyn ⟨3, Set.mem_Iio.2 (by omega), rfl⟩
      exact hcell_u 3 hk (by norm_num)
  have hPu_closed : IsClosed (convexHull ℝ (W \ (omegaListN V ul '' Set.Iio (i + 1)))) :=
    Set.Finite.isClosed_convexHull ℝ (hWfin.sdiff)
  have hPu_ne : convexHull ℝ (W \ (omegaListN V ul '' Set.Iio (i + 1))) ≠ ∅ := by
    intro h
    rw [h] at hmemPu
    exact hmemPu
  have hstep_u : omegaListN V ul (i + 1)
      = closestPoint (convexHull ℝ (W \ (omegaListN V ul '' Set.Iio (i + 1))))
          (omegaListN V ul i) :=
    CLOSEST_POINT_SUBSET_lemma (a := omegaListN V ul (i + 1)) (x := omegaListN V ul i)
      (S := voronoiList V (truncateSimplex (i + 1) ul))
      (P := convexHull ℝ (W \ (omegaListN V ul '' Set.Iio (i + 1))))
      rfl hmemPu hPu_sub (convex_convexHull ℝ _) hPu_closed (CLOSED_VORONOI_LIST V _) hPu_ne
  have hmemPv : omegaListN V vl (i + 1) ∈
      convexHull ℝ (W \ (omegaListN V vl '' Set.Iio (i + 1))) := by
    refine subset_convexHull ℝ _ ⟨hmemW_v (i + 1) (by omega), ?_⟩
    rintro ⟨j, hj, hjy⟩
    have hj' : j < i + 1 := hj
    exact hdistv (i + 1) j (by omega) (by omega) (by omega) hjy.symm
  have hPv_sub : convexHull ℝ (W \ (omegaListN V vl '' Set.Iio (i + 1))) ⊆
      voronoiList V (truncateSimplex (i + 1) vl) := by
    refine convexHull_min ?_ (CONVEX_VORONOI_LIST V _)
    rintro y ⟨hyW, hyn⟩
    rw [hWdefv] at hyW
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hyW
    rcases hyW with h0 | h1 | h2 | h3
    · exfalso
      exact hyn ⟨0, Set.mem_Iio.2 (by omega), by rw [h0]; rfl⟩
    · subst h1
      have hk : i + 1 ≤ 1 := by
        by_contra hcon
        exact hyn ⟨1, Set.mem_Iio.2 (by omega), rfl⟩
      exact hcell_v 1 hk (by norm_num)
    · subst h2
      have hk : i + 1 ≤ 2 := by
        by_contra hcon
        exact hyn ⟨2, Set.mem_Iio.2 (by omega), rfl⟩
      exact hcell_v 2 hk (by norm_num)
    · subst h3
      have hk : i + 1 ≤ 3 := by
        by_contra hcon
        exact hyn ⟨3, Set.mem_Iio.2 (by omega), rfl⟩
      exact hcell_v 3 hk (by norm_num)
  have hPv_closed : IsClosed (convexHull ℝ (W \ (omegaListN V vl '' Set.Iio (i + 1)))) :=
    Set.Finite.isClosed_convexHull ℝ (hWfin.sdiff)
  have hPv_ne : convexHull ℝ (W \ (omegaListN V vl '' Set.Iio (i + 1))) ≠ ∅ := by
    intro h
    rw [h] at hmemPv
    exact hmemPv
  have hstep_v : omegaListN V vl (i + 1)
      = closestPoint (convexHull ℝ (W \ (omegaListN V vl '' Set.Iio (i + 1))))
          (omegaListN V vl i) :=
    CLOSEST_POINT_SUBSET_lemma (a := omegaListN V vl (i + 1)) (x := omegaListN V vl i)
      (S := voronoiList V (truncateSimplex (i + 1) vl))
      (P := convexHull ℝ (W \ (omegaListN V vl '' Set.Iio (i + 1))))
      rfl hmemPv hPv_sub (convex_convexHull ℝ _) hPv_closed (CLOSED_VORONOI_LIST V _) hPv_ne
  calc omegaListN V ul (i + 1)
      = closestPoint (convexHull ℝ (W \ (omegaListN V ul '' Set.Iio (i + 1))))
          (omegaListN V ul i) := hstep_u
    _ = closestPoint (convexHull ℝ (W \ (omegaListN V vl '' Set.Iio (i + 1))))
          (omegaListN V vl i) := by rw [himg, hpre i le_rfl]
    _ = omegaListN V vl (i + 1) := hstep_v.symm

-- DISCHARGES: (NJIUTIU.hl:149; concl NJIUTIU.hl:27-33 — no pack_concl interface)

/-- HOL `NJIUTIU` (NJIUTIU.hl:149): two `barV V 3` lists whose Rogers
simplices coincide and are full-dimensional have identical omega chains.

FILLED (B6a, 2026-10-22). Route: the shared hull is the hull of both
4-point vertex sets `{HD, omega1, omega2, omega3}` (private `p9_rogers_explicit`),
both affinely independent since `affDim (rogers) = 3` and a dependent 4-set
has `affDim ≤ 2` (`AFF_DEPENDENT_AFF_DIM_4`); `CONVEX_HULL_EQ_EQ_SET_EQ`
(PA5, filled in this lane) gives the vertex-set equality `W`. `HD ul = HD vl`
follows from `p9_rogersInV_of_gltvhum` (the `GLTVHUM_concl` route: the Rogers
simplex of a `barV V 3` list lies in the closed Voronoi cell of its head).
The descent `p9_omega_descent_step` recovers each `omega_{i+1}` as the
closest point of `conv (W minus {omega_0..omega_i})` inside
`voronoiList V (truncateSimplex (i+1) ul)` via `CLOSEST_POINT_SUBSET_lemma`
+ `CONVEX_VORONOI_LIST`/`CLOSED_VORONOI_LIST`, determined by the shared `W`.
Note: PA9 cannot import PA12 (which imports PA9), so `ROGERS_EXPLICIT` and
`ROGERS_INTER_V_LEMMA` are re-derived here as private `p9_` helpers. -/
theorem NJIUTIU (V : Set V3) (ul vl : List V3) (hs : saturated V) (hP : Packing V)
    (hul : barV V 3 ul) (hvl : barV V 3 vl) (hrogers : rogers V ul = rogers V vl)
    (hdim : affDim (rogers V ul) = 3) :
    ∀ i : ℕ, i ≤ 3 → omegaListN V ul i = omegaListN V vl i := by
  have hdimv : affDim (rogers V vl) = 3 := by rw [← hrogers]; exact hdim
  have hW := p9_vertex_set_eq V ul vl hs hP hul hvl hrogers hdim
  have hd0 : omegaListN V ul 0 = omegaListN V vl 0 :=
    p9_hd_eq V ul vl hs hP hul hvl hrogers
  have h1 := p9_omega_descent_step V ul vl hs hP hul hvl hW hdim hdimv 0 (by norm_num)
    (fun j hj => by interval_cases j; exact hd0)
  have h2 := p9_omega_descent_step V ul vl hs hP hul hvl hW hdim hdimv 1 (by norm_num)
    (fun j hj => by interval_cases j; exact hd0; exact h1)
  have h3 := p9_omega_descent_step V ul vl hs hP hul hvl hW hdim hdimv 2 (by norm_num)
    (fun j hj => by interval_cases j; exact hd0; exact h1; exact h2)
  intro i hi
  interval_cases i
  · exact hd0
  · exact h1
  · exact h2
  · exact h3




/-! ## TEZFFSK kit -/


/-! ## TEZFFSK (TEZFFSK.hl) -/

-- DISCHARGES: (TEZFFSK.hl:38; concl TEZFFSK.hl:31-36 — no pack_concl interface)

private lemma p9_ncard2_ne {a b : V3} (h : ({a, b} : Set V3).ncard = 2) : a ≠ b := by
  intro hab
  have hsingle : ({a, b} : Set V3) = {a} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [hab]; tauto
  rw [hsingle, Set.ncard_singleton] at h
  omega

private lemma p9_ncard3_ne {a b c : V3} (h : ({a, b, c} : Set V3).ncard = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hle2 : ∀ x y : V3, ({x, y} : Set V3).ncard ≤ 2 := by
    intro x y
    have h2 := Set.ncard_insert_le x ({y} : Set V3)
    rw [Set.ncard_singleton] at h2
    simpa using h2
  have hab : a ≠ b := by
    intro hab
    have hsub : ({a, b, c} : Set V3) = ({b, c} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [hab]; tauto
    rw [hsub] at h
    have := hle2 b c
    omega
  have hac : a ≠ c := by
    intro hac
    have hsub : ({a, b, c} : Set V3) = ({a, b} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [hac]; tauto
    rw [hsub] at h
    have := hle2 a b
    omega
  have hbc : b ≠ c := by
    intro hbc
    have hsub : ({a, b, c} : Set V3) = ({a, b} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [hbc]; tauto
    rw [hsub] at h
    have := hle2 a b
    omega
  exact ⟨hab, hac, hbc⟩

private lemma p9_ncard4_ne {a b c d : V3} (h : ({a, b, c, d} : Set V3).ncard = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hle3 : ∀ x y z : V3, ({x, y, z} : Set V3).ncard ≤ 3 := by
    intro x y z
    have h2 := Set.ncard_insert_le x ({y, z} : Set V3)
    have h3 := Set.ncard_insert_le y ({z} : Set V3)
    rw [Set.ncard_singleton] at h3
    omega
  have hab : a ≠ b := by
    intro hab
    have hsub : ({a, b, c, d} : Set V3) = ({b, c, d} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [hab]; tauto
    rw [hsub] at h
    have := hle3 b c d
    omega
  have hac : a ≠ c := by
    intro hac
    have hsub : ({a, b, c, d} : Set V3) = ({a, b, d} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [hac]; tauto
    rw [hsub] at h
    have := hle3 a b d
    omega
  have had : a ≠ d := by
    intro had
    have hsub : ({a, b, c, d} : Set V3) = ({a, b, c} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [had]; tauto
    rw [hsub] at h
    have := hle3 a b c
    omega
  have hbc : b ≠ c := by
    intro hbc
    have hsub : ({a, b, c, d} : Set V3) = ({a, b, d} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [hbc]; tauto
    rw [hsub] at h
    have := hle3 a b d
    omega
  have hbd : b ≠ d := by
    intro hbd
    have hsub : ({a, b, c, d} : Set V3) = ({a, b, c} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [hbd]; tauto
    rw [hsub] at h
    have := hle3 a b c
    omega
  have hcd : c ≠ d := by
    intro hcd
    have hsub : ({a, b, c, d} : Set V3) = ({a, b, c} : Set V3) := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [hcd]; tauto
    rw [hsub] at h
    have := hle3 a b c
    omega
  exact ⟨hab, hac, had, hbc, hbd, hcd⟩

private theorem p9_omega1_circumcenter (V : Set V3) (u0 u1 u2 u3 : V3) (ul : List V3)
    (hs : saturated V) (hP : Packing V) (hb : barV V 3 ul) (hul : ul = [u0, u1, u2, u3])
    (hlt : hl (truncateSimplex 1 ul) < Real.sqrt 2) :
    omegaListN V ul 1 = circumcenter ({u0, u1} : Set V3) := by
  rw [hul] at hb hlt ⊢
  have hb1 : barV V 1 [u0, u1] := by
    simpa using BARV_INITIAL_SUBLIST V 3 [u0, u1, u2, u3] [u0, u1] hb
      (INITIAL_SUBLIST_APPEND [u0, u1] [u2, u3]) (by simp)
  have hsmall : hl [u0, u1] < Real.sqrt 2 := by
    simpa [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2] using hlt
  have hcen : omegaList V [u0, u1] = circumcenter (setOfList [u0, u1]) :=
    XNHPWAB1 V [u0, u1] 1 hP hb1 hsmall
  rw [OMEGA_LIST_TRUNCATE_1 V u0 u1 u2 u3, hcen]
  exact congrArg circumcenter (by ext x; simp [setOfList])

private theorem p9_omega2_circumcenter (V : Set V3) (u0 u1 u2 u3 : V3) (ul : List V3)
    (hs : saturated V) (hP : Packing V) (hb : barV V 3 ul) (hul : ul = [u0, u1, u2, u3])
    (hlt : hl (truncateSimplex 2 ul) < Real.sqrt 2) :
    omegaListN V ul 2 = circumcenter ({u0, u1, u2} : Set V3) := by
  rw [hul] at hb hlt ⊢
  have hb2 : barV V 2 [u0, u1, u2] := by
    simpa using BARV_INITIAL_SUBLIST V 3 [u0, u1, u2, u3] [u0, u1, u2] hb
      (INITIAL_SUBLIST_APPEND [u0, u1, u2] [u3]) (by simp)
  have hsmall : hl [u0, u1, u2] < Real.sqrt 2 := by
    simpa [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2] using hlt
  have hcen : omegaList V [u0, u1, u2] = circumcenter (setOfList [u0, u1, u2]) :=
    XNHPWAB1 V [u0, u1, u2] 2 hP hb2 hsmall
  rw [OMEGA_LIST_TRUNCATE_2 V u0 u1 u2 u3, hcen]
  exact congrArg circumcenter (by ext x; simp [setOfList])

/-- HOL `TEZFFSK` (TEZFFSK.hl:38): two `barV V 3` lists with the same
full-dimensional Rogers simplex share every truncation whose circumradius
drops below `sqrt 2`.

FILLED (B6b, 2026-10-22). `hl (truncateSimplex k vl) < sqrt 2` is transferred
from the `ul` side via `WAUFCHE1`/`WAUFCHE2` and the shared omega chain; the
smallness then propagates down (`HL_DECREASE` + `TRUNCATE_TRUNCATE_SIMPLEX`).
Each vertex `u_{i+1} = v_{i+1}` (for `i+1 ≤ k`) is forced by the strict
circumcenter gap `XYOFCGX` on `{u_0,...,u_i}` with the explicit circumcenter
formulas (`p9_omega1/2_circumcenter`, PA8 `OMEGA_LIST_3_EXPLICIT`); the `vl`
points are pairwise distinct (`BARV_IMP_LENGTH_EQ_CARD` + `Set.ncard_eq_*`
collapse lemmas). Case analysis on `k ≤ 3` finishes with the explicit
truncations. -/
theorem TEZFFSK (V : Set V3) (ul vl : List V3) (k : ℕ) (hs : saturated V)
    (hP : Packing V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (hrogers : rogers V ul = rogers V vl) (hdim : affDim (rogers V ul) = 3)
    (hk : k ≤ 3) (hlt : hl (truncateSimplex k ul) < Real.sqrt 2) :
    truncateSimplex k ul = truncateSimplex k vl := by
  obtain ⟨u0, u1, u2, u3, hul4⟩ := BARV_3_EXPLICIT V ul hul
  obtain ⟨v0, v1, v2, v3, hvl4⟩ := BARV_3_EXPLICIT V vl hvl
  subst hul4
  subst hvl4
  have homega : ∀ i : ℕ, i ≤ 3 → omegaListN V [u0, u1, u2, u3] i = omegaListN V [v0, v1, v2, v3] i :=
    NJIUTIU V [u0, u1, u2, u3] [v0, v1, v2, v3] hs hP hul hvl hrogers hdim
  have hd0 : omegaListN V [u0, u1, u2, u3] 0 = omegaListN V [v0, v1, v2, v3] 0 :=
    p9_hd_eq V [u0, u1, u2, u3] [v0, v1, v2, v3] hs hP hul hvl hrogers
  have hd0' : u0 = v0 := hd0
  -- smallness propagation ([u0, u1, u2, u3])
  have hmono : ∀ i : ℕ, i ≤ k → hl (truncateSimplex i [u0, u1, u2, u3]) < Real.sqrt 2 := by
    intro i hik
    have h1 : truncateSimplex i (truncateSimplex k [u0, u1, u2, u3]) = truncateSimplex i [u0, u1, u2, u3] :=
      TRUNCATE_TRUNCATE_SIMPLEX [u0, u1, u2, u3] i k hik (by rw [hul.1]; omega)
    have hb : barV V k (truncateSimplex k [u0, u1, u2, u3]) := TRUNCATE_SIMPLEX_BARV V k 3 [u0, u1, u2, u3] hul hk
    have h3 := HL_DECREASE V (truncateSimplex k [u0, u1, u2, u3]) k i hP hb hik
    rw [h1] at h3
    linarith
  -- smallness propagation ([v0, v1, v2, v3]) via WAUFCHE1/2 and the shared omega chain
  have hltv : hl (truncateSimplex k [v0, v1, v2, v3]) < Real.sqrt 2 := by
    have hbzl : barV V k (truncateSimplex k [v0, v1, v2, v3]) := TRUNCATE_SIMPLEX_BARV V k 3 [v0, v1, v2, v3] hvl hk
    have hle := WAUFCHE1 V (truncateSimplex k [v0, v1, v2, v3]) k hP hbzl
    have homegavl : omegaList V (truncateSimplex k [v0, v1, v2, v3]) = omegaListN V [v0, v1, v2, v3] k :=
      OMEGA_LIST_LEMMA V [v0, v1, v2, v3] k (by rw [hvl.1]; omega)
    have hhdvl : hdV (truncateSimplex k [v0, v1, v2, v3]) = hdV [v0, v1, v2, v3] :=
      HD_TRUNCATE_SIMPLEX [v0, v1, v2, v3] k (by rw [hvl.1]; omega)
    rw [homegavl, hhdvl] at hle
    rw [← homega k hk] at hle
    have hbwl : barV V k (truncateSimplex k [u0, u1, u2, u3]) := TRUNCATE_SIMPLEX_BARV V k 3 [u0, u1, u2, u3] hul hk
    have hwl := WAUFCHE2 V (truncateSimplex k [u0, u1, u2, u3]) k hP hbwl hlt
    have homegaul : omegaList V (truncateSimplex k [u0, u1, u2, u3]) = omegaListN V [u0, u1, u2, u3] k :=
      OMEGA_LIST_LEMMA V [u0, u1, u2, u3] k (by rw [hul.1]; omega)
    have hhdul : hdV (truncateSimplex k [u0, u1, u2, u3]) = hdV [u0, u1, u2, u3] :=
      HD_TRUNCATE_SIMPLEX [u0, u1, u2, u3] k (by rw [hul.1]; omega)
    rw [homegaul, hhdul] at hwl
    have hdvl : hdV [v0, v1, v2, v3] = hdV [u0, u1, u2, u3] := hd0.symm
    rw [hdvl, ← hwl] at hle
    linarith
  have hmonov : ∀ i : ℕ, i ≤ k → hl (truncateSimplex i [v0, v1, v2, v3]) < Real.sqrt 2 := by
    intro i hik
    have h1 : truncateSimplex i (truncateSimplex k [v0, v1, v2, v3]) = truncateSimplex i [v0, v1, v2, v3] :=
      TRUNCATE_TRUNCATE_SIMPLEX [v0, v1, v2, v3] i k hik (by rw [hvl.1]; omega)
    have hb : barV V k (truncateSimplex k [v0, v1, v2, v3]) := TRUNCATE_SIMPLEX_BARV V k 3 [v0, v1, v2, v3] hvl hk
    have h3 := HL_DECREASE V (truncateSimplex k [v0, v1, v2, v3]) k i hP hb hik
    rw [h1] at h3
    linarith
  -- pairwise distinctness of the [v0, v1, v2, v3] points
  have hcard1 : ({v0, v1} : Set V3).ncard = 2 := by
    have hb1v : barV V 1 [v0, v1] := by
      simpa using BARV_INITIAL_SUBLIST V 3 [v0, v1, v2, v3] [v0, v1] hvl
        (INITIAL_SUBLIST_APPEND [v0, v1] [v2, v3]) (by simp)
    have h := (BARV_IMP_LENGTH_EQ_CARD V [v0, v1] 1 hP hb1v).2
    have hset : setOfList [v0, v1] = ({v0, v1} : Set V3) := by ext x; simp [setOfList]
    rw [hset] at h
    exact h
  have hcard2 : ({v0, v1, v2} : Set V3).ncard = 3 := by
    have hb2v : barV V 2 [v0, v1, v2] := by
      simpa using BARV_INITIAL_SUBLIST V 3 [v0, v1, v2, v3] [v0, v1, v2] hvl
        (INITIAL_SUBLIST_APPEND [v0, v1, v2] [v3]) (by simp)
    have h := (BARV_IMP_LENGTH_EQ_CARD V [v0, v1, v2] 2 hP hb2v).2
    have hset : setOfList [v0, v1, v2] = ({v0, v1, v2} : Set V3) := by ext x; simp [setOfList]
    rw [hset] at h
    exact h
  have hcard3 : ({v0, v1, v2, v3} : Set V3).ncard = 4 := by
    have h := (BARV_IMP_LENGTH_EQ_CARD V [v0, v1, v2, v3] 3 hP hvl).2
    have hset : setOfList [v0, v1, v2, v3] = ({v0, v1, v2, v3} : Set V3) := by
      ext x; simp [setOfList]
    rw [hset] at h
    exact h
  have hv01 : v0 ≠ v1 := p9_ncard2_ne hcard1
  obtain ⟨_, hv02, hv12⟩ := p9_ncard3_ne hcard2
  obtain ⟨_, _, hv03, _, hv13, hv23⟩ := p9_ncard4_ne hcard3
  -- step 1: u1 = v1
  have hu1 : 1 ≤ k → u1 = v1 := by
    intro hk1
    by_contra hne
    have hS1 : setOfList (truncateSimplex 1 [u0, u1, u2, u3]) = ({u0, u1} : Set V3) := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2]
      ext x; simp [setOfList]
    have hb1u : barV V 1 (truncateSimplex 1 [u0, u1, u2, u3]) := TRUNCATE_SIMPLEX_BARV V 1 3 [u0, u1, u2, u3] hul (by norm_num)
    have hind1 : ¬ affineDependent ({u0, u1} : Set V3) := by
      rw [← hS1]
      exact BARV_AFFINE_INDEPENDENT V (truncateSimplex 1 [u0, u1, u2, u3]) 1 hP hb1u
    have hsv1 : ({u0, u1} : Set V3) ⊆ V := by
      rw [← hS1]
      exact BARV_SUBSET V 1 (truncateSimplex 1 [u0, u1, u2, u3]) hb1u
    have hr1 : radV ({u0, u1} : Set V3) < Real.sqrt 2 := by
      have h' : radV (setOfList (truncateSimplex 1 [u0, u1, u2, u3])) < Real.sqrt 2 := hmono 1 hk1
      rwa [hS1] at h'
    have hgap := XYOFCGX V ({u0, u1} : Set V3) (circumcenter ({u0, u1} : Set V3))
      hP hsv1 hind1 rfl hr1
    have hv1V : v1 ∈ V := by
      exact BARV_SUBSET V 3 [v0, v1, v2, v3] hvl (by simp [setOfList])
    have hv1not : v1 ∉ ({u0, u1} : Set V3) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact hv01 (by rw [← hd0', h])
      · exact hne h.symm
    have h1 := hgap u0 v1 (by simp) ⟨hv1V, hv1not⟩
    have hS1v : setOfList (truncateSimplex 1 [v0, v1, v2, v3]) = ({v0, v1} : Set V3) := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2]
      ext x; simp [setOfList]
    have hb1v : barV V 1 (truncateSimplex 1 [v0, v1, v2, v3]) := TRUNCATE_SIMPLEX_BARV V 1 3 [v0, v1, v2, v3] hvl (by norm_num)
    have hind1v : ¬ affineDependent ({v0, v1} : Set V3) := by
      rw [← hS1v]
      exact BARV_AFFINE_INDEPENDENT V (truncateSimplex 1 [v0, v1, v2, v3]) 1 hP hb1v
    have hcenu := p9_omega1_circumcenter V u0 u1 u2 u3 [u0, u1, u2, u3] hs hP hul rfl (hmono 1 hk1)
    have hcenv := p9_omega1_circumcenter V v0 v1 v2 v3 [v0, v1, v2, v3] hs hP hvl rfl (hmonov 1 hk1)
    have hcu : circumcenter ({u0, u1} : Set V3) = circumcenter ({v0, v1} : Set V3) := by
      rw [← hcenu, ← hcenv, homega 1 (by norm_num)]
    have hdv1 : dist v1 (circumcenter ({v0, v1} : Set V3)) = radV ({v0, v1} : Set V3) := by
      rw [dist_comm]
      exact (OAPVION2 ({v0, v1} : Set V3) hind1v v1 (by simp)).symm
    have hdu0 : dist u0 (circumcenter ({v0, v1} : Set V3)) = radV ({v0, v1} : Set V3) := by
      rw [dist_comm, hd0']
      exact (OAPVION2 ({v0, v1} : Set V3) hind1v v0 (by simp)).symm
    rw [hcu, hdv1, hdu0] at h1
    exact absurd h1 (lt_irrefl _)
  -- step 2: u2 = v2
  have hu2 : 2 ≤ k → u2 = v2 := by
    intro hk2
    have hk1 : 1 ≤ k := by omega
    by_contra hne
    have hS2 : setOfList (truncateSimplex 2 [u0, u1, u2, u3]) = ({u0, u1, u2} : Set V3) := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2]
      ext x; simp [setOfList]
    have hb2u : barV V 2 (truncateSimplex 2 [u0, u1, u2, u3]) := TRUNCATE_SIMPLEX_BARV V 2 3 [u0, u1, u2, u3] hul (by norm_num)
    have hind2 : ¬ affineDependent ({u0, u1, u2} : Set V3) := by
      rw [← hS2]
      exact BARV_AFFINE_INDEPENDENT V (truncateSimplex 2 [u0, u1, u2, u3]) 2 hP hb2u
    have hsv2 : ({u0, u1, u2} : Set V3) ⊆ V := by
      rw [← hS2]
      exact BARV_SUBSET V 2 (truncateSimplex 2 [u0, u1, u2, u3]) hb2u
    have hr2 : radV ({u0, u1, u2} : Set V3) < Real.sqrt 2 := by
      have h' : radV (setOfList (truncateSimplex 2 [u0, u1, u2, u3])) < Real.sqrt 2 := hmono 2 hk2
      rwa [hS2] at h'
    have hgap := XYOFCGX V ({u0, u1, u2} : Set V3) (circumcenter ({u0, u1, u2} : Set V3))
      hP hsv2 hind2 rfl hr2
    have hv2V : v2 ∈ V := BARV_SUBSET V 3 [v0, v1, v2, v3] hvl (by simp [setOfList])
    have hd1' : u1 = v1 := hu1 hk1
    have hv2not : v2 ∉ ({u0, u1, u2} : Set V3) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h)
      · exact hv02 (by rw [← hd0', h])
      · exact hv12 (by rw [← hd1', h])
      · exact hne h.symm
    have h1 := hgap u0 v2 (by simp) ⟨hv2V, hv2not⟩
    have hS2v : setOfList (truncateSimplex 2 [v0, v1, v2, v3]) = ({v0, v1, v2} : Set V3) := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 v0 v1 v2 v3).2]
      ext x; simp [setOfList]
    have hb2v : barV V 2 (truncateSimplex 2 [v0, v1, v2, v3]) := TRUNCATE_SIMPLEX_BARV V 2 3 [v0, v1, v2, v3] hvl (by norm_num)
    have hind2v : ¬ affineDependent ({v0, v1, v2} : Set V3) := by
      rw [← hS2v]
      exact BARV_AFFINE_INDEPENDENT V (truncateSimplex 2 [v0, v1, v2, v3]) 2 hP hb2v
    have hcenu := p9_omega2_circumcenter V u0 u1 u2 u3 [u0, u1, u2, u3] hs hP hul rfl (hmono 2 hk2)
    have hcenv := p9_omega2_circumcenter V v0 v1 v2 v3 [v0, v1, v2, v3] hs hP hvl rfl (hmonov 2 hk2)
    have hcu2 : circumcenter ({u0, u1, u2} : Set V3) = circumcenter ({v0, v1, v2} : Set V3) := by
      rw [← hcenu, ← hcenv, homega 2 (by norm_num)]
    have hdv2 : dist v2 (circumcenter ({v0, v1, v2} : Set V3)) = radV ({v0, v1, v2} : Set V3) := by
      rw [dist_comm]
      exact (OAPVION2 ({v0, v1, v2} : Set V3) hind2v v2 (by simp)).symm
    have hdu0' : dist u0 (circumcenter ({v0, v1, v2} : Set V3)) = radV ({v0, v1, v2} : Set V3) := by
      rw [dist_comm, hd0']
      exact (OAPVION2 ({v0, v1, v2} : Set V3) hind2v v0 (by simp)).symm
    rw [hcu2, hdv2, hdu0'] at h1
    exact absurd h1 (lt_irrefl _)
  -- step 3: u3 = v3
  have hu3 : 3 ≤ k → u3 = v3 := by
    intro hk3
    have hk2 : 2 ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    by_contra hne
    have hS3 : setOfList [u0, u1, u2, u3] = ({u0, u1, u2, u3} : Set V3) := by
      ext x; simp [setOfList]
    have hind3 : ¬ affineDependent ({u0, u1, u2, u3} : Set V3) := by
      rw [← hS3]
      exact BARV_AFFINE_INDEPENDENT V [u0, u1, u2, u3] 3 hP hul
    have hsv3 : ({u0, u1, u2, u3} : Set V3) ⊆ V := by
      rw [← hS3]
      exact BARV_SUBSET V 3 [u0, u1, u2, u3] hul
    have hr3 : radV ({u0, u1, u2, u3} : Set V3) < Real.sqrt 2 := by
      have h' : radV (setOfList [u0, u1, u2, u3]) < Real.sqrt 2 := by
        have h := hmono 3 hk3
        rwa [TRUNCATE_SIMPLEX_REFL 3 [u0, u1, u2, u3] rfl] at h
      rwa [hS3] at h'
    have hgap := XYOFCGX V ({u0, u1, u2, u3} : Set V3)
      (circumcenter ({u0, u1, u2, u3} : Set V3)) hP hsv3 hind3 rfl hr3
    have hv3V : v3 ∈ V := BARV_SUBSET V 3 [v0, v1, v2, v3] hvl (by simp [setOfList])
    have hd1' : u1 = v1 := hu1 hk1
    have hd2' : u2 = v2 := hu2 hk2
    have hv3not : v3 ∉ ({u0, u1, u2, u3} : Set V3) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h | h)
      · exact hv03 (by rw [← hd0', h])
      · exact hv13 (by rw [← hd1', h])
      · exact hv23 (by rw [← hd2', h])
      · exact hne h.symm
    have h1 := hgap u0 v3 (by simp) ⟨hv3V, hv3not⟩
    have hltul : hl [u0, u1, u2, u3] < Real.sqrt 2 := by
      have h := hmono 3 hk3
      rwa [TRUNCATE_SIMPLEX_REFL 3 [u0, u1, u2, u3] rfl] at h
    have hltvl : hl [v0, v1, v2, v3] < Real.sqrt 2 := by
      have h := hmonov 3 hk3
      rwa [TRUNCATE_SIMPLEX_REFL 3 [v0, v1, v2, v3] rfl] at h
    have hcenu := OMEGA_LIST_3_EXPLICIT u0 u1 u2 u3 V [u0, u1, u2, u3] hs hP hul hltul rfl
    have hcenv := OMEGA_LIST_3_EXPLICIT v0 v1 v2 v3 V [v0, v1, v2, v3] hs hP hvl hltvl rfl
    have hcu3 : circumcenter ({u0, u1, u2, u3} : Set V3) =
        circumcenter ({v0, v1, v2, v3} : Set V3) := by
      rw [← hcenu, ← hcenv, homega 3 (by norm_num)]
    have hS3v : setOfList [v0, v1, v2, v3] = ({v0, v1, v2, v3} : Set V3) := by
      ext x; simp [setOfList]
    have hind3v : ¬ affineDependent ({v0, v1, v2, v3} : Set V3) := by
      rw [← hS3v]
      exact BARV_AFFINE_INDEPENDENT V [v0, v1, v2, v3] 3 hP hvl
    have hdv3 : dist v3 (circumcenter ({v0, v1, v2, v3} : Set V3)) =
        radV ({v0, v1, v2, v3} : Set V3) := by
      rw [dist_comm]
      exact (OAPVION2 ({v0, v1, v2, v3} : Set V3) hind3v v3 (by simp)).symm
    have hdu0'' : dist u0 (circumcenter ({v0, v1, v2, v3} : Set V3)) =
        radV ({v0, v1, v2, v3} : Set V3) := by
      rw [dist_comm, hd0']
      exact (OAPVION2 ({v0, v1, v2, v3} : Set V3) hind3v v0 (by simp)).symm
    rw [hcu3, hdv3, hdu0''] at h1
    exact absurd h1 (lt_irrefl _)
  interval_cases k
  · rw [(TRUNCATE_SIMPLEX_EXPLICIT_0 u0 u1 u2 u3).2.2.2,
      (TRUNCATE_SIMPLEX_EXPLICIT_0 v0 v1 v2 v3).2.2.2, hd0']
  · rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2, hd0', hu1 le_rfl]
  · rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2,
      (TRUNCATE_SIMPLEX_EXPLICIT_2 v0 v1 v2 v3).2, hd0', hu1 (by norm_num), hu2 le_rfl]
  · rw [(TRUNCATE_SIMPLEX_EXPLICIT_3 u0 u1 u2 u3),
      (TRUNCATE_SIMPLEX_EXPLICIT_3 v0 v1 v2 v3), hd0', hu1 (by norm_num),
      hu2 (by norm_num), hu3 le_rfl]


end Kepler.Text
