/-
Packing chapter, marchal1 lane: the Marchal-cell truncation bridge.

HOL source: Flyspeck `scripts/packing/marchal1.hl` (module `Marchal_cells`,
VU KHAC KY, 2010-10-03; 541 lines, 17 `prove_by_refinement` items). This file
supports the marchal-cells measure work: explicit computations of
`truncate_simplex` at levels 0..3, the reduction of `omega_list_n` on a
4-point `barV V 3` list to `omega_list` on its truncations, and small
dimension/convexity utilities.

Encoding notes.
- HOL `real^3` ↔ `V3` (Kepler.Geom); generic `real^N` list/set lemmas are
  instantiated at `V3` (the only downstream instance), matching the
  V3-specialized defs of PackingAuto2.
- HOL `truncate_simplex`/`omega_list_n`/`omega_list`/`barV`/`hl`/
  `saturated`/`set_of_list` ↔ `truncateSimplex`/`omegaListN`/`omegaList`/
  `barV`/`hl`/`saturated`/`setOfList` (Kepler.Text.PackingAuto2);
  `initial_sublist` ↔ `initialSublist` (`∃ yl, zl = xl ++ yl`);
  `aff_dim` ↔ `affDim` (Kepler.Text.Polytope); `circumcenter` ↔ `circumcenter`
  on `Set V3` (so HOL `{a,b}` ↔ `{a, b}`, the inserted 2-element set).
- HOL `convex hull` ↔ `convexHull ℝ`; `dist (s,x)` ↔ `dist s x`;
  `ball (s,r)` ↔ `Metric.ball s r`.
- Rogers dependency: HL `OMEGA_LIST_{1,2,3}_EXPLICIT` cite Rogers.hl
  `XNHPWAB1` (HL:319/364/411) and `XNHPWAB4` (HL:342/387) via
  `open Rogers;;` (marchal1.hl:34). Those Rogers lanes (PackingAuto6/7) are
  NOT importable yet, so the three proofs are discharged here through the
  statement-identical pack_concl interfaces `XNHPWAB1_concl`/`XNHPWAB4_concl`
  of PackingAuto2 (which carry the Rogers `sorry`s at this stage). Delete
  this note when Auto6/7 land and those interfaces get proved.
- The two `AFF_DIM_LE_LENGTH`/`BALL_CONVEX_HULL_LEMMA` statements are
  `real^N`-generic in HOL; ported at `V3`.
- Imports: `Kepler.Text.PackingAuto2` (defs + the pack_concl interfaces),
  `Kepler.Text.PackingAuto5` (initial-sublist/truncation kit),
  `Kepler.Text.Polytope` (`affDim`), `Mathlib`.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Truncate_simplex at levels 0..3 (marchal1.hl:38-255) -/

/-- HOL `TRUNCATE_SIMPLEX_GENERAL_0` (marchal1.hl:38):
`!xl. ~(xl = []) ==> truncate_simplex 0 xl = [HD xl]`. -/
theorem TRUNCATE_SIMPLEX_GENERAL_0 (xl : List V3) (hne : xl ≠ []) :
    truncateSimplex 0 xl = [hdV xl] :=
  TRUNCATE_0_EQ_HEAD xl (List.length_pos_of_ne_nil hne)

/-- HOL `TRUNCATE_SIMPLEX_EXPLICIT_0` (marchal1.hl:69). -/
theorem TRUNCATE_SIMPLEX_EXPLICIT_0 (u0 u1 u2 u3 : V3) :
    truncateSimplex 0 [u0] = [u0] ∧
    truncateSimplex 0 [u0, u1] = [u0] ∧
    truncateSimplex 0 [u0, u1, u2] = [u0] ∧
    truncateSimplex 0 [u0, u1, u2, u3] = [u0] := by
  have h0 := TRUNCATE_SIMPLEX_GENERAL_0
  exact ⟨h0 _ (by simp), h0 _ (by simp), h0 _ (by simp), h0 _ (by simp)⟩

/-- HOL `TRUNCATE_SIMPLEX_GENERAL_1` (marchal1.hl:92):
`ul = APPEND [a;b] vl ==> truncate_simplex 1 ul = [a;b]`. -/
theorem TRUNCATE_SIMPLEX_GENERAL_1 (ul vl : List V3) (a b : V3)
    (h : ul = [a, b] ++ vl) : truncateSimplex 1 ul = [a, b] :=
  ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST 1 [a, b] ul).2
    ⟨by rw [h]; exact INITIAL_SUBLIST_APPEND [a, b] vl, rfl⟩).1

/-- HOL `TRUNCATE_SIMPLEX_EXPLICIT_1` (marchal1.hl:128). -/
theorem TRUNCATE_SIMPLEX_EXPLICIT_1 (a b c d : V3) :
    truncateSimplex 1 [a, b] = [a, b] ∧
    truncateSimplex 1 [a, b, c] = [a, b] ∧
    truncateSimplex 1 [a, b, c, d] = [a, b] :=
  ⟨TRUNCATE_SIMPLEX_GENERAL_1 _ [] a b rfl,
   TRUNCATE_SIMPLEX_GENERAL_1 _ [c] a b rfl,
   TRUNCATE_SIMPLEX_GENERAL_1 _ [c, d] a b rfl⟩

/-- HOL `TRUNCATE_SIMPLEX_GENERAL_2` (marchal1.hl:146):
`ul = APPEND [a;b;c] vl ==> truncate_simplex 2 ul = [a;b;c]`. -/
theorem TRUNCATE_SIMPLEX_GENERAL_2 (ul vl : List V3) (a b c : V3)
    (h : ul = [a, b, c] ++ vl) : truncateSimplex 2 ul = [a, b, c] :=
  ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST 2 [a, b, c] ul).2
    ⟨by rw [h]; exact INITIAL_SUBLIST_APPEND [a, b, c] vl, rfl⟩).1

/-- HOL `TRUNCATE_SIMPLEX_EXPLICIT_2` (marchal1.hl:189). -/
theorem TRUNCATE_SIMPLEX_EXPLICIT_2 (a b c d : V3) :
    truncateSimplex 2 [a, b, c] = [a, b, c] ∧
    truncateSimplex 2 [a, b, c, d] = [a, b, c] :=
  ⟨TRUNCATE_SIMPLEX_GENERAL_2 _ [] a b c rfl,
   TRUNCATE_SIMPLEX_GENERAL_2 _ [d] a b c rfl⟩

/-- HOL `TRUNCATE_SIMPLEX_EXPLICIT_3` (marchal1.hl:204). -/
theorem TRUNCATE_SIMPLEX_EXPLICIT_3 (a b c d : V3) :
    truncateSimplex 3 [a, b, c, d] = [a, b, c, d] :=
  TRUNCATE_SIMPLEX_REFL 3 [a, b, c, d] rfl

/-! ## omega_list_n on the 4-point list (marchal1.hl:262-301) -/

/-- HOL `OMEGA_LIST_TRUNCATE_1` (marchal1.hl:262):
`omega_list_n V [u0;u1;u2;u3] 1 = omega_list V [u0;u1]`. -/
theorem OMEGA_LIST_TRUNCATE_1 (V : Set V3) (u0 u1 u2 u3 : V3) :
    omegaListN V [u0, u1, u2, u3] 1 = omegaList V [u0, u1] := by
  have he : omegaList V [u0, u1] = omegaListN V [u0, u1] 1 := rfl
  rw [he]
  show closestPoint (voronoiList V (truncateSimplex 1 [u0, u1, u2, u3]))
      (hdV [u0, u1, u2, u3]) =
    closestPoint (voronoiList V (truncateSimplex 1 [u0, u1])) (hdV [u0, u1])
  rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).1]
  rfl

/-- HOL `OMEGA_LIST_TRUNCATE_2` (marchal1.hl:274):
`omega_list_n V [u0;u1;u2;u3] 2 = omega_list V [u0;u1;u2]`. -/
theorem OMEGA_LIST_TRUNCATE_2 (V : Set V3) (u0 u1 u2 u3 : V3) :
    omegaListN V [u0, u1, u2, u3] 2 = omegaList V [u0, u1, u2] := by
  have he : omegaList V [u0, u1, u2] = omegaListN V [u0, u1, u2] 2 := rfl
  rw [he]
  show closestPoint (voronoiList V (truncateSimplex 2 [u0, u1, u2, u3]))
      (closestPoint (voronoiList V (truncateSimplex 1 [u0, u1, u2, u3]))
        (hdV [u0, u1, u2, u3])) =
    closestPoint (voronoiList V (truncateSimplex 2 [u0, u1, u2]))
      (closestPoint (voronoiList V (truncateSimplex 1 [u0, u1, u2]))
        (hdV [u0, u1, u2]))
  rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2,
      (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).1,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.1]
  rfl

/-- HOL `OMEGA_LIST_0_EXPLICIT` (marchal1.hl:291). The HL binder list omits
`d` (`!a b c V ul` with `ul = [a;b;c;d]`); generalized here. Mechanical:
`omega_list_n V ul 0 = HD ul`. -/
theorem OMEGA_LIST_0_EXPLICIT (a b c d : V3) (V : Set V3) (ul : List V3)
    (_hsat : saturated V) (_hpack : Packing V) (_hbar : barV V 3 ul)
    (_hlt : hl ul < Real.sqrt 2) (hul : ul = [a, b, c, d]) :
    omegaListN V ul 0 = a := by
  rw [hul]
  rfl

/-! ## omega_list_n as circumcenters (marchal1.hl:306-419; Rogers-dependent) -/

/-- HOL `OMEGA_LIST_1_EXPLICIT` (marchal1.hl:306): on a `sqrt 2`-small
`barV V 3` list, the first omega point is the circumcenter of `{a,b}`.
NEEDS: Rogers (PackingAuto6/7) `XNHPWAB4` (HL:342) and `XNHPWAB1` (HL:319) —
discharged via the statement-identical PackingAuto2 interfaces
`XNHPWAB4_concl`/`XNHPWAB1_concl`. -/
theorem OMEGA_LIST_1_EXPLICIT (a b c d : V3) (V : Set V3) (ul : List V3)
    (_hsat : saturated V) (_hpack : Packing V) (hbar : barV V 3 ul)
    (_hlt : hl ul < Real.sqrt 2) (hul : ul = [a, b, c, d]) :
    omegaListN V ul 1 = circumcenter {a, b} := by
  rw [hul] at hbar _hlt ⊢
  have hb1 : barV V 1 [a, b] := by
    simpa using BARV_INITIAL_SUBLIST V 3 [a, b, c, d] [a, b] hbar
      (INITIAL_SUBLIST_APPEND [a, b] [c, d]) (by simp)
  have hmono : hl (truncateSimplex 1 [a, b, c, d]) < hl (truncateSimplex 3 [a, b, c, d]) :=
    XNHPWAB4_concl V [a, b, c, d] 3 _hsat _hpack le_rfl hbar _hlt 1 3 (by omega) (by omega)
  rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 a b c d).2.2,
      TRUNCATE_SIMPLEX_REFL 3 [a, b, c, d] rfl] at hmono
  have hcen : omegaList V [a, b] = circumcenter (setOfList [a, b]) :=
    XNHPWAB1_concl V [a, b] 1 _hsat _hpack (by omega) hb1 (hmono.trans _hlt)
  rw [OMEGA_LIST_TRUNCATE_1, hcen]
  exact congrArg circumcenter (by ext x; simp [setOfList])

/-- HOL `OMEGA_LIST_2_EXPLICIT` (marchal1.hl:351): the second omega point is
the circumcenter of `{a,b,c}`.
NEEDS: Rogers (PackingAuto6/7) `XNHPWAB4` (HL:387) and `XNHPWAB1` (HL:364) —
discharged via `XNHPWAB4_concl`/`XNHPWAB1_concl`. -/
theorem OMEGA_LIST_2_EXPLICIT (a b c d : V3) (V : Set V3) (ul : List V3)
    (_hsat : saturated V) (_hpack : Packing V) (hbar : barV V 3 ul)
    (_hlt : hl ul < Real.sqrt 2) (hul : ul = [a, b, c, d]) :
    omegaListN V ul 2 = circumcenter {a, b, c} := by
  rw [hul] at hbar _hlt ⊢
  have hb2 : barV V 2 [a, b, c] := by
    simpa using BARV_INITIAL_SUBLIST V 3 [a, b, c, d] [a, b, c] hbar
      (INITIAL_SUBLIST_APPEND [a, b, c] [d]) (by simp)
  have hmono : hl (truncateSimplex 2 [a, b, c, d]) < hl (truncateSimplex 3 [a, b, c, d]) :=
    XNHPWAB4_concl V [a, b, c, d] 3 _hsat _hpack le_rfl hbar _hlt 2 3 (by omega) (by omega)
  rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 a b c d).2,
      TRUNCATE_SIMPLEX_REFL 3 [a, b, c, d] rfl] at hmono
  have hcen : omegaList V [a, b, c] = circumcenter (setOfList [a, b, c]) :=
    XNHPWAB1_concl V [a, b, c] 2 _hsat _hpack (by omega) hb2 (hmono.trans _hlt)
  rw [OMEGA_LIST_TRUNCATE_2, hcen]
  exact congrArg circumcenter (by ext x; simp [setOfList])

/-- HOL `OMEGA_LIST_3_EXPLICIT` (marchal1.hl:398): the last omega point is
the circumcenter of the whole list.
NEEDS: Rogers (PackingAuto6/7) `XNHPWAB1` (HL:411) — discharged via
`XNHPWAB1_concl`. -/
theorem OMEGA_LIST_3_EXPLICIT (a b c d : V3) (V : Set V3) (ul : List V3)
    (_hsat : saturated V) (_hpack : Packing V) (hbar : barV V 3 ul)
    (_hlt : hl ul < Real.sqrt 2) (hul : ul = [a, b, c, d]) :
    omegaListN V ul 3 = circumcenter {a, b, c, d} := by
  rw [hul] at hbar _hlt ⊢
  have hcen : omegaList V [a, b, c, d] = circumcenter (setOfList [a, b, c, d]) :=
    XNHPWAB1_concl V [a, b, c, d] 3 _hsat _hpack le_rfl hbar _hlt
  have hrw : omegaListN V [a, b, c, d] 3 = omegaList V [a, b, c, d] := rfl
  rw [hrw, hcen]
  exact congrArg circumcenter (by ext x; simp [setOfList])

/-! ## barV at level 3 (marchal1.hl:424-459) -/

/-- HOL `BARV_3_EXPLICIT` (marchal1.hl:424): a `barV V 3` list has exactly
four points. -/
theorem BARV_3_EXPLICIT (V : Set V3) (vl : List V3) (h : barV V 3 vl) :
    ∃ u0 u1 u2 u3 : V3, vl = [u0, u1, u2, u3] := by
  have h4 : vl.length = 4 := h.1
  rcases vl with _ | ⟨u0, vl1⟩
  · simp at h4
  rcases vl1 with _ | ⟨u1, vl2⟩
  · simp at h4
  rcases vl2 with _ | ⟨u2, vl3⟩
  · simp at h4
  rcases vl3 with _ | ⟨u3, vl4⟩
  · simp at h4
  rcases vl4 with _ | ⟨u4, _⟩
  · exact ⟨u0, u1, u2, u3, rfl⟩
  · simp only [List.length_cons] at h4
    omega

/-! ## Dimension and convexity utilities (marchal1.hl:465-529) -/

/-- Membership in a list is realized by a `getD` index (mechanical helper,
replacing the HOL `LENGTH_EQ_CONS` destructuring steps). -/
private theorem mem_getD {xl : List V3} {p : V3} (hp : p ∈ xl) :
    ∃ i : ℕ, i < xl.length ∧ xl.getD i 0 = p := by
  induction xl with
  | nil => cases hp
  | cons a t ih =>
    rcases List.mem_cons.1 hp with rfl | hm
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨i, hi, he⟩ := ih hm
      refine ⟨i + 1, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · simpa using he

/-- The linear map sending the standard basis of `Fin m → ℝ` to the edge
vectors `xl.getD (j+1) 0 - xl.getD 0 0`; its range carries the vector span of
`setOfList xl` when `xl.length = m + 1` (helper for `AFF_DIM_LE_LENGTH`,
replacing the HOL `AFFINE_BASIS_EXISTS` argument). -/
private def sumDiffMap (xl : List V3) (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] V3 :=
  ∑ j : Fin m,
    LinearMap.smulRight (LinearMap.proj j) (xl.getD (j + 1) 0 - xl.getD 0 0)

private theorem sumDiffMap_apply (xl : List V3) (m : ℕ) (c : Fin m → ℝ) :
    sumDiffMap xl m c = ∑ j : Fin m, c j • (xl.getD (j + 1) 0 - xl.getD 0 0) := by
  simp [sumDiffMap]

/-- HOL `AFF_DIM_LE_LENGTH` (marchal1.hl:465):
`LENGTH xl = n ==> aff_dim (set_of_list xl) < &n` — the affine dimension of
the point set of a list is below the point count (`real^N`-generic in HOL,
ported at `V3`). -/
theorem AFF_DIM_LE_LENGTH (xl : List V3) (n : ℕ) (h : xl.length = n) :
    affDim (setOfList xl) < (n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hnil : xl = [] := List.length_eq_zero_iff.1 h
    have hempty : setOfList xl = (∅ : Set V3) := by
      rw [hnil]; ext x; simp [setOfList]
    unfold affDim
    rw [if_pos hempty]
    omega
  · have hne : ¬(setOfList xl = (∅ : Set V3)) := by
      intro he
      rcases xl with _ | ⟨a, t⟩
      · rw [List.length_nil] at h; omega
      · exact Set.notMem_empty a (by rw [← he]; simp [setOfList])
    have key : ∀ i : ℕ, i < n →
        xl.getD i 0 - xl.getD 0 0 ∈ LinearMap.range (sumDiffMap xl (n - 1)) := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with hir | hip
      · have e0 : xl.getD i 0 - xl.getD 0 0 = 0 := by
          rw [show i = 0 by omega]
          simp
        rw [e0]
        exact ⟨0, by rw [sumDiffMap_apply]; simp⟩
      · obtain ⟨k, hk0⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hkn : k < n - 1 := by omega
        refine ⟨fun j => if (j : ℕ) = k then (1 : ℝ) else 0, ?_⟩
        rw [sumDiffMap_apply]
        show (∑ j : Fin (n - 1),
              (if (j : ℕ) = k then (1 : ℝ) else 0) •
                (xl.getD (j + 1) 0 - xl.getD 0 0)) = _
        rw [Finset.sum_eq_single ⟨k, hkn⟩]
        · simp [hk0]
        · intro j _ hj
          have hjk : (j : ℕ) ≠ k := fun hh => hj (Fin.eq_of_val_eq hh)
          simp [hjk]
        · simp
    have hgens : (setOfList xl -ᵥ setOfList xl) ⊆
        (LinearMap.range (sumDiffMap xl (n - 1)) : Set V3) := by
      rintro w ⟨p, hp, q, hq, rfl⟩
      show p - q ∈ LinearMap.range (sumDiffMap xl (n - 1))
      obtain ⟨i, hi, hpi⟩ := mem_getD hp
      obtain ⟨j, hj, hqj⟩ := mem_getD hq
      rw [← hpi, ← hqj]
      have hi' := key i (by omega)
      have hj' := key j (by omega)
      have hsub2 : xl.getD i 0 - xl.getD j 0 =
          (xl.getD i 0 - xl.getD 0 0) - (xl.getD j 0 - xl.getD 0 0) := by abel
      rw [hsub2]
      exact Submodule.sub_mem _ hi' hj'
    have hvs : vectorSpan ℝ (setOfList xl) ≤
        LinearMap.range (sumDiffMap xl (n - 1)) := by
      rw [vectorSpan_def]
      exact Submodule.span_le.2 hgens
    have hfr : Module.finrank ℝ (vectorSpan ℝ (setOfList xl)) ≤ n - 1 := by
      refine le_trans (Submodule.finrank_mono hvs) ?_
      refine le_trans (LinearMap.finrank_range_le (sumDiffMap xl (n - 1))) ?_
      rw [Module.finrank_fin_fun]
    unfold affDim
    rw [if_neg hne]
    omega

/-- HOL `CONVEX_HULL_SUBSET` (marchal1.hl:498): monotonicity of the convex
hull (`real^N`-generic in HOL, ported at `V3`; Mathlib `convex_hull_mono`). -/
theorem CONVEX_HULL_SUBSET (S S' : Set V3) (h : S ⊆ S') :
    convexHull ℝ S ⊆ convexHull ℝ S' :=
  convexHull_mono h

/-- HOL `BALL_CONVEX_HULL_LEMMA` (marchal1.hl:515): if all points of `S` lie
within distance `r` of `s`, so does every point of the convex hull
(`real^N`-generic in HOL, ported at `V3`). -/
theorem BALL_CONVEX_HULL_LEMMA (S : Set V3) (s x : V3) (r : ℝ)
    (h : ∀ y ∈ S, dist s y < r) (hx : x ∈ convexHull ℝ S) : dist s x < r := by
  have hcvx : Convex ℝ (Metric.ball s r) := convex_ball s r
  have hsub : S ⊆ Metric.ball s r :=
    fun y hy => Metric.mem_ball.2 (by rw [dist_comm y s]; exact h y hy)
  have hmem : x ∈ Metric.ball s r := convexHull_min hsub hcvx hx
  rw [Metric.mem_ball] at hmem
  rwa [dist_comm x s] at hmem

end Kepler.Text
