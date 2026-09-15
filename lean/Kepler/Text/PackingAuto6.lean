/-
Kepler.Text.PackingAuto6 — Rogers simplex chapter, part A (statement-
faithful skeleton; geometric/measure giants `sorry`ed).

HOL source: `scripts/packing/Rogers.hl` (10872 lines, 111 theorems, 0 defs;
Alexey Solovyev 2010, chapter "Packing/Rogers simplex").

PART BOUNDARY:
  part A (this file): Rogers.hl theorems 1-65, lines 35-5365
    (BIS_FACE_OF_BIS_LE .. AZIM_EQ_SYM).
  part B (Kepler/Text/PackingAuto7.lean): from STRICT_CYCLIC_IMP_FAN
    (Rogers.hl:5373, start of the strict-cyclic-fan / angle-sum cluster)
    through the end of the file.

Encoding (conventions of Kepler/Text/Polytope.lean:1-40 and the
PackingAuto2 header):
  HOL `real^3` ↔ `V3` (Kepler.Geom = EuclideanSpace ℝ (Fin 3));
  `bis`/`bis_le` ↔ `bis`/`bisLe`; `voronoi_closed`/`_list`/`_set` ↔
  `voronoiClosed`/`voronoiList`/`voronoiSet`; `barV`; `truncate_simplex` ↔
  `truncateSimplex`; `omega_list_n` ↔ `omegaListN`; `set_of_list` ↔
  `setOfList`; `initial_sublist` ↔ `initialSublist`; `HD` ↔ `hdV`;
  `rogers`; `circumcenter`; `radV`; `face_of` ↔ `FaceOf`; `facet_of` ↔
  `FacetOf`; `polyhedron`; `aff_dim` ↔ `affDim` (ℤ-valued, ∅ ↦ -1);
  `coplanar` ↔ `Coplanar`; `packing` ↔ `Packing`; `saturated`;
  `affine hull s` ↔ `(affineSpan ℝ s : Set V3)`; `span s` ↔
  `Submodule.span ℝ s`; `independent s` ↔ `LinearIndependent ℝ` over `↥s`;
  `dim s` ↔ `Module.finrank ℝ (Submodule.span ℝ s)`; `vsum (1..n)` ↔
  `∑ i ∈ Finset.Icc 1 n`; `x % v` ↔ `x • v`; `dist(p,x)` ↔ `dist p x`;
  `PSUBSET` ↔ `⊂`; `SUC k` ↔ `k + 1`; `IMAGE` ↔ `Set.image`.
  vol/sol/measure conventions (PackingAuto2 header): HOL `measure` ↔
  `volume.real` (real-valued Lebesgue volume, Kepler/Geom/Volume.lean);
  `sol x C` ↔ `sol` (solid-angle density, Geom/Volume.lean); `NULLSET` ↔
  `volume X = 0`. (Part A states no volume facts; DUUNHOR/GLTVHUM use
  `Coplanar`/`rogers` only.)
  `arcV p u v` ↔ `arcV` (Geom/LuneVolume: arccos of the normalised dot);
  `azim` ↔ `azim` (Geom/Azim); `angle(a,b,c)` ↔ `EuclideanGeometry.angle`.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical EuclideanGeometry

/-! ## Rogers.hl:35-521 — faces of the bisector halfspace -/

/-- Rogers.hl:35 `BIS_FACE_OF_BIS_LE`: `A(u,v)` is a face of `A+(u,v)`. -/
theorem BIS_FACE_OF_BIS_LE (u v : V3) : FaceOf (bis u v) (bisLe u v) := by
  refine ⟨fun x hx => by simpa only [bisLe, Set.mem_setOf_eq] using le_of_eq hx,
    CONVEX_BIS u v, ?_⟩
  intro a b x ha hb hx hseg
  rw [BIS_EQ_HYPERPLANE] at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [BIS_LE_EQ_HALFSPACE] at ha hb
  simp only [Set.mem_setOf_eq] at ha hb
  simp only [openSegment, Set.mem_setOf_eq] at hseg
  obtain ⟨t1, t2, ht1, ht2, ht12, hxt⟩ := hseg
  -- linearity of `z ↦ (v - u) ⬝ᵥ z` along the segment
  have hsmul : ∀ (r : ℝ) (y : V3), (v - u) ⬝ᵥ (r • y) = r * ((v - u) ⬝ᵥ y) :=
    fun r y => dotProduct_smul r ((v - u : V3) : Fin 3 → ℝ) (y : Fin 3 → ℝ)
  have hadd : ∀ (y z : V3), (v - u) ⬝ᵥ (y + z) =
      (v - u) ⬝ᵥ y + (v - u) ⬝ᵥ z :=
    fun y z => dotProduct_add ((v - u : V3) : Fin 3 → ℝ) (y : Fin 3 → ℝ)
      (z : Fin 3 → ℝ)
  set A := 2 * ((v - u) ⬝ᵥ a) with hAdef
  set B := 2 * ((v - u) ⬝ᵥ b) with hBdef
  set C := v ⬝ᵥ v - u ⬝ᵥ u with hCdef
  have h1 : t1 * A + t2 * B = C := by
    rw [← hx, ← hxt, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul,
      hadd, hsmul, hsmul]
    ring
  have h2 : t1 * C + t2 * C = C := by rw [← add_mul, ht12, one_mul]
  have hz1 : t1 * (C - A) + t2 * (C - B) = 0 := by nlinarith
  have hz2 : t1 * (C - A) = 0 := by
    have hnn1 : 0 ≤ t1 * (C - A) := mul_nonneg ht1.le (sub_nonneg.2 ha)
    have hnn2 : 0 ≤ t2 * (C - B) := mul_nonneg ht2.le (sub_nonneg.2 hb)
    nlinarith
  have hz3 : t2 * (C - B) = 0 := by
    have hnn1 : 0 ≤ t1 * (C - A) := mul_nonneg ht1.le (sub_nonneg.2 ha)
    have hnn2 : 0 ≤ t2 * (C - B) := mul_nonneg ht2.le (sub_nonneg.2 hb)
    nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

/-- Rogers.hl:52 `KHEJKCI_GEN`: nested Voronoi lists are nested faces. -/
theorem KHEJKCI_GEN (V : Set V3) (k r : ℕ) (ul vl : List V3)
    (hs : saturated V) (hP : Packing V) (hk : barV V k ul) (hr : barV V r vl)
    (hinit : initialSublist ul vl) :
    FaceOf (voronoiList V vl) (voronoiList V ul) := by
  sorry

/-- Rogers.hl:142 `KHEJKCI`: the Voronoi list is a face of the closed
Voronoi cell of its head. -/
theorem KHEJKCI (V : Set V3) (k : ℕ) (ul : List V3) (hs : saturated V)
    (hP : Packing V) (hk : barV V k ul) :
    FaceOf (voronoiList V ul) (voronoiClosed V (hdV ul)) := by
  sorry

/-- Rogers.hl:172 `VORONOI_BARV_CANONICAL`: canonical halfspace
representation of the Voronoi list of a `barV` list. -/
theorem VORONOI_BARV_CANONICAL (V : Set V3) (k : ℕ) (ul : List V3)
    (hP : Packing V) (hs : saturated V) (hk : barV V k ul) :
    ∃ K : Set (Set V3), K.Finite ∧
      voronoiList V ul = (affineSpan ℝ (voronoiList V ul) : Set V3) ∩ ⋂₀ K ∧
      (∀ a ∈ K, ∃ v ∈ V, v ≠ hdV ul ∧ (a = bisLe v (hdV ul) ∨ a = bisLe (hdV ul) v)) ∧
      ∀ K' ⊂ K, voronoiList V ul ⊂
        (affineSpan ℝ (voronoiList V ul) : Set V3) ∩ ⋂₀ K' := by
  sorry

/-- Rogers.hl:192 `REAL_LINE_BOUNDED`. -/
theorem REAL_LINE_BOUNDED (a b : ℝ) (h : ∀ t : ℝ, t * a ≤ b) : a = 0 := by
  by_contra hne
  have h1 : (b + 1) / a * a = b + 1 := by field_simp
  linarith [h ((b + 1) / a), h1]

/-- Rogers.hl:202 `REAL_NEG_LE_RMUL`. -/
theorem REAL_NEG_LE_RMUL (x y z : ℝ) (hz : z < 0) : x ≤ y ↔ y * z ≤ x * z := by
  constructor
  · intro h
    exact mul_le_mul_of_nonpos_right h hz.le
  · intro h
    by_contra hxy
    exact absurd (mul_lt_mul_of_neg_right (not_le.mp hxy) hz) (not_lt.2 h)

/-- Rogers.hl:212 `HALFSPACE_EQ`: equality of linear halfspaces. -/
theorem HALFSPACE_EQ (a : V3) (b : ℝ) (c : V3) (d : ℝ) :
    {x : V3 | a ⬝ᵥ x ≤ b} = {x : V3 | c ⬝ᵥ x ≤ d} ↔
      (∃ t : ℝ, c = t • a ∧ d = t * b ∧ 0 < t) ∨
        (a = 0 ∧ c = 0 ∧ ((0 ≤ b ∧ 0 ≤ d) ∨ (b < 0 ∧ d < 0))) := by
  sorry

/-- Rogers.hl:397 `HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS`. -/
theorem HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a v w : V3) (b : ℝ) (ha : a ≠ 0)
    (h : {x : V3 | a ⬝ᵥ x ≤ b} = bisLe v w) :
    {x : V3 | a ⬝ᵥ x = b} = bis v w := by
  have e0 : ∀ y : V3, ((2 : ℝ) • (w - v)) ⬝ᵥ y = 2 * ((w - v) ⬝ᵥ y) :=
    fun y => smul_dotProduct 2 ((w - v : V3) : Fin 3 → ℝ) (y : Fin 3 → ℝ)
  have h2 : {x : V3 | a ⬝ᵥ x ≤ b} =
    {y : V3 | ((2 : ℝ) • (w - v)) ⬝ᵥ y ≤ w ⬝ᵥ w - v ⬝ᵥ v} := by
    rw [h, BIS_LE_EQ_HALFSPACE]
    ext y
    simp only [Set.mem_setOf_eq, e0]
  rcases (HALFSPACE_EQ a b ((2 : ℝ) • (w - v)) (w ⬝ᵥ w - v ⬝ᵥ v)).1 h2 with
    hcase | hcase
  · obtain ⟨t, ht1, ht2, ht3⟩ := hcase
    have e1 : ∀ y : V3, 2 * ((w - v) ⬝ᵥ y) = t * (a ⬝ᵥ y) := by
      intro y
      have e11 : ((2 : ℝ) • (w - v)) ⬝ᵥ y =
          t * ((a : Fin 3 → ℝ) ⬝ᵥ (y : Fin 3 → ℝ)) := by
        rw [ht1]
        exact smul_dotProduct t _ _
      rw [← e11, e0]
    have e2 : t * b = w ⬝ᵥ w - v ⬝ᵥ v := ht2.symm
    rw [BIS_EQ_HYPERPLANE v w]
    ext y
    simp only [Set.mem_setOf_eq, e1, ← e2]
    constructor
    · intro hh
      rw [hh]
    · intro hh
      exact mul_left_cancel₀ (ne_of_gt ht3) hh
  · exact absurd hcase.1 ha

/-- Rogers.hl:417 `FACET_OF_POLYHEDRON_EXPLICIT_BIS`. -/
theorem FACET_OF_POLYHEDRON_EXPLICIT_BIS (V : Set V3) (K : Set (Set V3)) (s : Set V3)
    (u : V3) (h1 : K.Finite) (h2 : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ K)
    (h3 : ∀ a ∈ K, ∃ v ∈ V, v ≠ u ∧ (a = bisLe v u ∨ a = bisLe u v))
    (h4 : ∀ K' ⊂ K, s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ K') :
    ∀ c : Set V3, FacetOf c s ↔
      ∃ v ∈ V, (bisLe v u ∈ K ∨ bisLe u v ∈ K) ∧ c = s ∩ bis u v := by
  sorry

/-! ## Rogers.hl:523-825 — facets of Voronoi lists, existence of barV lists -/

/-- Rogers.hl:523 `IDBEZAL`: facets of a Voronoi list of dimension `< 3`. -/
theorem IDBEZAL (V : Set V3) (ul : List V3) (k : ℕ) (F : Set V3) (hs : saturated V)
    (hP : Packing V) (hbar : barV V k ul) (h3 : k < 3) :
    FacetOf F (voronoiList V ul) ↔
      ∃ vl : List V3, F = voronoiList V vl ∧ barV V (k + 1) vl ∧
        truncateSimplex k vl = ul := by
  sorry

/-- Rogers.hl:694 `VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS`. -/
theorem VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS (V : Set V3) (ul : List V3) (k : ℕ)
    (p : V3) (hP : Packing V) (hs : saturated V) (hbar : barV V k ul) (hk3 : k < 3)
    (hp : p ∈ voronoiList V ul) :
    voronoiList V ul =
      ⋃₀ {convexHull ℝ (insert p (voronoiList V vl)) | vl ∈ {vl : List V3 |
        barV V (k + 1) vl ∧ truncateSimplex k vl = ul}} := by
  sorry

/-- Rogers.hl:754 `NUMSEG_SUBSET_INDUCT`. -/
theorem NUMSEG_SUBSET_INDUCT (s : Set ℕ) (a b : ℕ) (ha : a ∈ s)
    (hstep : ∀ k, a ≤ k → k + 1 ≤ b → k ∈ s → k + 1 ∈ s) :
    Set.Icc a b ⊆ s := by
  intro m hm
  have key : ∀ n : ℕ, a ≤ n → n ≤ b → n ∈ s := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h1 h2
      rcases Nat.eq_or_lt_of_le h1 with heq | hlt
      · subst heq
        exact ha
      · have h5 : n - 1 ∈ s := ih (n - 1) (by omega) (by omega) (by omega)
        have h6 : n - 1 + 1 = n := by omega
        rw [← h6]
        exact hstep (n - 1) (by omega) (by omega) h5
  exact key m hm.1 hm.2

/-- Rogers.hl:778 `BARV_EXISTS`: a `barV V k` list extends to `barV V (k+1)`. -/
theorem BARV_EXISTS (V : Set V3) (wl : List V3) (k : ℕ) (hP : Packing V)
    (hs : saturated V) (hk3 : k < 3) (hbar : barV V k wl) :
    ∃ vl : List V3, barV V (k + 1) vl ∧ truncateSimplex k vl = wl := by
  sorry

/-- Rogers.hl:803 `BARV_EXISTS_ALT`. -/
theorem BARV_EXISTS_ALT (V : Set V3) (k : ℕ) (hP : Packing V) (hs : saturated V)
    (hk3 : k ≤ 3) : ∃ ul : List V3, barV V k ul := by
  sorry

/-! ## Rogers.hl:826-1255 — GLTVHUM (Rogers simplex covering) -/

/-- Rogers.hl:826 `GLTVHUM_lemma1`. -/
theorem GLTVHUM_lemma1 (V : Set V3) (ul : List V3) (j : ℕ) (hP : Packing V)
    (hs : saturated V) (hj : j < 3) (hbar : barV V j ul) :
    {k : ℕ | k ∈ (Finset.Icc j 3 : Set ℕ) ∧ voronoiList V ul =
      ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j (k - 1)} ∪
        voronoiList V vl) | vl ∈ {vl : List V3 |
        barV V k vl ∧ truncateSimplex j vl = ul}}} = (Finset.Icc j 3 : Set ℕ) := by
  sorry

/-- Rogers.hl:1152 `GLTVHUM`: the closed Voronoi cell of `u0` is covered by
the Rogers simplices rooted at `u0`. -/
theorem GLTVHUM (V : Set V3) (u0 p : V3) (h : Packing V ∧ saturated V) (hu0 : u0 ∈ V) :
    p ∈ voronoiClosed V u0 ↔
      ∃ vl : List V3, barV V 3 vl ∧ p ∈ rogers V vl ∧ truncateSimplex 0 vl = [u0] :=
  GLTVHUM_concl V u0 p h hu0

/-! ## Rogers.hl:1256-1681 — Voronoi cells, ODIGPXU, omega/truncate kit -/

/-- Rogers.hl:1256 `VORONOI_CLOSED_EQ_LEMMA`. -/
theorem VORONOI_CLOSED_EQ_LEMMA (V : Set V3) (u v : V3) (hP : Packing V) (hu : u ∈ V)
    (hv : v ∈ V) (h : voronoiClosed V u = voronoiClosed V v) : u = v := by
  have h1 := (CENTER_IN_VORONOI_CELL V u).1
  rw [h] at h1
  have h3 := h1 u hu
  have h4 : dist u v ≤ 0 := by simpa using h3
  exact dist_le_zero.mp h4

/-- Auxiliary: `closest_point K x = x` when `x IN K`
(closest_point is a selection; used for `OMEGA_LIST_N_EQ`). -/
theorem CLOSEST_POINT_MEM (K : Set V3) (x : V3) (hx : x ∈ K) : closestPoint K x = x := by
  have h := Classical.epsilon_spec
    (p := fun y : V3 => y ∈ K ∧ ∀ z ∈ K, dist x y ≤ dist x z)
    ⟨x, hx, by intro z _; rw [dist_self x]; exact dist_nonneg⟩
  have h2 : dist x (closestPoint K x) ≤ 0 :=
    (h.2 x hx).trans (by rw [dist_self x])
  exact (dist_le_zero.mp h2).symm

/-- Rogers.hl:1342 `OMEGA_LIST_N_EQ`. -/
theorem OMEGA_LIST_N_EQ (V : Set V3) (ul : List V3) (i : ℕ)
    (h : omegaListN V ul i ∈ voronoiList V (truncateSimplex (i + 1) ul)) :
    omegaListN V ul (i + 1) = omegaListN V ul i := by
  show closestPoint (voronoiList V (truncateSimplex (i + 1) ul))
    (omegaListN V ul i) = omegaListN V ul i
  exact CLOSEST_POINT_MEM _ _ h

/-- Rogers.hl:1267 `ODIGPXU_lemma`. -/
theorem ODIGPXU_lemma (P f f' : Set V3) (p0 p q : V3) (t s : ℝ) (hP : polyhedron P)
    (hp0 : p0 ∈ P) (hf : p0 ∉ f ∪ f') (h1 : FacetOf f P) (h2 : FacetOf f' P)
    (hp : p ∈ f) (hq : q ∈ f') (ht : 0 < t) (hs : 0 < s)
    (heq : (1 - t) • p0 + t • p = (1 - s) • p0 + s • q) : s ≤ t := by
  sorry

/-- Rogers.hl:1321 `ODIGPXU`. -/
theorem ODIGPXU (P f f' : Set V3) (p0 p q : V3) (t s : ℝ) (hP : polyhedron P)
    (hp0 : p0 ∈ P) (hf : p0 ∉ f ∪ f') (h1 : FacetOf f P) (h2 : FacetOf f' P)
    (hp : p ∈ f) (hq : q ∈ f') (ht : 0 < t) (hs : 0 < s)
    (heq : (1 - t) • p0 + t • p = (1 - s) • p0 + s • q) : s = t :=
  le_antisymm (ODIGPXU_lemma P f f' p0 p q t s hP hp0 hf h1 h2 hp hq ht hs heq)
    (ODIGPXU_lemma P f' f p0 q p s t hP hp0 (by rw [Set.union_comm]; exact hf) h2 h1
      hq hp hs ht heq.symm)

/-- Rogers.hl:1360 `OMEGA_LIST_N_IN_FACET`. -/
theorem OMEGA_LIST_N_IN_FACET (V : Set V3) (ul : List V3) (k i : ℕ) (hP : Packing V)
    (hs : saturated V) (hbar : barV V k ul) (hik : i < k) :
    ∃ F : Set V3, FacetOf F (voronoiList V (truncateSimplex i ul)) ∧
      voronoiList V (truncateSimplex (i + 1) ul) = F ∧
      ∀ j, i < j → j ≤ k → omegaListN V ul j ∈ F := by
  sorry

/-- Rogers.hl:1462 `VORONOI_SET_SUBSET`. -/
theorem VORONOI_SET_SUBSET (V : Set V3) (s t : Set V3) (h : s ⊆ t) :
    voronoiSet V t ⊆ voronoiSet V s := by
  intro x hx
  simp only [voronoiSet, Set.mem_sInter] at hx ⊢
  intro A hA
  obtain ⟨v, hv, rfl⟩ := hA
  exact hx _ ⟨v, h hv, rfl⟩

private theorem initialSublist_truncate_truncate (ul : List V3) {i j : ℕ} (hij : i ≤ j)
    (hj : j + 1 ≤ ul.length) :
    initialSublist (truncateSimplex i ul) (truncateSimplex j ul) := by
  rw [← TRUNCATE_TRUNCATE_SIMPLEX ul i j hij hj]
  exact ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST i (truncateSimplex i (truncateSimplex j ul))
    (truncateSimplex j ul)).mp ⟨rfl, by
      rw [LENGTH_TRUNCATE_SIMPLEX j ul hj]; omega⟩).1

private theorem voronoiList_initialSublist_mono (V : Set V3) (t u : List V3)
    (h : initialSublist t u) : voronoiList V u ⊆ voronoiList V t :=
  VORONOI_SET_SUBSET V (setOfList t) (setOfList u) (SET_OF_LIST_INITIAL_SUBLIST_SUBSET h)

/-- Rogers.hl:1433 `OMEGA_LIST_N_IN_VORONOI_LIST_GEN`. -/
theorem OMEGA_LIST_N_IN_VORONOI_LIST_GEN (V : Set V3) (ul : List V3) (k i j : ℕ)
    (hP : Packing V) (hs : saturated V) (hbar : barV V k ul) (hij : i ≤ j) (hjk : j ≤ k) :
    omegaListN V ul j ∈ voronoiList V (truncateSimplex i ul) :=
  voronoiList_initialSublist_mono V (truncateSimplex i ul) (truncateSimplex j ul)
    (initialSublist_truncate_truncate ul hij (by have := hbar.1; omega))
    (OMEGA_LIST_N_IN_VORONOI_LIST V ul k j hbar hjk)

/-- Rogers.hl:1468 `TRUNCATE_SIMPLEX_SUBSET`. (HOL states this over generic
`(A)list`; the local truncate kit is `List V3`-typed.) -/
theorem TRUNCATE_SIMPLEX_SUBSET (ul : List V3) (i j : ℕ) (hji : j ≤ i)
    (hi : i + 1 ≤ ul.length) :
    setOfList (truncateSimplex j ul) ⊆ setOfList (truncateSimplex i ul) := by
  rw [← TRUNCATE_TRUNCATE_SIMPLEX ul j i hji hi]
  exact SET_OF_LIST_INITIAL_SUBLIST_SUBSET
    (((TRUNCATE_SIMPLEX_INITIAL_SUBLIST j (truncateSimplex j (truncateSimplex i ul))
      (truncateSimplex i ul)).mp ⟨rfl, by
        rw [LENGTH_TRUNCATE_SIMPLEX i ul hi]; omega⟩).1)

/-- Rogers.hl:1484 `OMEGA_LIST_N_EQ_GEN`. -/
theorem OMEGA_LIST_N_EQ_GEN (V : Set V3) (ul : List V3) (k i j : ℕ) (hP : Packing V)
    (hs : saturated V) (hbar : barV V k ul) (hij : i < j) (hjk : j ≤ k)
    (hmem : omegaListN V ul i ∈ voronoiList V (truncateSimplex j ul)) :
    omegaListN V ul (i + 1) = omegaListN V ul i := by
  refine OMEGA_LIST_N_EQ V ul i ?_
  exact voronoiList_initialSublist_mono V (truncateSimplex (i + 1) ul)
    (truncateSimplex j ul)
    (initialSublist_truncate_truncate ul (by omega) (by have := hbar.1; omega)) hmem

/-- Rogers.hl:1551 `SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET`. (V3-typed kit.) -/
theorem SET_OF_LIST_TRUNCATE_SIMPLEX_SUBSET (ul : List V3) (k : ℕ)
    (h : k + 1 ≤ ul.length) : setOfList (truncateSimplex k ul) ⊆ setOfList ul :=
  SET_OF_LIST_INITIAL_SUBLIST_SUBSET
    ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST k (truncateSimplex k ul) ul).mp ⟨rfl, h⟩).1

/-- Rogers.hl:1641 `VORONOI_LIST_AFF_DIM`. -/
theorem VORONOI_LIST_AFF_DIM (V : Set V3) (ul : List V3) (k i : ℕ) (hbar : barV V k ul)
    (hi : i ≤ k) : affDim (voronoiList V (truncateSimplex i ul)) = 3 - i :=
  AFF_DIM_VORONOI_LIST V (truncateSimplex i ul) i
    (TRUNCATE_SIMPLEX_BARV V i k ul hbar hi)

/-- Rogers.hl:1499 `CARD_LE_3`. -/
theorem CARD_LE_3 {α : Type*} (s : Set α) (h1 : s ≠ ∅) (h2 : s.Finite)
    (h3 : Nat.card s ≤ 3) : ∃ x y z : α, s = {x, y, z} := by
  classical
  haveI := h2.fintype
  have hF : (h2.toFinset : Set α) = s := h2.coe_toFinset
  have hmem : ∀ a : α, a ∈ h2.toFinset ↔ a ∈ s := fun a => by
    rw [show (a ∈ h2.toFinset) ↔ (a ∈ (h2.toFinset : Set α)) from Iff.rfl, hF]
  have hle : h2.toFinset.card ≤ 3 := by
    have hct : h2.toFinset.card = Nat.card s := by
      rw [h2.card_toFinset, Nat.card_eq_fintype_card]
    omega
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h1
  have hxF : x ∈ h2.toFinset := (hmem x).mpr hx
  have hins : h2.toFinset = insert x (h2.toFinset.erase x) :=
    (Finset.insert_erase hxF).symm
  have hG : h2.toFinset.erase x = ∅ ∨ (∃ y : α, h2.toFinset.erase x = {y}) ∨
      (∃ y z : α, h2.toFinset.erase x = {y, z} ∧ y ≠ z) := by
    have hgc := Finset.card_erase_of_mem hxF
    rcases Nat.lt_or_ge (h2.toFinset.erase x).card 1 with hc0 | hc1
    · have he : (h2.toFinset.erase x).card = 0 := by omega
      left
      exact Finset.card_eq_zero.mp he
    rcases Nat.lt_or_ge (h2.toFinset.erase x).card 2 with hc1' | hc2
    · right
      have he : (h2.toFinset.erase x).card = 1 := by omega
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp he
      exact Or.inl ⟨y, hy⟩
    · right
      have he : (h2.toFinset.erase x).card = 2 := by omega
      obtain ⟨y, z, hyz, hcard2⟩ := Finset.card_eq_two.mp he
      exact Or.inr ⟨y, z, hcard2, hyz⟩
  rcases hG with hG0 | ⟨y, hG2⟩ | ⟨y, z, hG2, -⟩
  · refine ⟨x, x, x, ?_⟩
    rw [← hF, hins, hG0]
    simp
  · refine ⟨x, y, y, ?_⟩
    rw [← hF, hins, hG2]
    simp
  · refine ⟨x, y, z, ?_⟩
    rw [← hF, hins, hG2]
    simp

/-! ## Rogers.hl:1521-1681 — dimension/coplanarity; Rogers.hl:1682 DUUNHOR;
Rogers.hl:3106-3851 — linear algebra and circumcenter kit -/

/-- Rogers.hl:1521 `AFF_DIM_LE_2_IMP_COPLANAR`. -/
theorem AFF_DIM_LE_2_IMP_COPLANAR (s : Set V3) (h : affDim s ≤ 2) : Coplanar s := by
  sorry

/-- Rogers.hl:1559 `ROGERS_AFF_DIM_FULL`. -/
theorem ROGERS_AFF_DIM_FULL (V : Set V3) (ul : List V3) (hbar : barV V 3 ul)
    (hdim : affDim (rogers V ul) = 3) :
    ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → omegaListN V ul i ≠ omegaListN V ul j := by
  sorry

/-- Rogers.hl:1657 `AFF_DIM_FINITE_UNION_LE`. -/
theorem AFF_DIM_FINITE_UNION_LE (s t : Set V3) (hs : s.Finite) :
    affDim (s ∪ t) ≤ (Nat.card s : ℤ) + affDim t := by
  sorry

/-- Rogers.hl:1682 `DUUNHOR`: distinct Rogers simplices meet in a coplanar
set. (The `packing`/`saturated` hypotheses are unused here.) -/
theorem DUUNHOR (V : Set V3) (ul vl : List V3) (hP : Packing V) (hs : saturated V)
    (hul : barV V 3 ul) (hvl : barV V 3 vl) (hne : rogers V ul ≠ rogers V vl) :
    Coplanar (rogers V ul ∩ rogers V vl) :=
  DUUNHOR_concl V ul vl hul hvl hne

/-- Rogers.hl:3106 `AFFINE_INDEPENDENT_IMP_INDEPENDENT`. -/
theorem AFFINE_INDEPENDENT_IMP_INDEPENDENT (S : Set V3) (hS : ¬affineDependent S) :
    ∀ x ∈ S, LinearIndependent ℝ (fun y : (S \ {x} : Set V3) => (y : V3) - x) := by
  sorry

/-- Rogers.hl:3141 `ORTHOGONAL_TO_SPAN_EXISTS`. -/
theorem ORTHOGONAL_TO_SPAN_EXISTS (s t : Set V3)
    (h1 : s ⊆ (Submodule.span ℝ t : Set V3))
    (h2 : Module.finrank ℝ (Submodule.span ℝ s) <
      Module.finrank ℝ (Submodule.span ℝ t)) :
    ∃ v : V3, v ≠ 0 ∧ v ∈ Submodule.span ℝ t ∧ ∀ x ∈ s, x ⬝ᵥ v = 0 := by
  sorry

/-- Rogers.hl:3224 `INDEPENDENT_EXPLICIT_NUMSEG`. -/
theorem INDEPENDENT_EXPLICIT_NUMSEG (v : ℕ → V3) (f : ℕ → ℝ) (n : ℕ)
    (h1 : ∀ i j : ℕ, i ∈ Finset.Icc 1 n → j ∈ Finset.Icc 1 n → v i = v j → i = j)
    (h2 : LinearIndependent ℝ (fun i : (Finset.Icc (1 : ℕ) n : Finset ℕ) => v (i : ℕ)))
    (h3 : (∑ i ∈ Finset.Icc (1 : ℕ) n, f i • v (i : ℕ)) = 0) :
    ∀ i ∈ Finset.Icc (1 : ℕ) n, f i = 0 := by
  sorry

/-- Rogers.hl:3286 `ORTHOGONAL_TO_ALL_IMP_ZERO`. -/
theorem ORTHOGONAL_TO_ALL_IMP_ZERO (v : V3) (s : Set V3)
    (h1 : v ∈ Submodule.span ℝ s) (h2 : ∀ x ∈ s, v ⬝ᵥ x = 0) : v = 0 := by
  sorry

/-- Rogers.hl:3325 `UNIQUE_SOLUTION_lemma`. -/
theorem UNIQUE_SOLUTION_lemma (S : Set V3) (b : V3 → ℝ)
    (hS : LinearIndependent ℝ (fun x : S => (x : V3))) :
    ∃! p : V3, p ∈ Submodule.span ℝ S ∧ ∀ x ∈ S, p ⬝ᵥ x = b x := by
  sorry

/-- Rogers.hl:3609 `UNIQUE_SOLUTION_AFFINE_INDEPENDENT`. -/
theorem UNIQUE_SOLUTION_AFFINE_INDEPENDENT (S : Set V3) (b : V3 → ℝ)
    (h1 : S ≠ ∅) (h2 : ¬affineDependent S) :
    ∃! p : V3, p ∈ (affineSpan ℝ S : Set V3) ∧
      ∀ x ∈ S, ∀ y ∈ S, p ⬝ᵥ (x - y) = b x - b y := by
  sorry

/-- Rogers.hl:3732 `QXSKIIT`: unique interpolation on the affine hull. -/
theorem QXSKIIT {A : Type} (vf : A → V3) (b : A → ℝ)
    (h1 : (vf '' (Set.univ : Set A)).Finite)
    (h2 : ¬affineDependent (vf '' (Set.univ : Set A)))
    (h3 : ∀ i j : A, vf i = vf j → b i = b j) :
    ∃! p : V3, p ∈ (affineSpan ℝ (vf '' (Set.univ : Set A)) : Set V3) ∧
      ∀ i j : A, p ⬝ᵥ (vf i - vf j) = b i - b j :=
  QXSKIIT_concl vf b h1 h2 h3

/-- Rogers.hl:3802 `CIRCUMCENTER_lemma`. -/
theorem CIRCUMCENTER_lemma (S : Set V3) (h1 : S ≠ ∅) (h2 : ¬affineDependent S) :
    ∃! p : V3, p ∈ (affineSpan ℝ S : Set V3) ∧
      ∀ x ∈ S, ∀ y ∈ S, dist p x = dist p y := by
  sorry

/-- Rogers.hl:3816 `CIRCUMCENTER_LEMMA`. -/
theorem CIRCUMCENTER_LEMMA (S : Set V3) (h1 : S ≠ ∅) (h2 : ¬affineDependent S) :
    ∃! p : V3, p ∈ (affineSpan ℝ S : Set V3) ∧ ∃ c : ℝ, ∀ w ∈ S, c = dist p w := by
  sorry

/-- Rogers.hl:3843 `OAPVION1`: the circumcenter lies on the affine hull. -/
theorem OAPVION1 (S : Set V3) (h1 : S ≠ ∅) (h2 : ¬affineDependent S) :
    circumcenter S ∈ (affineSpan ℝ S : Set V3) :=
  OAPVION1_concl S h1 h2

/-- Rogers.hl:3851 `OAPVION2`: all points of `S` are at circumradius
distance from the circumcenter. -/
theorem OAPVION2 (S : Set V3) (h2 : ¬affineDependent S) :
    ∀ w ∈ S, radV S = dist (circumcenter S) w :=
  OAPVION2_concl S h2

/-! ## Rogers.hl:3892-4340 — circumcenter characterisation, MHFTTZN -/

/-- Rogers.hl:3892 `OAPVION3`: the circumcenter is the unique equidistant
point on the affine hull. -/
theorem OAPVION3 (S : Set V3) (h2 : ¬affineDependent S) :
    ∀ p : V3, p ∈ (affineSpan ℝ S : Set V3) → (∃ c : ℝ, ∀ w ∈ S, dist p w = c) →
      p = circumcenter S :=
  OAPVION3_concl S h2

/-- Rogers.hl:3935 `CIRCUMCENTER_1`. -/
theorem CIRCUMCENTER_1 (x : V3) : circumcenter {x} = x := by
  have h := Classical.epsilon_spec
    (p := fun v : V3 => v ∈ (affineSpan ℝ ({x} : Set V3) : Set V3) ∧
      ∃ c : ℝ, ∀ w ∈ ({x} : Set V3), c = dist v w)
    ⟨x, SetLike.mem_coe.mpr (mem_affineSpan ℝ (Set.mem_singleton x)), 0, by simp⟩
  exact (AffineSubspace.mem_affineSpan_singleton ℝ V3).mp (SetLike.mem_coe.mpr h.1)

/-- Rogers.hl:3945 `CIRCUMCENTER_NOT_EQ`: a nondegenerate finite set (here:
`1 < CARD S`) contains none of its own circumcenter. -/
theorem CIRCUMCENTER_NOT_EQ (S : Set V3) (h1 : ¬affineDependent S)
    (h2 : 1 < Nat.card S) : ∀ x ∈ S, circumcenter S ≠ x := by
  intro x hx hcc
  have hwne : ∃ w ∈ S, w ≠ x := by
    by_contra hcon
    have hsub : S ⊆ ({x} : Set V3) := by
      intro y hy
      by_contra hne
      exact hcon ⟨y, hy, hne⟩
    have hfin : ({x} : Set V3).Finite := Set.finite_singleton x
    have hcard : Nat.card S ≤ Nat.card ({x} : Set V3) := Nat.card_mono hfin hsub
    have hone : Nat.card ({x} : Set V3) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((Set.mem_singleton_iff.1 a.property).trans
        (Set.mem_singleton_iff.2 b.property).symm)⟩, ⟨⟨x, Set.mem_singleton x⟩⟩⟩
    omega
  obtain ⟨w, hwS, hwx⟩ := hwne
  have hrw := OAPVION2_concl S h1 w hwS
  have hrx := OAPVION2_concl S h1 x hx
  rw [hcc] at hrw hrx
  have hzw : dist x w = 0 := by rw [← hrw, hrx, dist_self]
  exact hwx (dist_eq_zero.mp hzw).symm

/-- Rogers.hl:3972 `CIRCUMCENTER_TRANSLATION`. -/
theorem CIRCUMCENTER_TRANSLATION (s : Set V3) (a : V3) (h1 : s ≠ ∅)
    (h2 : ¬affineDependent s) :
    circumcenter ((fun x : V3 => a + x) '' s) = a + circumcenter s := by
  sorry

/-- Rogers.hl:4002 `RADV_TRANSLATION`. -/
theorem RADV_TRANSLATION (s : Set V3) (a : V3) (h : ¬affineDependent s) :
    radV ((fun x : V3 => a + x) '' s) = radV s := by
  sorry

/-- Rogers.hl:4046 `AFF_INTER_SUBSET_INTER_AFF`. -/
theorem AFF_INTER_SUBSET_INTER_AFF (s t : Set V3) :
    (affineSpan ℝ (s ∩ t) : Set V3) ⊆
      (affineSpan ℝ s : Set V3) ∩ (affineSpan ℝ t : Set V3) := by
  intro x hx
  exact ⟨SetLike.le_def.mp (affineSpan_mono ℝ Set.inter_subset_left) hx,
    SetLike.le_def.mp (affineSpan_mono ℝ Set.inter_subset_right) hx⟩

/-- Rogers.hl:4053 `MHFTTZN_lemma`. -/
theorem MHFTTZN_lemma (V : Set V3) (ul : List V3) (k : ℕ) (hP : Packing V)
    (hbar : barV V k ul) :
    (affineSpan ℝ (voronoiList V ul) : Set V3) =
      ⋂₀ {bis (hdV ul) u | u ∈ setOfList ul} := by
  sorry

/-- Rogers.hl:4340 `MHFTTZN_lemma2`. -/
theorem MHFTTZN_lemma2 (V : Set V3) (ul : List V3) (k : ℕ) (hP : Packing V)
    (hbar : barV V k ul) :
    affDim (setOfList ul) = (k : ℤ) ∧
      ∀ u v : V3, u ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) →
        v ∈ (affineSpan ℝ (setOfList ul) : Set V3) →
          (u - circumcenter (setOfList ul)) ⬝ᵥ (v - circumcenter (setOfList ul)) = 0 := by
  sorry

/-- Rogers.hl:4862 `MHFTTZN1`. -/
theorem MHFTTZN1 (V : Set V3) (ul : List V3) (k : ℕ) (hP : Packing V)
    (hbar : barV V k ul) : affDim (setOfList ul) = (k : ℤ) :=
  (MHFTTZN_lemma2 V ul k hP hbar).1

/-- Rogers.hl:4871 `MHFTTZN2`. -/
theorem MHFTTZN2 (V : Set V3) (ul : List V3) (k : ℕ) (hP : Packing V)
    (hbar : barV V k ul) :
    ∀ p : V3, p ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) ↔
      ∀ u ∈ setOfList ul, p ∈ bis (hdV ul) u := by
  rw [MHFTTZN_lemma V ul k hP hbar]
  intro p
  simp only [Set.mem_sInter]
  constructor
  · intro hp u hu
    exact hp _ ⟨u, hu, rfl⟩
  · intro hp A hA
    obtain ⟨u, hu, rfl⟩ := hA
    exact hp u hu

/-- Rogers.hl:4881 `MHFTTZN3`. -/
theorem MHFTTZN3 (V : Set V3) (ul : List V3) (k : ℕ) (hP : Packing V)
    (hbar : barV V k ul) :
    (affineSpan ℝ (voronoiList V ul) : Set V3) ∩
      (affineSpan ℝ (setOfList ul) : Set V3) = {circumcenter (setOfList ul)} := by
  sorry

/-- Rogers.hl:4985 `MHFTTZN4`. -/
theorem MHFTTZN4 (V : Set V3) (ul : List V3) (k : ℕ) (u v : V3) (hP : Packing V)
    (hbar : barV V k ul)
    (hu : u ∈ (affineSpan ℝ (voronoiList V ul) : Set V3))
    (hv : v ∈ (affineSpan ℝ (setOfList ul) : Set V3)) :
    (u - circumcenter (setOfList ul)) ⬝ᵥ (v - circumcenter (setOfList ul)) = 0 :=
  (MHFTTZN_lemma2 V ul k hP hbar).2 u v hu hv

/-- Rogers.hl:5003 `ARCV_GT_PI2`. -/
theorem ARCV_GT_PI2 (p u v : V3) :
    Real.pi / 2 < arcV p u v ↔ Real.cos (arcV p u v) < 0 := by
  have hden : 0 ≤ dist u p * dist v p := mul_nonneg dist_nonneg dist_nonneg
  have hcs : |(u - p) ⬝ᵥ (v - p)| ≤ dist u p * dist v p := by
    have h1 := norm_inner_le_norm (𝕜 := ℝ) (u - p) (v - p)
    rw [inner_eq_dot (u - p) (v - p), Real.norm_eq_abs, ← dist_eq_norm,
      ← dist_eq_norm] at h1
    exact h1
  rcases abs_le.mp hcs with ⟨hn1, hn2⟩
  set q : ℝ := (u - p) ⬝ᵥ (v - p) / (dist u p * dist v p) with hqdef
  have hq1 : -(1 : ℝ) ≤ q := by
    by_cases h0 : dist u p * dist v p = 0
    · rw [hqdef, h0, div_zero]
      norm_num
    · rw [hqdef, le_div_iff₀ (lt_of_le_of_ne hden (Ne.symm h0))]
      linarith
  have hq2 : q ≤ 1 := by
    by_cases h0 : dist u p * dist v p = 0
    · rw [hqdef, h0, div_zero]
      norm_num
    · rw [hqdef, div_le_iff₀ (lt_of_le_of_ne hden (Ne.symm h0))]
      linarith
  show Real.pi / 2 < Real.arccos q ↔ Real.cos (Real.arccos q) < 0
  rw [Real.cos_arccos hq1 hq2]
  have hkey : Real.pi / 2 < Real.arccos q ↔ Real.arccos (-q) < Real.pi / 2 := by
    rw [Real.arccos_neg]
    constructor <;> intro h <;> linarith
  exact hkey.trans ((Real.arccos_lt_pi_div_two (x := -q)).trans (by simp))

/-- Rogers.hl:5022 `XYOFCGX_lemma0`. -/
theorem XYOFCGX_lemma0 (V S : Set V3) (p w : V3) (hV : Packing V) (hSV : S ⊆ V)
    (hS : ¬affineDependent S) (hp : p = circumcenter S) (hr : radV S < Real.sqrt 2)
    (hw : w ∈ V \ S) (hdw : dist p w ≤ radV S) (hcard : 1 < Nat.card S) :
    (∀ u ∈ S, Real.pi / 2 < arcV p w u) ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Real.pi / 2 < arcV p u v := by
  sorry

/-- Rogers.hl:5180 `CARD_1_IMP_SING`. -/
theorem CARD_1_IMP_SING {α : Type*} (s : Set α) (h1 : s.Finite) (h2 : Nat.card s = 1) :
    ∃ x : α, s = {x} := by
  haveI := h1.fintype
  have hF : (h1.toFinset : Set α) = s := h1.coe_toFinset
  have hc : h1.toFinset.card = 1 := by
    have hct : h1.toFinset.card = Nat.card s := by
      rw [h1.card_toFinset, Nat.card_eq_fintype_card]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
  refine ⟨x, ?_⟩
  rw [← hF, hx]
  simp

/-! ## Rogers.hl:5195-5365 — XYOFCGX pair comparisons, angle/azim identities -/

/-- Rogers.hl:5195 `XYOFCGX_1`. -/
theorem XYOFCGX_1 (V S : Set V3) (p : V3) (hV : Packing V) (hSV : S ⊆ V)
    (hS : ¬affineDependent S) (hp : p = circumcenter S) (hr : radV S < Real.sqrt 2)
    (hcard : Nat.card S ≤ 1) :
    ∀ u ∈ S, ∀ v ∈ V \ S, dist v p > dist u p := by
  sorry

/-- Rogers.hl:5222 `CIRCUMCENTER_2`. (HOL `midpoint (a,b)`; Mathlib
`midpoint ℝ a b`.) -/
theorem CIRCUMCENTER_2 (a b : V3) : circumcenter {a, b} = midpoint ℝ a b := by
  sorry

/-- Rogers.hl:5243 `CARD_2_IMP_DOUBLE`. -/
theorem CARD_2_IMP_DOUBLE {α : Type*} (s : Set α) (h1 : s.Finite) (h2 : Nat.card s = 2) :
    ∃ a b : α, s = {a, b} ∧ a ≠ b := by
  haveI := h1.fintype
  have hF : (h1.toFinset : Set α) = s := h1.coe_toFinset
  have hc : h1.toFinset.card = 2 := by
    have hct : h1.toFinset.card = Nat.card s := by
      rw [h1.card_toFinset, Nat.card_eq_fintype_card]
    omega
  obtain ⟨x, y, hxy, hcard⟩ := Finset.card_eq_two.mp hc
  exact ⟨x, y, by rw [← hF, hcard]; simp, hxy⟩

/-- Rogers.hl:5252 `XYOFCGX_2`. -/
theorem XYOFCGX_2 (V S : Set V3) (p : V3) (hV : Packing V) (hSV : S ⊆ V)
    (hS : ¬affineDependent S) (hp : p = circumcenter S) (hr : radV S < Real.sqrt 2)
    (hcard : Nat.card S = 2) :
    ∀ u ∈ S, ∀ v ∈ V \ S, dist v p > dist u p := by
  sorry

/-- Rogers.hl:5292 `ANGLE_GT_PI2`. (HOL `angle (a,b,c)`; Mathlib
`EuclideanGeometry.angle a b c`, the angle at `b`.) -/
theorem ANGLE_GT_PI2 (a b c : V3) :
    Real.pi / 2 < EuclideanGeometry.angle a b c ↔ (a - b) ⬝ᵥ (c - b) < 0 := by
  sorry

/-- Rogers.hl:5348 `AZIM_COMPL_EXT`. -/
theorem AZIM_COMPL_EXT (v w a b : V3) :
    azim v w b a =
      if azim v w a b = 0 then 0 else 2 * Real.pi - azim v w a b := by
  sorry

/-- Rogers.hl:5365 `AZIM_EQ_SYM`. (Part A boundary; part B
(`STRICT_CYCLIC_IMP_FAN`, Rogers.hl:5373) in `Kepler/Text/PackingAuto7`.) -/
theorem AZIM_EQ_SYM (v w a b c : V3) :
    azim v w b a = azim v w c a ↔ azim v w a b = azim v w a c := by
  sorry

end Kepler.Text
