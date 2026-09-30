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

/-- Honest bootstrapping: a single packing point forms a `barV V 0` list
(the only initial sublist is the list itself; the cell is full-dimensional
by `AFF_DIM_VORONOI_CLOSED`). -/
private theorem p6_barV_0 (V : Set V3) (hP : Packing V) (v : V3) (hv : v ∈ V) :
    barV V 0 [v] := by
  refine ⟨by simp, ?_⟩
  rintro wl ⟨⟨yl, heq⟩, hpos⟩
  have hlen : wl.length + yl.length = 1 := by
    rw [← List.length_append, ← heq]; simp
  have hylen : yl.length = 0 := by omega
  have hyl : yl = [] := List.length_eq_zero_iff.mp hylen
  rw [hyl, List.append_nil] at heq
  subst heq
  refine ⟨by simp, ?_, ?_⟩
  · intro z hz
    have hz' : z = v := by simpa [setOfList] using hz
    rw [hz']
    exact hv
  · rw [VORONOI_LIST_SING]
    have hd3 := AFF_DIM_VORONOI_CLOSED V v hP
    simp only [List.length_cons, List.length_nil]
    omega

/-- Bridge (copy of the self-contained core of PackingAuto7's
`VORONOI_LIST_EQ_INTERS_BIS`, needed here before that file can be
imported): the Voronoi list is the closed cell of the head cut by the
bisectors against the remaining list points. -/
private theorem p6_voronoi_list_eq_inters_bis (V : Set V3) (ul : List V3)
    (hsub : setOfList ul ⊆ V) (h1 : 1 ≤ ul.length) :
    voronoiList V ul =
      voronoiClosed V (hdV ul) ∩ ⋂₀ {bis (hdV ul) u | u ∈ setOfList ul} := by
  have hhd_mem : hdV ul ∈ setOfList ul := by
    cases ul with
    | nil => exact absurd h1 (by simp)
    | cons a t => simp [setOfList, hdV]
  ext x
  constructor
  · intro hx
    have hx2 : x ∈ ⋂₀ {voronoiClosed V v | v ∈ setOfList ul} := hx
    rw [Set.mem_sInter] at hx2
    have hx' : ∀ w ∈ setOfList ul, ∀ w' ∈ V, dist x w ≤ dist x w' := by
      intro w hw w' hw'
      have hzw : x ∈ voronoiClosed V w := hx2 _ (by simpa using ⟨w, hw, rfl⟩)
      exact hzw w' hw'
    have hA : ∀ w ∈ V, dist x (hdV ul) ≤ dist x w := hx' (hdV ul) hhd_mem
    have hB : ∀ w ∈ setOfList ul, dist x (hdV ul) = dist x w := by
      intro w hw
      exact le_antisymm (hA w (hsub hw)) (hx' w hw (hdV ul) (hsub hhd_mem))
    refine ⟨hA, ?_⟩
    rw [Set.mem_sInter]
    intro T hT
    obtain ⟨u, hu, rfl⟩ := by simpa using hT
    exact hB u hu
  · intro hx
    have hx1 : ∀ w' ∈ V, dist x (hdV ul) ≤ dist x w' := hx.1
    have hxI : ∀ T ∈ {bis (hdV ul) u | u ∈ setOfList ul}, x ∈ T := hx.2
    show x ∈ ⋂₀ {voronoiClosed V v | v ∈ setOfList ul}
    rw [Set.mem_sInter]
    intro U hU
    obtain ⟨u, hu, rfl⟩ := by simpa using hU
    intro w hw
    have hC : dist x (hdV ul) = dist x u := hxI _ (by simpa using ⟨u, hu, rfl⟩)
    rw [← hC]
    exact hx1 w hw

/-- Rogers.hl:52 `KHEJKCI_GEN`: nested Voronoi lists are nested faces. -/
theorem KHEJKCI_GEN (V : Set V3) (k r : ℕ) (ul vl : List V3)
    (hs : saturated V) (hP : Packing V) (hk : barV V k ul) (hr : barV V r vl)
    (hinit : initialSublist ul vl) :
    FaceOf (voronoiList V vl) (voronoiList V ul) := by
  obtain ⟨h, t, hcons, -⟩ := BARV_CONS V k ul hk
  obtain ⟨yl, hvle⟩ := hinit
  have hvcons : vl = h :: (t ++ yl) := by rw [hvle, hcons]; rfl
  have hsubU : setOfList (h :: t) ⊆ V := by rw [← hcons]; exact BARV_SUBSET V k ul hk
  have hsubV : setOfList (h :: (t ++ yl)) ⊆ V := by
    rw [← hvcons]; exact BARV_SUBSET V r vl hr
  rw [hcons, hvcons,
    p6_voronoi_list_eq_inters_bis V (h :: t) hsubU (by simp),
    p6_voronoi_list_eq_inters_bis V (h :: (t ++ yl)) hsubV (by simp)]
  have hsubTT : setOfList (h :: t) ⊆ setOfList (h :: (t ++ yl)) := by
    intro u hu
    simp only [setOfList, List.mem_cons] at hu ⊢
    rcases hu with rfl | hut
    · exact Or.inl rfl
    · exact Or.inr (List.mem_append_left _ hut)
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    rw [Set.mem_sInter]
    rintro T ⟨u, hu, rfl⟩
    exact hx2 _ (by simpa using ⟨u, hsubTT hu, rfl⟩)
  · exact Convex.inter (CONVEX_VORONOI_CLOSED V (hdV (h :: (t ++ yl))))
      (convex_sInter fun T hT => by
        obtain ⟨u, -, rfl⟩ := by simpa using hT
        exact CONVEX_BIS _ _)
  · intro a b x ha hb hx hseg
    obtain ⟨ha1, -⟩ := ha
    obtain ⟨hb1, -⟩ := hb
    obtain ⟨hx1, hx2⟩ := hx
    have hstep : ∀ u ∈ setOfList (h :: (t ++ yl)), a ∈ bis h u ∧ b ∈ bis h u := by
      intro u hu
      have huV : u ∈ V := hsubV hu
      have hxT : x ∈ bis h u := hx2 _ (by simpa using ⟨u, hu, rfl⟩)
      exact (BIS_FACE_OF_BIS_LE h u).2.2 a b x (ha1 u huV) (hb1 u huV) hxT hseg
    refine ⟨⟨ha1, ?_⟩, ⟨hb1, ?_⟩⟩
    · rw [Set.mem_sInter]
      rintro T ⟨u, hu, rfl⟩
      exact (hstep u hu).1
    · rw [Set.mem_sInter]
      rintro T ⟨u, hu, rfl⟩
      exact (hstep u hu).2

/-- Rogers.hl:142 `KHEJKCI`: the Voronoi list is a face of the closed
Voronoi cell of its head. -/
theorem KHEJKCI (V : Set V3) (k : ℕ) (ul : List V3) (hs : saturated V)
    (hP : Packing V) (hk : barV V k ul) :
    FaceOf (voronoiList V ul) (voronoiClosed V (hdV ul)) := by
  obtain ⟨h, t, hcons, -⟩ := BARV_CONS V k ul hk
  have hsub : setOfList ul ⊆ V := BARV_SUBSET V k ul hk
  have h0V : h ∈ V := hsub (by rw [hcons]; simp [setOfList])
  -- honest bootstrapping of `barV V 0 [h]`
  have h0 : barV V 0 [h] := p6_barV_0 V hP h h0V
  rw [hcons] at hk ⊢
  have hface := KHEJKCI_GEN V 0 k [h] (h :: t) hs hP h0 hk ⟨t, rfl⟩
  rw [VORONOI_LIST_SING] at hface
  exact hface

/-- Rogers.hl:172 `VORONOI_BARV_CANONICAL`: canonical halfspace
representation of the Voronoi list of a `barV` list. -/
theorem VORONOI_BARV_CANONICAL (V : Set V3) (k : ℕ) (ul : List V3)
    (hP : Packing V) (hs : saturated V) (hk : barV V k ul) :
    ∃ K : Set (Set V3), K.Finite ∧
      voronoiList V ul = (affineSpan ℝ (voronoiList V ul) : Set V3) ∩ ⋂₀ K ∧
      (∀ a ∈ K, ∃ v ∈ V, v ≠ hdV ul ∧ (a = bisLe v (hdV ul) ∨ a = bisLe (hdV ul) v)) ∧
      ∀ K' ⊂ K, voronoiList V ul ⊂
        (affineSpan ℝ (voronoiList V ul) : Set V3) ∩ ⋂₀ K' := by
  obtain ⟨h, t, hcons, -⟩ := BARV_CONS V k ul hk
  have hhdev : hdV (h :: t) = h := rfl
  rw [hcons, hhdev]
  exact VORONOI_LIST_CANONICAL V (h :: t) h t hP hs
    (by rw [← hcons]; exact BARV_SUBSET V k ul hk) rfl

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
  -- V3 dot product is the `Fin 3 → ℝ` dot product after `ofLp`
  have hpi : ∀ (y z : V3), y ⬝ᵥ z = ((y : Fin 3 → ℝ) ⬝ᵥ (z : Fin 3 → ℝ)) :=
    fun y z => rfl
  have haddV : ∀ (y z : V3), ((y + z : V3) : Fin 3 → ℝ)
      = (y : Fin 3 → ℝ) + (z : Fin 3 → ℝ) := fun y z => rfl
  have hsmulV : ∀ (r : ℝ) (y : V3), ((r • y : V3) : Fin 3 → ℝ)
      = r • (y : Fin 3 → ℝ) := fun r y => rfl
  have hzdot : ∀ x : V3, (0 : V3) ⬝ᵥ x = 0 := by
    intro x
    have h0 : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl
    rw [hpi, h0]
    exact zero_dotProduct ((x : Fin 3 → ℝ))
  have hdotself : ∀ y : V3, y ⬝ᵥ y = 0 → y = 0 := by
    intro y h
    apply WithLp.ofLp_injective
    have h' : ((y : Fin 3 → ℝ)) ⬝ᵥ ((y : Fin 3 → ℝ)) = 0 := by
      rw [← hpi y y]
      exact h
    simpa using dotProduct_self_eq_zero.mp h'
  have hsmul : ∀ (r : ℝ) (y z : V3), y ⬝ᵥ (r • z) = r * (y ⬝ᵥ z) :=
    fun r y z => dotProduct_smul r (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)
  have hsmulL : ∀ (r : ℝ) (y z : V3), (r • y) ⬝ᵥ z = r * (y ⬝ᵥ z) :=
    fun r y z => smul_dotProduct r (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)
  have hadd : ∀ (y z w : V3), y ⬝ᵥ (z + w) = y ⬝ᵥ z + y ⬝ᵥ w :=
    fun y z w => dotProduct_add (y : Fin 3 → ℝ) (z : Fin 3 → ℝ) (w : Fin 3 → ℝ)
  have hcomm : ∀ (y z : V3), y ⬝ᵥ z = z ⬝ᵥ y :=
    fun y z => dotProduct_comm (y : Fin 3 → ℝ) (z : Fin 3 → ℝ)
  have hexp : ∀ (y z : V3) (r : ℝ),
      (y - r • z) ⬝ᵥ (y - r • z) =
        y ⬝ᵥ y - 2 * r * (y ⬝ᵥ z) + r * r * (z ⬝ᵥ z) := by
    intro y z r
    rw [hpi y y, hpi y z, hpi z z, hpi]
    rw [show ((y - r • z : V3) : Fin 3 → ℝ) = (y : Fin 3 → ℝ) - r • (z : Fin 3 → ℝ) from rfl]
    simp only [dotProduct_sub, dotProduct_smul, dotProduct_comm]
    ring
  constructor
  · intro heq
    have hiff : ∀ x : V3, (a ⬝ᵥ x ≤ b ↔ c ⬝ᵥ x ≤ d) := by
      intro x
      have h : x ∈ {x : V3 | a ⬝ᵥ x ≤ b} ↔ x ∈ {x : V3 | c ⬝ᵥ x ≤ d} := by
        rw [heq]
      simpa only [Set.mem_setOf_eq] using h
    by_cases ha : a = 0
    · subst ha
      have hiff0 : ∀ x : V3, (0 ≤ b ↔ c ⬝ᵥ x ≤ d) := by
        intro x
        have h := hiff x
        rw [hzdot x] at h
        exact h
      by_cases hc : c = 0
      · subst hc
        refine Or.inr ⟨rfl, rfl, ?_⟩
        have hz : (0 ≤ b ↔ 0 ≤ d) := by
          have h1 := hiff0 0
          rw [hzdot (0 : V3)] at h1
          exact h1
        by_cases hb : 0 ≤ b
        · exact Or.inl ⟨hb, hz.1 hb⟩
        · have hd : ¬ 0 ≤ d := fun hd0 => hb (hz.2 hd0)
          exact Or.inr ⟨lt_of_not_ge hb, lt_of_not_ge hd⟩
      · exfalso
        have hcc : c ⬝ᵥ c ≠ 0 := by
          intro h0
          exact hc (hdotself c h0)
        by_cases hb : 0 ≤ b
        · -- the left side is the whole space; then c · x ≤ d for all x,
          -- contradicting x = ((d + 1) / (c ⬝ᵥ c)) • c
          have hx : c ⬝ᵥ (((d + 1) / (c ⬝ᵥ c)) • c) = d + 1 := by
            rw [hsmul]
            field_simp [hcc]
          have hxle : c ⬝ᵥ (((d + 1) / (c ⬝ᵥ c)) • c) ≤ d :=
            (hiff0 (((d + 1) / (c ⬝ᵥ c)) • c)).1 hb
          rw [hx] at hxle
          linarith
        · -- the left side is empty; but x = (d / (c ⬝ᵥ c)) • c lies in the right
          have hb' : b < 0 := lt_of_not_ge hb
          have hx : c ⬝ᵥ ((d / (c ⬝ᵥ c)) • c) = d := by
            rw [hsmul]
            field_simp [hcc]
          have hxle : c ⬝ᵥ ((d / (c ⬝ᵥ c)) • c) ≤ d := by rw [hx]
          exact absurd ((hiff0 ((d / (c ⬝ᵥ c)) • c)).2 hxle) (not_le.2 hb')
    · -- a ≠ 0
      have haa : a ⬝ᵥ a ≠ 0 := by
        intro h0
        exact ha (hdotself a h0)
      have hge0 : 0 ≤ a ⬝ᵥ a := by
        have h0 : a ⬝ᵥ a = ∑ i : Fin 3, (a : Fin 3 → ℝ) i * (a : Fin 3 → ℝ) i := rfl
        rw [h0]
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      -- the key quadratic inequality (Rogers.hl:254, subgoal "A")
      have key : ∀ u : ℝ, u * ((a ⬝ᵥ a) * (c ⬝ᵥ c) - (a ⬝ᵥ c) * (a ⬝ᵥ c))
          ≤ d * (a ⬝ᵥ a) - b * (a ⬝ᵥ c) := by
        intro u
        set w := (b - u * (a ⬝ᵥ c)) / (a ⬝ᵥ a) with hwdef
        have hwaa : w * (a ⬝ᵥ a) = b - u * (a ⬝ᵥ c) := by
          rw [hwdef]
          field_simp [haa]
        have hax : a ⬝ᵥ (w • a + u • c) = b := by
          rw [hadd, hsmul, hsmul, hwaa]
          ring
        have hcx : c ⬝ᵥ (w • a + u • c) ≤ d := by
          have h := hiff (w • a + u • c)
          rw [haddV, hsmulV, hsmulV] at h
          rw [hax] at h
          exact h.1 (le_refl b)
        have hcxv : c ⬝ᵥ (w • a + u • c) = w * (a ⬝ᵥ c) + u * (c ⬝ᵥ c) := by
          rw [hadd, hsmul, hsmul, hcomm]
        have h3 := mul_le_mul_of_nonneg_right hcx hge0
        rw [hcxv] at h3
        have e1 : (w * (a ⬝ᵥ c)) * (a ⬝ᵥ a) = (b - u * (a ⬝ᵥ c)) * (a ⬝ᵥ c) := by
          rw [← hwaa]
          ring
        nlinarith [e1, h3]
      -- the equality case of Cauchy–Schwarz: c lies on the line spanned by a
      have hCauchy : (a ⬝ᵥ a) * (c ⬝ᵥ c) = (a ⬝ᵥ c) * (a ⬝ᵥ c) := by
        have h := REAL_LINE_BOUNDED ((a ⬝ᵥ a) * (c ⬝ᵥ c) - (a ⬝ᵥ c) * (a ⬝ᵥ c))
          (d * (a ⬝ᵥ a) - b * (a ⬝ᵥ c)) key
        linarith
      set s : ℝ := (a ⬝ᵥ c) / (a ⬝ᵥ a) with hsdef
      have hSab : s * (a ⬝ᵥ a) = a ⬝ᵥ c := by
        rw [hsdef]
        exact div_mul_cancel₀ _ haa
      have h2 : s * (a ⬝ᵥ c) * (a ⬝ᵥ a) = (a ⬝ᵥ c) * (a ⬝ᵥ c) := by
        rw [hsdef]
        field_simp [haa]
      have hcc' : c ⬝ᵥ c = s * (a ⬝ᵥ c) := by
        have hprod : s * (a ⬝ᵥ c) * (a ⬝ᵥ a) = (c ⬝ᵥ c) * (a ⬝ᵥ a) := by
          nlinarith [h2, hCauchy]
        exact (mul_right_cancel₀ haa hprod).symm
      have h3saa : s * s * (a ⬝ᵥ a) = s * (a ⬝ᵥ c) := by
        rw [← hSab]
        ring
      have hceq : c = s • a := by
        have hcoll : (c - s • a) ⬝ᵥ (c - s • a) = 0 := by
          rw [hexp, hcc', h3saa, hcomm c a]
          ring
        exact sub_eq_zero.mp (hdotself _ hcoll)
      -- s ≠ 0, otherwise the right side is degenerate while the left is not
      have hs0 : s ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hceq
        have hz : ∀ x : V3, (a ⬝ᵥ x ≤ b ↔ 0 ≤ d) := by
          intro x
          have h := hiff x
          rw [hceq, hzdot x] at h
          exact h
        have hx2 : a ⬝ᵥ (((b + 1) / (a ⬝ᵥ a)) • a) = b + 1 := by
          rw [hsmul]
          field_simp [haa]
        have hx3 : a ⬝ᵥ (((b - 1) / (a ⬝ᵥ a)) • a) = b - 1 := by
          rw [hsmul]
          field_simp [haa]
        have hnot : ¬ 0 ≤ d := fun hd0 => by
          have h9 := (hz (((b + 1) / (a ⬝ᵥ a)) • a)).2 hd0
          rw [hsmulV, hx2] at h9
          linarith
        exact hnot ((hz (((b - 1) / (a ⬝ᵥ a)) • a)).1
          (by rw [hsmulV, hx3]; linarith))
      -- the two sample points pin `d = s * b` once `s > 0`
      have hx1 : a ⬝ᵥ ((b / (a ⬝ᵥ a)) • a) = b := by
        rw [hsmul]
        field_simp [haa]
      have h1 : s * b ≤ d := by
        have hmem := (hiff ((b / (a ⬝ᵥ a)) • a)).1 (by rw [hsmulV, hx1])
        have hc1 : c ⬝ᵥ ((b / (a ⬝ᵥ a)) • a) = s * b := by
          rw [hceq, hsmulL, hx1]
        rw [hsmulV, hc1] at hmem
        exact hmem
      have h4 : d / s ≤ b := by
        have hx0 : c ⬝ᵥ (((d / s) / (a ⬝ᵥ a)) • a) = d := by
          rw [hceq, hsmulL, hsmul]
          field_simp [haa, hs0]
        have h4a : a ⬝ᵥ (((d / s) / (a ⬝ᵥ a)) • a) = d / s := by
          rw [hsmul]
          field_simp [haa]
        have hmem := (hiff (((d / s) / (a ⬝ᵥ a)) • a)).2 (by rw [hsmulV, hx0])
        rw [hsmulV, h4a] at hmem
        exact hmem
      by_cases hsneg : s < 0
      · -- s < 0 is incompatible with the equality of the two halfspaces
        exfalso
        have hx4 : a ⬝ᵥ (((b + 1) / (a ⬝ᵥ a)) • a) = b + 1 := by
          rw [hsmul]
          field_simp [haa]
        have hx4' : c ⬝ᵥ (((b + 1) / (a ⬝ᵥ a)) • a) = s * (b + 1) := by
          rw [hceq, hsmulL, hx4]
        have hnotmem : ¬ (a ⬝ᵥ (((b + 1) / (a ⬝ᵥ a)) • a) ≤ b) := by
          intro hcon
          rw [hx4] at hcon
          linarith
        have hgt : ¬ (c ⬝ᵥ (((b + 1) / (a ⬝ᵥ a)) • a) ≤ d) :=
          fun hcon => hnotmem ((hiff (((b + 1) / (a ⬝ᵥ a)) • a)).2 hcon)
        rw [hx4'] at hgt
        have hgt' : d < s * (b + 1) := not_le.mp hgt
        have hexp4 : s * (b + 1) = s * b + s := by ring
        rw [hexp4] at hgt'
        linarith
      · -- 0 < s
        have hpos : 0 < s := lt_of_le_of_ne (le_of_not_gt hsneg) (Ne.symm hs0)
        have hq : d / s * s = d := div_mul_cancel₀ d hs0
        have h5 : d ≤ s * b := by
          have h5a : d / s * s ≤ b * s := mul_le_mul_of_nonneg_right h4
            (le_of_not_gt hsneg)
          rw [hq, mul_comm] at h5a
          exact h5a
        exact Or.inl ⟨s, hceq, le_antisymm h5 h1, hpos⟩
  · rintro (⟨t, rfl, rfl, ht⟩ | ⟨rfl, rfl, hsign⟩)
    · ext x
      simp only [Set.mem_setOf_eq, hsmulL]
      exact (mul_le_mul_iff_of_pos_left ht).symm
    · ext x
      have hz : (0 : V3) ⬝ᵥ x = 0 := hzdot x
      simp only [Set.mem_setOf_eq, hz]
      rcases hsign with ⟨hb, hd⟩ | ⟨hb, hd⟩
      · exact ⟨fun _ => hd, fun _ => hb⟩
      · exact iff_of_false (not_le.2 hb) (not_le.2 hd)

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
  classical
  intro c
  -- every bisector constraint is a nonzero linear halfspace (Rogers.hl:417,
  -- the Skolem step `bis_le v u = {x | 2 % (u - v) dot x ≤ u dot u - v dot v}`)
  obtain ⟨a, b, hab⟩ : ∃ a : Set V3 → V3, ∃ b : Set V3 → ℝ,
      ∀ h ∈ K, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h} := by
    have hsk : ∀ h : Set V3, ∃ a : V3, ∃ b : ℝ,
        h ∈ K → (a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b}) := by
      intro h
      by_cases hK : h ∈ K
      · obtain ⟨v, hvV, hvu, hcase⟩ := h3 h hK
        rcases hcase with heq | heq
        · refine ⟨(2 : ℝ) • (u - v), u ⬝ᵥ u - v ⬝ᵥ v, ?_⟩
          intro _
          refine ⟨?_, ?_⟩
          · intro hcon
            exact hvu (sub_eq_zero.mp
              ((smul_eq_zero.mp hcon).resolve_left (by norm_num))).symm
          · rw [heq, BIS_LE_EQ_HALFSPACE]
            ext x
            simp only [Set.mem_setOf_eq, WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]
        · refine ⟨(2 : ℝ) • (v - u), v ⬝ᵥ v - u ⬝ᵥ u, ?_⟩
          intro _
          refine ⟨?_, ?_⟩
          · intro hcon
            exact hvu (sub_eq_zero.mp
              ((smul_eq_zero.mp hcon).resolve_left (by norm_num)))
          · rw [heq, BIS_LE_EQ_HALFSPACE]
            ext x
            simp only [Set.mem_setOf_eq, WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]
      · exact ⟨0, 0, fun hm => absurd hm hK⟩
    choose a b hab using hsk
    exact ⟨a, b, fun h hK => hab h hK⟩
  have hmain := FACET_OF_POLYHEDRON_EXPLICIT (s := s) (F := K) a b h1 h2 hab h4 c
  rw [hmain]
  constructor
  · rintro ⟨h, hK, rfl⟩
    obtain ⟨v, hvV, hvu, hcase⟩ := h3 h hK
    rcases hcase with heq | heq
    · have hplane := HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a h) v u (b h)
        (hab h hK).1 ((hab h hK).2.symm.trans heq)
      exact ⟨v, hvV, Or.inl (by rw [← heq]; exact hK), by rw [hplane, BIS_SYM]⟩
    · have hplane := HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a h) u v (b h)
        (hab h hK).1 ((hab h hK).2.symm.trans heq)
      exact ⟨v, hvV, Or.inr (by rw [← heq]; exact hK), by rw [hplane]⟩
  · rintro ⟨v, hvV, hKmem, rfl⟩
    rcases hKmem with hKmem | hKmem
    · have hplane := HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a (bisLe v u))
        v u (b (bisLe v u)) (hab _ hKmem).1 (hab _ hKmem).2.symm
      exact ⟨bisLe v u, hKmem, by rw [hplane, BIS_SYM]⟩
    · have hplane := HALFSPACE_EQ_BIS_LE_IMP_HYPERPLANE_EQ_BIS (a (bisLe u v))
        u v (b (bisLe u v)) (hab _ hKmem).1 (hab _ hKmem).2.symm
      exact ⟨bisLe u v, hKmem, by rw [hplane]⟩

/-! ## Rogers.hl:523-825 — facets of Voronoi lists, existence of barV lists -/

/-- Prefix criterion: if `w` and `u` are both initial sublists of a common
list, `w` is an initial sublist of `u`. -/
private theorem p6_initial_sublist_prefix {w u z : List V3}
    (h1 : initialSublist w z) (h2 : initialSublist u z) (hlen : w.length ≤ u.length) :
    initialSublist w u := by
  obtain ⟨t1, ht1⟩ := h1
  obtain ⟨t2, ht2⟩ := h2
  have heq : w ++ t1 = u ++ t2 := by rw [← ht1, ← ht2]
  rcases List.append_eq_append_iff.mp heq with hcase | hcase
  · obtain ⟨t, hw, -⟩ := hcase
    exact ⟨t, hw⟩
  · obtain ⟨t, hu, -⟩ := hcase
    rw [hu, List.length_append] at hlen
    have ht0 : t = [] := List.length_eq_zero_iff.mp (by omega)
    rw [ht0, List.append_nil] at hu
    exact ⟨[], by rw [hu, List.append_nil]⟩

/-- Rogers.hl:523 `IDBEZAL`: facets of a Voronoi list of dimension `< 3`. -/
theorem IDBEZAL (V : Set V3) (ul : List V3) (k : ℕ) (F : Set V3) (hs : saturated V)
    (hP : Packing V) (hbar : barV V k ul) (h3 : k < 3) :
    FacetOf F (voronoiList V ul) ↔
      ∃ vl : List V3, F = voronoiList V vl ∧ barV V (k + 1) vl ∧
        truncateSimplex k vl = ul := by
  constructor
  · intro hF
    obtain ⟨h, t, hcons, hhd⟩ := BARV_CONS V k ul hbar
    have hcons' : ul = hdV ul :: t := hcons.trans (by rw [← hhd])
    have hsub : setOfList ul ⊆ V := BARV_SUBSET V k ul hbar
    obtain ⟨K, hKfin, hKeq, hKprop, hKmin⟩ := VORONOI_BARV_CANONICAL V k ul hP hs hbar
    obtain ⟨v, hvV, hKin, hFv⟩ :=
      (FACET_OF_POLYHEDRON_EXPLICIT_BIS V K (voronoiList V ul) (hdV ul) hKfin hKeq
        hKprop hKmin F).mp hF
    have hts : truncateSimplex k (ul ++ [v]) = ul :=
      ((TRUNCATE_SIMPLEX_INITIAL_SUBLIST k ul (ul ++ [v])).2
        ⟨INITIAL_SUBLIST_APPEND ul [v], hbar.1⟩).1
    have hFext : voronoiList V (ul ++ [v]) = F := by
      rw [← VORONOI_LIST_INTER_BIS V ul v (hdV ul) t hsub hvV hcons', hFv]
    have hbarext : barV V (k + 1) (ul ++ [v]) := by
      refine ⟨by rw [List.length_append, List.length_singleton, hbar.1], ?_⟩
      rintro w ⟨hwinit, hwpos⟩
      by_cases hlen : w.length ≤ k + 1
      · have hwinit' : initialSublist w ul :=
          p6_initial_sublist_prefix hwinit (INITIAL_SUBLIST_APPEND ul [v])
            (by rw [hbar.1]; exact hlen)
        exact hbar.2 w ⟨hwinit', hwpos⟩
      · have hlenEq : w.length = (ul ++ [v]).length := by
          have hwle := INITIAL_SUBLIST_LENGTH_LE hwinit
          rw [List.length_append, List.length_singleton, hbar.1] at hwle ⊢
          omega
        have hwEq : w = ul ++ [v] :=
          INITIAL_SUBLIST_UNIQUE hwinit (INITIAL_SUBLIST_REFL (ul ++ [v])) hlenEq rfl
        subst hwEq
        have hlen4 : (ul ++ [v]).length = k + 2 := by
          rw [List.length_append, List.length_singleton, hbar.1]
        refine ⟨by rw [hlen4]; omega, ?_, ?_⟩
        · intro z hz
          rcases List.mem_append.1 hz with hz | hz
          · exact hsub hz
          · rw [List.mem_singleton] at hz
            rw [hz]
            exact hvV
        · rw [hFext, hlen4]
          have h1 := hF.2.2
          rw [AFF_DIM_VORONOI_LIST V ul k hbar] at h1
          omega
    exact ⟨ul ++ [v], hFext.symm, hbarext, hts⟩
  · rintro ⟨vl, hFvl, hbarvl, hts⟩
    obtain ⟨hinit, hlenul⟩ := (TRUNCATE_SIMPLEX_INITIAL_SUBLIST k ul vl).1 ⟨hts, by
      have := hbarvl.1
      omega⟩
    rw [hFvl]
    refine ⟨KHEJKCI_GEN V k (k + 1) ul vl hs hP hbar hbarvl hinit, ?_, ?_⟩
    · exact BARV_IMP_VORONOI_LIST_NOT_EMPTY V vl (k + 1) hbarvl
    · rw [AFF_DIM_VORONOI_LIST V vl (k + 1) hbarvl, AFF_DIM_VORONOI_LIST V ul k hbar]
      omega

/-- The supremum of a nonempty, bounded-above, closed set of reals belongs
to the set. -/
private theorem p6_sSup_mem_closed (I : Set ℝ) (hne : I.Nonempty) (hbdd : BddAbove I)
    (hcl : IsClosed I) : sSup I ∈ I := by
  by_contra hnot
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl (sSup I) (by
    simpa using hnot)
  have hbound : ∀ x ∈ I, x ≤ sSup I - ε := by
    intro x hx
    have hxle : x ≤ sSup I := le_csSup hbdd hx
    have hlt : x < sSup I := by
      rcases eq_or_lt_of_le hxle with he | hl
      · exact absurd (he ▸ hx) hnot
      · exact hl
    have hballmem : x ∉ Metric.ball (sSup I) ε := fun hm => hball hm hx
    have hdist : ε ≤ dist x (sSup I) :=
      le_of_not_gt fun hlt' => hballmem (Metric.mem_ball.2 hlt')
    rw [Real.dist_eq, abs_of_neg (by linarith)] at hdist
    linarith
  have hsup := csSup_le hne hbound
  linarith

/-- A compact convex set of positive affine dimension has two distinct
points. -/
private theorem p6_two_distinct_of_affDim_pos {s : Set V3} (hsne : s.Nonempty)
    (hdim : 0 < affDim s) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  by_contra hall
  push_neg at hall
  obtain ⟨x₀, hx₀⟩ := hsne
  have hseq : s = {x₀} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨hx₀, fun z hz => hall z hz x₀ hx₀⟩
  rw [hseq, affDim_singleton] at hdim
  omega

/-- Boundary-point lemma behind Rogers.hl:694: a point of a compact
polyhedron lies in the convex hull of `p0` and a facet (or is `p0`
itself). -/
private theorem p6_mem_hull_insert_facet (s : Set V3) (p0 v : V3)
    (hsp : polyhedron s) (hcomp : _root_.IsCompact s) (hp0 : p0 ∈ s) (hv : v ∈ s) :
    v = p0 ∨ ∃ f : Set V3, FacetOf f s ∧ v ∈ convexHull ℝ (insert p0 f) := by
  classical
  by_cases hv0 : v = p0
  · exact Or.inl hv0
  · right
    have hdnz : v - p0 ≠ 0 := sub_ne_zero.2 hv0
    have hnormpos : (0 : ℝ) < ‖v - p0‖ := norm_pos_iff.2 hdnz
    have hcont : Continuous fun t : ℝ => p0 + t • (v - p0) := by fun_prop
    have hIcl : IsClosed {t : ℝ | p0 + t • (v - p0) ∈ s} :=
      (IsCompact.isClosed hcomp).preimage hcont
    have hone : (1 : ℝ) ∈ {t : ℝ | p0 + t • (v - p0) ∈ s} := by
      simp only [Set.mem_setOf_eq, one_smul, add_sub_cancel]
      exact hv
    have hzero : (0 : ℝ) ∈ {t : ℝ | p0 + t • (v - p0) ∈ s} := by
      simp only [Set.mem_setOf_eq, zero_smul, add_zero]
      exact hp0
    have hbdd : BddAbove {t : ℝ | p0 + t • (v - p0) ∈ s} := by
      obtain ⟨C, hC⟩ := IsCompact.exists_isMaxOn hcomp ⟨p0, hp0⟩
        (f := fun x : V3 => ‖x‖) (by fun_prop)
      refine ⟨(2 * ‖C‖) / ‖v - p0‖, ?_⟩
      intro t ht
      have hC0 : ‖p0‖ ≤ ‖C‖ := hC.2 hp0
      have h1 : ‖t • (v - p0)‖ ≤ ‖C‖ + ‖p0‖ := by
        have h2 : ‖t • (v - p0)‖ = ‖(p0 + t • (v - p0)) - p0‖ := by
          rw [add_sub_cancel_left]
        rw [h2]
        calc ‖(p0 + t • (v - p0)) - p0‖ ≤ ‖p0 + t • (v - p0)‖ + ‖p0‖ := norm_sub_le _ _
          _ ≤ ‖C‖ + ‖p0‖ := by
              exact add_le_add (hC.2 ht) (le_refl _)
      have h3 : |t| * ‖v - p0‖ ≤ ‖C‖ + ‖p0‖ := by
        rw [norm_smul, Real.norm_eq_abs] at h1
        exact h1
      have h4 : t * ‖v - p0‖ ≤ ‖C‖ + ‖p0‖ := by
        rcases abs_choice t with hc | hc
        · rw [← hc]
          exact h3
        · have ht0 : t ≤ 0 := by
            have habs : 0 ≤ |t| := abs_nonneg t
            linarith
          have hd0 : 0 ≤ ‖v - p0‖ := norm_nonneg _
          have hS0 : 0 ≤ ‖C‖ + ‖p0‖ := by
            have h1' : 0 ≤ ‖C‖ := norm_nonneg _
            have h2' : 0 ≤ ‖p0‖ := norm_nonneg _
            linarith
          nlinarith
      exact (le_div_iff₀ hnormpos).2 (by linarith)
    set T := sSup {t : ℝ | p0 + t • (v - p0) ∈ s} with hTdef
    have hTmem : p0 + T • (v - p0) ∈ s :=
      hTdef ▸ p6_sSup_mem_closed _ ⟨0, hzero⟩ hbdd hIcl
    have hT1 : (1 : ℝ) ≤ T := le_csSup hbdd hone
    -- the farthest point of the polytope on the ray is not in the relative interior
    have haff : ∀ r : ℝ, p0 + r • (v - p0) ∈ (affineSpan ℝ s : Set V3) := by
      intro r
      have hA0 : p0 ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hp0
      have hdir : (v - p0 : V3) ∈ (affineSpan ℝ s).direction := by
        rw [direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ hv hp0
      have hv2 := AffineSubspace.vadd_mem_of_mem_direction
        (Submodule.smul_mem _ r hdir) hA0
      rw [vadd_eq_add, add_comm] at hv2
      exact hv2
    have hwint : p0 + T • (v - p0) ∉ intrinsicInterior ℝ s := by
      intro hm
      obtain ⟨-, ε, hε, hball⟩ := mem_rint_iff.1 hm
      have hpos : 0 < ε / (2 * ‖v - p0‖) := by
        apply div_pos hε
        linarith
      have hd : dist (p0 + (T + ε / (2 * ‖v - p0‖)) • (v - p0))
          (p0 + T • (v - p0)) < ε := by
        rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, add_sub_cancel_left,
          norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
        field_simp
        linarith
      have hmem : (T + ε / (2 * ‖v - p0‖)) ∈
          {t : ℝ | p0 + t • (v - p0) ∈ s} :=
        Set.mem_setOf.2 (hball ⟨hd, haff _⟩)
      have hle := le_csSup hbdd hmem
      linarith
    rw [RELATIVE_INTERIOR_OF_POLYHEDRON hsp] at hwint
    have hU : p0 + T • (v - p0) ∈ ⋃₀ {f : Set V3 | FacetOf f s} := by
      by_contra hcon
      exact hwint ((Set.mem_sdiff _).2 ⟨hTmem, hcon⟩)
    obtain ⟨f, hf, hwf⟩ := Set.mem_sUnion.1 hU
    refine ⟨f, hf, ?_⟩
    have hTpos : (0 : ℝ) < T := by linarith
    have hseg : v ∈ convexHull ℝ {p0, p0 + T • (v - p0)} := by
      rw [convexHull_pair, segment_eq_image' ℝ p0 (p0 + T • (v - p0))]
      have hθ1 : (0:ℝ) ≤ 1 / T := div_nonneg (by norm_num) hTpos.le
      have hθ2 : 1 / T ≤ 1 := (div_le_one hTpos).2 hT1
      refine ⟨1 / T, ⟨hθ1, hθ2⟩, ?_⟩
      show p0 + (1 / T) • ((p0 + T • (v - p0)) - p0) = v
      rw [add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hTpos),
        one_smul, add_sub_cancel]
    refine convexHull_mono ?_ hseg
    intro z hz
    rcases Set.mem_insert_iff.1 hz with hz | hz
    · subst hz
      exact Set.mem_insert z f
    · subst hz
      exact Set.mem_insert_of_mem _ hwf

/-- Specialization of HOL `POLYTOPE_UNION_CONVEX_HULL_FACETS` (polytope.ml)
to a compact polyhedron of positive dimension. -/
private theorem p6_union_convex_hull_facets (s : Set V3) (p : V3) (hsp : polyhedron s)
    (hcomp : _root_.IsCompact s) (hdim : 0 < affDim s) (hp : p ∈ s) :
    s = ⋃₀ {convexHull ℝ (insert p f) | f ∈ {f : Set V3 | FacetOf f s}} := by
  classical
  have hsne : s.Nonempty := ⟨p, hp⟩
  have hconv : Convex ℝ s := POLYHEDRON_IMP_CONVEX hsp
  obtain ⟨x, hx, y, hy, hxy⟩ := p6_two_distinct_of_affDim_pos hsne hdim
  have hfacet : ∃ f : Set V3, FacetOf f s := by
    rcases eq_or_ne x p with hx0 | hx0
    · obtain ⟨f, hf, -⟩ := (p6_mem_hull_insert_facet s p y hsp hcomp hp hy).resolve_left
        (fun heq => hxy (by rw [hx0]; exact heq.symm))
      exact ⟨f, hf⟩
    · obtain ⟨f, hf, -⟩ := (p6_mem_hull_insert_facet s p x hsp hcomp hp hx).resolve_left hx0
      exact ⟨f, hf⟩
  ext v
  constructor
  · intro hv
    by_cases hv0 : v = p
    · obtain ⟨f, hf⟩ := hfacet
      rw [hv0]
      exact Set.mem_sUnion.2 ⟨convexHull ℝ (insert p f), ⟨f, hf, rfl⟩,
        subset_convexHull ℝ _ (Set.mem_insert p f)⟩
    · obtain ⟨f, hf, hvm⟩ :=
        (p6_mem_hull_insert_facet s p v hsp hcomp hp hv).resolve_left hv0
      exact Set.mem_sUnion.2 ⟨convexHull ℝ (insert p f), ⟨f, hf, rfl⟩, hvm⟩
  · rintro ⟨T, ⟨f, hf, rfl⟩, hvT⟩
    have hsub : insert p f ⊆ s := by
      intro z hz
      rcases Set.mem_insert_iff.1 hz with hz | hz
      · rw [hz]; exact hp
      · exact hf.1.1 hz
    exact convexHull_min hsub hconv hvT

/-- Monotonicity of Voronoi lists under initial sublists. -/
private theorem p6_voronoi_list_mono_init (V : Set V3) (t u : List V3)
    (h : initialSublist t u) : voronoiList V u ⊆ voronoiList V t := by
  intro x hx
  simp only [voronoiList, voronoiSet, Set.mem_sInter] at hx ⊢
  intro A hA
  obtain ⟨v, hv, rfl⟩ := hA
  exact hx _ ⟨v, SET_OF_LIST_INITIAL_SUBLIST_SUBSET h hv, rfl⟩

/-- Rogers.hl:694 `VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS`. -/
theorem VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS (V : Set V3) (ul : List V3) (k : ℕ)
    (p : V3) (hP : Packing V) (hs : saturated V) (hbar : barV V k ul) (hk3 : k < 3)
    (hp : p ∈ voronoiList V ul) :
    voronoiList V ul =
      ⋃₀ {convexHull ℝ (insert p (voronoiList V vl)) | vl ∈ {vl : List V3 |
        barV V (k + 1) vl ∧ truncateSimplex k vl = ul}} := by
  classical
  have hcomp : _root_.IsCompact (voronoiList V ul) :=
    POLYTOPE_IMP_COMPACT (POLYTOPE_VORONOI_LIST_BARV V ul k hP hs hbar)
  have hsp : polyhedron (voronoiList V ul) :=
    POLYHEDRON_VORONOI_LIST V ul hP hs (BARV_SUBSET V k ul hbar)
  have hdim : 0 < affDim (voronoiList V ul) := by
    rw [AFF_DIM_VORONOI_LIST V ul k hbar]
    omega
  have hmain := p6_union_convex_hull_facets (voronoiList V ul) p hsp hcomp hdim hp
  have hfam : {convexHull ℝ (insert p f) | f ∈ {f : Set V3 |
      FacetOf f (voronoiList V ul)}} =
      {convexHull ℝ (insert p (voronoiList V vl)) | vl ∈ {vl : List V3 |
        barV V (k + 1) vl ∧ truncateSimplex k vl = ul}} := by
    ext T
    constructor
    · rintro ⟨f, hf, hTeq⟩
      obtain ⟨vl, hvl1, hvl2, hvl3⟩ := (IDBEZAL V ul k f hs hP hbar hk3).mp hf
      exact ⟨vl, ⟨hvl2, hvl3⟩, by rw [← hTeq, hvl1]⟩
    · rintro ⟨vl, hmem, hTeq⟩
      obtain ⟨hvl2, hvl3⟩ := hmem
      have hf : FacetOf (voronoiList V vl) (voronoiList V ul) :=
        (IDBEZAL V ul k (voronoiList V vl) hs hP hbar hk3).mpr ⟨vl, rfl, hvl2, hvl3⟩
      exact ⟨voronoiList V vl, hf, by rw [hTeq]⟩
  rw [hmain, hfam]

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

/-- Rogers.hl:778 `BARV_EXISTS`: a `barV V k` list extends to `barV V (k+1)`.
The cell `voronoi_list V wl` is nonempty (dimension `3 - k > 0`, so not the
empty set of dimension `-1`), hence the union decomposition of
`VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS` (Rogers.hl:694) has a nonempty
index family, which is exactly an extension `vl` with
`barV V (k + 1) vl` and `truncateSimplex k vl = wl`. -/
-- NEEDS: transitive upstream stubs in PackingAuto5 — POLYHEDRON_VORONOI_LIST
-- (:1500) / POLYTOPE_VORONOI_LIST (:1503) consumed by the in-file
-- VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS route; close them in PA5 to make
-- this proof sorryAx-free end to end. AFF_DIM_VORONOI_LIST (PA5:1531) is
-- already a real proof.
theorem BARV_EXISTS (V : Set V3) (wl : List V3) (k : ℕ) (hP : Packing V)
    (hs : saturated V) (hk3 : k < 3) (hbar : barV V k wl) :
    ∃ vl : List V3, barV V (k + 1) vl ∧ truncateSimplex k vl = wl := by
  have hdim : 0 < affDim (voronoiList V wl) := by
    rw [AFF_DIM_VORONOI_LIST V wl k hbar]
    omega
  have hne : (voronoiList V wl).Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty] at h0
    rw [h0, affDim_empty] at hdim
    omega
  obtain ⟨p, hp⟩ := hne
  have hpmem : p ∈ ⋃₀ {convexHull ℝ (insert p (voronoiList V vl)) |
      vl ∈ {vl : List V3 | barV V (k + 1) vl ∧ truncateSimplex k vl = wl}} := by
    rw [← VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS V wl k p hP hs hbar hk3 hp]
    exact hp
  obtain ⟨T, hT, -⟩ := Set.mem_sUnion.1 hpmem
  obtain ⟨vl, hv, rfl⟩ := hT
  exact ⟨vl, hv.1, hv.2⟩

/-- Rogers.hl:803 `BARV_EXISTS_ALT`. -/
theorem BARV_EXISTS_ALT (V : Set V3) (k : ℕ) (hP : Packing V) (hs : saturated V)
    (hk3 : k ≤ 3) : ∃ ul : List V3, barV V k ul := by
  induction k with
  | zero =>
    obtain ⟨v, hv, -⟩ := TIWWFYQ V 0 hP hs
    exact ⟨[v], p6_barV_0 V hP v hv⟩
  | succ k ih =>
    obtain ⟨ul, hul⟩ := ih (by omega)
    obtain ⟨vl, hv2, -⟩ := BARV_EXISTS V ul k hP hs (by omega) hul
    exact ⟨vl, hv2⟩

/-! ## Rogers.hl:826-1255 — GLTVHUM (Rogers simplex covering) -/

/-- `hull (A ∪ hull B) = hull (A ∪ B)` (pack3.hl:144 `CONV_UNION_lemma`). -/
private theorem p6_convexHull_union_hull (A B : Set V3) :
    convexHull ℝ (A ∪ convexHull ℝ B) = convexHull ℝ (A ∪ B) := by
  refine subset_antisymm ?_ ?_
  · refine convexHull_min ?_ (convex_convexHull ℝ (A ∪ B))
    intro z hz
    simp only [Set.mem_union] at hz
    rcases hz with hz | hz
    · exact subset_convexHull ℝ (A ∪ B) (Set.mem_union_left _ hz)
    · exact (convexHull_mono (Set.subset_union_right : B ⊆ A ∪ B)) hz
  · refine convexHull_min ?_ (convex_convexHull ℝ (A ∪ convexHull ℝ B))
    intro z hz
    simp only [Set.mem_union] at hz
    rcases hz with hz | hz
    · exact subset_convexHull ℝ (A ∪ convexHull ℝ B) (Set.mem_union_left _ hz)
    · exact subset_convexHull ℝ (A ∪ convexHull ℝ B)
        (Set.mem_union_right _ (subset_convexHull ℝ B hz))

/-- Image-congruent families have equal unions. -/
private theorem p6_sUnion_image_congr {α : Type*} {F : Set α} {f g : α → Set V3}
    (h : ∀ x ∈ F, f x = g x) : ⋃₀ {f x | x ∈ F} = ⋃₀ {g x | x ∈ F} := by
  ext z
  simp only [Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, hT, hz⟩
    obtain ⟨x, hx, rfl⟩ := hT
    exact ⟨g x, ⟨x, hx, rfl⟩, h x hx ▸ hz⟩
  · rintro ⟨T, hT, hz⟩
    obtain ⟨x, hx, rfl⟩ := hT
    exact ⟨f x, ⟨x, hx, rfl⟩, (h x hx).symm ▸ hz⟩

/-- Star lemma (HOL convex1.ml:2999 `CONVEX_HULL_UNION_UNIONS`): for a
nonempty family with convex union, the hull of `S ∪ ⋃₀ 𝒞` is the union of
the hulls of `S ∪ c`. -/
private theorem p6_convexHull_sUnion_left (S : Set V3) (𝒞 : Set (Set V3))
    (hne : 𝒞.Nonempty) (hconv : Convex ℝ (⋃₀ 𝒞)) :
    convexHull ℝ (S ∪ ⋃₀ 𝒞) = ⋃₀ {convexHull ℝ (S ∪ c) | c ∈ 𝒞} := by
  classical
  obtain ⟨c₀, hc₀⟩ := hne
  refine subset_antisymm ?_ ?_
  · -- the hull is inside the union of the pairwise hulls
    intro x hx
    by_cases hSe : S.Nonempty
    · by_cases hUe : (⋃₀ 𝒞).Nonempty
      · have hxj : x ∈ convexJoin ℝ (convexHull ℝ S) (convexHull ℝ (⋃₀ 𝒞)) := by
          rw [← convexHull_union hSe hUe]
          exact hx
        obtain ⟨p, hp, q, hq, hseg⟩ := mem_convexJoin.1 hxj
        have hqU : q ∈ ⋃₀ 𝒞 := hconv.convexHull_eq ▸ hq
        obtain ⟨c₁, hc₁, hqc₁⟩ := Set.mem_sUnion.1 hqU
        refine ⟨convexHull ℝ (S ∪ c₁), ⟨c₁, hc₁, rfl⟩, ?_⟩
        obtain ⟨θ, ϑ, hθ0, hϑ0, hsum, hxq⟩ := hseg
        refine (convex_iff_segment_subset.1 (convex_convexHull ℝ (S ∪ c₁))
          ((convexHull_mono (Set.subset_union_left : S ⊆ S ∪ c₁)) hp)
          (subset_convexHull ℝ _ (Set.mem_union_right _ hqc₁))) ?_
        rw [segment_eq_image]
        refine (Set.mem_image _ _ _).2 ⟨ϑ, ⟨hϑ0, by linarith⟩, ?_⟩
        show (1 - ϑ) • p + ϑ • q = x
        rw [show 1 - ϑ = θ from by linarith]
        exact hxq
      · have hU0 : ⋃₀ 𝒞 = ∅ := Set.not_nonempty_iff_eq_empty.1 hUe
        rw [hU0, Set.union_empty] at hx
        exact ⟨convexHull ℝ (S ∪ c₀), ⟨c₀, hc₀, rfl⟩,
          (convexHull_mono (Set.subset_union_left : S ⊆ S ∪ c₀)) hx⟩
    · have hSe0 : S = ∅ := Set.not_nonempty_iff_eq_empty.1 hSe
      have hx2 : x ∈ convexHull ℝ (⋃₀ 𝒞) := by
        rw [hSe0, Set.empty_union] at hx
        exact hx
      have hx3 : x ∈ ⋃₀ 𝒞 := hconv.convexHull_eq ▸ hx2
      obtain ⟨c₁, hc₁, xc₁⟩ := Set.mem_sUnion.1 hx3
      exact ⟨convexHull ℝ (S ∪ c₁), ⟨c₁, hc₁, rfl⟩, by
        rw [hSe0, Set.empty_union]
        exact subset_convexHull ℝ c₁ xc₁⟩
  · -- each member hull (S ∪ c) is inside the hull
    rintro x ⟨T, hT, hx⟩
    obtain ⟨c, hc, rfl⟩ := hT
    exact (convexHull_mono (Set.union_subset_union (Subset.refl _)
      (Set.subset_sUnion_of_mem hc))) hx

/-- Step lemma (C) of `GLTVHUM_lemma1`: the union of the "one-point
extension" hulls around a Voronoi list is the list itself (this is
`VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS` at the point `omega_list_n wl k`). -/
private theorem p6_gltvhum_union_g (V : Set V3) (wl : List V3) (k : ℕ) (hP : Packing V)
    (hs : saturated V) (hk3 : k < 3) (hbar : barV V k wl) :
    ⋃₀ {convexHull ℝ (insert (omegaListN V vl k) (voronoiList V vl)) | vl ∈
      {vl : List V3 | barV V (k + 1) vl ∧ truncateSimplex k vl = wl}} =
    voronoiList V wl := by
  have hp : omegaListN V wl k ∈ voronoiList V wl := by
    have h1 := OMEGA_LIST_N_IN_VORONOI_LIST V wl k k hbar (le_refl k)
    rwa [TRUNCATE_SIMPLEX_REFL k wl hbar.1] at h1
  rw [VORONOI_LIST_EQ_UNION_CONVEX_HULL_FACETS V wl k (omegaListN V wl k) hP hs hbar
    hk3 hp]
  ext T
  simp only [Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, hT, hx⟩
    obtain ⟨vl, hbarvl, hts, rfl⟩ := hT
    obtain ⟨hbarvl, hts⟩ := hbarvl
    have homega : omegaListN V vl k = omegaListN V wl k := by
      have hlen : vl.length = k + 2 := hbarvl.1
      have h5 := OMEGA_LIST_N_LEMMA V vl k 0 (by omega)
      rw [Nat.add_zero, hts] at h5
      exact h5
    rw [homega] at hx
    refine ⟨convexHull ℝ (insert (omegaListN V wl k) (voronoiList V vl)),
      Set.mem_setOf.2 ⟨vl, ⟨hbarvl, hts⟩, rfl⟩, hx⟩
  · rintro ⟨t, hT, hx⟩
    obtain ⟨vl, hbarvl, hts, rfl⟩ := hT
    obtain ⟨hbarvl, hts⟩ := hbarvl
    have homega : omegaListN V vl k = omegaListN V wl k := by
      have hlen : vl.length = k + 2 := hbarvl.1
      have h5 := OMEGA_LIST_N_LEMMA V vl k 0 (by omega)
      rw [Nat.add_zero, hts] at h5
      exact h5
    rw [← homega] at hx
    refine ⟨convexHull ℝ (insert (omegaListN V vl k) (voronoiList V vl)),
      Set.mem_setOf.2 ⟨vl, ⟨hbarvl, hts⟩, rfl⟩, hx⟩

/-- The `j..k` omega-window splits into the `j..k-1` window plus the top
point (HOL Rogers.hl:944-964). -/
private theorem p6_image_Icc_succ (f : ℕ → V3) (j k : ℕ) (hjk : j ≤ k) :
    {f i | i ∈ Finset.Icc j (k - 1)} ∪ {f k} = {f i | i ∈ Finset.Icc j k} := by
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, Finset.mem_Icc]
  constructor
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨k, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    rcases eq_or_ne i k with rfl | hik
    · exact Or.inr rfl
    · exact Or.inl ⟨i, by omega, rfl⟩

/-- Re-indexing a family union through the family image (the ∃-setOf
bookkeeping between the star lemma's `c ∈ 𝒞` form and the `vl`-indexed
form). -/
private theorem p6_sUnion_image_image {α β : Type*} {F : Set α} (g : α → β)
    (h : β → Set V3) :
    ⋃₀ {h (g x) | x ∈ F} = ⋃₀ {h y | y ∈ {g x | x ∈ F}} := by
  ext z
  simp only [Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, ⟨x, hxF, rfl⟩, hzT⟩
    exact ⟨h (g x), ⟨g x, ⟨x, hxF, rfl⟩, rfl⟩, hzT⟩
  · rintro ⟨T, ⟨y, ⟨x, hxF, rfl⟩, rfl⟩, hzT⟩
    exact ⟨h (g x), ⟨x, hxF, rfl⟩, hzT⟩

/-- A singleton-indexed family union collapses to the member. -/
private theorem p6_sUnion_singleton_image {α : Type*} (q : α → Set V3) (a : α) :
    ⋃₀ {q v | v ∈ ({a} : Set α)} = q a := by
  ext z
  simp only [Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨T, ⟨v, rfl, rfl⟩, hzT⟩
    exact hzT
  · intro hz
    exact ⟨q a, ⟨a, rfl, rfl⟩, hz⟩

/-- Step lemma (A) of `GLTVHUM_lemma1` (HOL Rogers.hl:905-942): split the
`(k+1)`-family through the truncation at level `k`. -/
private theorem p6_union_split (V : Set V3) (ul : List V3) (j k : ℕ) (hjk : j ≤ k)
    (Q : List V3 → Set V3) :
    ⋃₀ {Q vl | vl ∈ {vl : List V3 | barV V (k + 1) vl ∧ truncateSimplex j vl = ul}} =
    ⋃₀ {⋃₀ {Q vl | vl ∈ {vl : List V3 | barV V (k + 1) vl ∧ truncateSimplex k vl = wl}} |
      wl ∈ {wl : List V3 | barV V k wl ∧ truncateSimplex j wl = ul}} := by
  classical
  ext z
  simp only [Set.mem_sUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨T, ⟨vl, ⟨hb, ht⟩, rfl⟩, hzT⟩
    have hlen : vl.length = k + 2 := hb.1
    have hbart : barV V k (truncateSimplex k vl) :=
      TRUNCATE_SIMPLEX_BARV V k (k + 1) vl hb (by omega)
    have htwl : truncateSimplex j (truncateSimplex k vl) = ul := by
      rw [TRUNCATE_TRUNCATE_SIMPLEX vl j k hjk (by omega)]
      exact ht
    refine ⟨⋃₀ {Q v | v ∈ {v : List V3 | barV V (k + 1) v ∧
      truncateSimplex k v = truncateSimplex k vl}},
      ⟨truncateSimplex k vl, ⟨hbart, htwl⟩, rfl⟩, ?_⟩
    exact ⟨Q vl, ⟨vl, ⟨hb, rfl⟩, rfl⟩, hzT⟩
  · rintro ⟨W, ⟨wl, ⟨hbw, htw⟩, rfl⟩, hzW⟩
    obtain ⟨T, ⟨v, ⟨hb, hvw⟩, rfl⟩, hzT⟩ := hzW
    have hlen : v.length = k + 2 := hb.1
    have htv : truncateSimplex j (truncateSimplex k v) = ul := by
      rw [hvw]
      exact htw
    exact ⟨Q v, ⟨v, ⟨hb,
      (TRUNCATE_TRUNCATE_SIMPLEX v j k hjk (by omega)).symm.trans htv⟩, rfl⟩, hzT⟩

/-- Rogers.hl:826 `GLTVHUM_lemma1`. -/
theorem GLTVHUM_lemma1 (V : Set V3) (ul : List V3) (j : ℕ) (hP : Packing V)
    (hs : saturated V) (hj : j < 3) (hbar : barV V j ul) :
    {k : ℕ | k ∈ (Finset.Icc j 3 : Set ℕ) ∧ voronoiList V ul =
      ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j (k - 1)} ∪
        voronoiList V vl) | vl ∈ {vl : List V3 |
        barV V k vl ∧ truncateSimplex j vl = ul}}} = (Finset.Icc j 3 : Set ℕ) := by
  -- k-归纳（NUMSEG_SUBSET_INDUCT）。≡-claim：`barV V j` 家族是单点 {ul}
  -- （TRUNCATE_SIMPLEX_INITIAL_SUBLIST + TRUNCATE_SIMPLEX_REFL）。
  have hclaim : ∀ vl : List V3, barV V j vl ∧ truncateSimplex j vl = ul ↔ vl = ul := by
    intro vl
    constructor
    · rintro ⟨hbarvl, hts⟩
      have h1 := (TRUNCATE_SIMPLEX_INITIAL_SUBLIST j vl vl).2
        ⟨INITIAL_SUBLIST_REFL vl, hbarvl.1⟩
      exact (hts.symm.trans h1.1).symm
    · rintro rfl
      exact ⟨hbar, TRUNCATE_SIMPLEX_REFL _ _ hbar.1⟩
  -- base k=j：家族={ul}；j=0 用 VORONOI_LIST_SING+CENTER_IN_VORONOI_CELL+
  -- CONVEX_VORONOI_CLOSED，j>0 用 Icc_eq_empty+CONVEX_VORONOI_LIST。
  have hbase : voronoiList V ul =
      ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j (j - 1)} ∪
        voronoiList V vl) | vl ∈ {vl : List V3 |
        barV V j vl ∧ truncateSimplex j vl = ul}} := by
    have hsingleton : {vl : List V3 | barV V j vl ∧ truncateSimplex j vl = ul} = {ul} := by
      ext v
      simpa only [Set.mem_setOf_eq, Set.mem_singleton_iff] using hclaim v
    rw [hsingleton, p6_sUnion_singleton_image]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      obtain ⟨y, rfl⟩ := List.length_eq_one_iff.1 (show ul.length = 1 from hbar.1)
      rw [VORONOI_LIST_SING, show (0 : ℕ) - 1 = 0 from by omega]
      have h0 : {omegaListN V [y] i | i ∈ Finset.Icc 0 0} = {y} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Finset.mem_Icc]
        constructor
        · rintro ⟨i, hi1, hi2, rfl⟩
          rw [show i = 0 from by omega]
          rfl
        · rintro rfl
          exact ⟨0, by omega, rfl⟩
      rw [h0, Set.singleton_union,
        Set.insert_eq_of_mem (CENTER_IN_VORONOI_CELL V y).1,
        (CONVEX_VORONOI_CLOSED V y).convexHull_eq]
    · have hempty : Finset.Icc j (j - 1) = ∅ := Finset.Icc_eq_empty_iff.2 (by omega)
      have himge : {omegaListN V ul i | i ∈ Finset.Icc j (j - 1)} = (∅ : Set V3) := by
        rw [hempty]
        ext z
        simp
      rw [himge, Set.empty_union, (CONVEX_VORONOI_LIST V ul).convexHull_eq]
  -- step k→k+1：(A) p6_union_split 重排 → (B) stepB 壳-窗 rearrange →
  -- omega-窗 vl↔wl 逐点一致（OMEGA_LIST_N_LEMMA）→ p6_convexHull_sUnion_left
  -- （星引理；非空=BARV_EXISTS，凸性=ℂ-并=p6_gltvhum_union_g+CONVEX_
  -- VORONOI_LIST）→ p6_sUnion_image_image（𝒞-重指标）→ 归纳假设。
  have hstep : ∀ k : ℕ, j ≤ k → k + 1 ≤ 3 →
      (voronoiList V ul =
        ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j (k - 1)} ∪
          voronoiList V vl) | vl ∈ {vl : List V3 |
          barV V k vl ∧ truncateSimplex j vl = ul}}) →
      (voronoiList V ul =
        ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j k} ∪
          voronoiList V vl) | vl ∈ {vl : List V3 |
          barV V (k + 1) vl ∧ truncateSimplex j vl = ul}}) := by
    intro k hjk hk2 ih
    have hk3 : k < 3 := by omega
    -- (B) `hull (window ∪ cell) = hull (window' ∪ hull (ω_k insert cell))`
    have stepB : ∀ v : List V3,
        convexHull ℝ ({omegaListN V v i | i ∈ Finset.Icc j k} ∪ voronoiList V v) =
        convexHull ℝ ({omegaListN V v i | i ∈ Finset.Icc j (k - 1)} ∪
          convexHull ℝ (insert (omegaListN V v k) (voronoiList V v))) := by
      intro v
      rw [p6_convexHull_union_hull, Set.insert_eq, ← Set.union_assoc,
        ← p6_image_Icc_succ (omegaListN V v) j k hjk]
    -- (C)+(D) hinner：对固定 wl（barV V k wl），`vl`-族的并 = S_wl 的壳。
    have wl2 : ∀ wl : List V3, barV V k wl →
        ⋃₀ {convexHull ℝ ({omegaListN V v i | i ∈ Finset.Icc j k} ∪ voronoiList V v) |
            v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl}} =
        convexHull ℝ ({omegaListN V wl i | i ∈ Finset.Icc j (k - 1)} ∪
          voronoiList V wl) := by
      intro wl hbw
      have hkC := p6_gltvhum_union_g V wl k hP hs hk3 hbw
      obtain ⟨v0, hv0, hv0t⟩ := BARV_EXISTS V wl k hP hs hk3 hbw
      have hne : ({convexHull ℝ (insert (omegaListN V v k) (voronoiList V v)) |
          v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl}} :
            Set (Set V3)).Nonempty :=
        ⟨convexHull ℝ (insert (omegaListN V v0 k) (voronoiList V v0)),
          ⟨v0, ⟨hv0, hv0t⟩, rfl⟩⟩
      have hconv : Convex ℝ (⋃₀ {convexHull ℝ (insert (omegaListN V v k) (voronoiList V v)) |
          v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl}}) := by
        rw [hkC]
        exact CONVEX_VORONOI_LIST V wl
      have hstar := p6_convexHull_sUnion_left
        {omegaListN V wl i | i ∈ Finset.Icc j (k - 1)}
        {convexHull ℝ (insert (omegaListN V v k) (voronoiList V v)) |
          v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl}}
        hne hconv
      have hpt : ∀ v ∈ {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl},
          convexHull ℝ ({omegaListN V v i | i ∈ Finset.Icc j k} ∪ voronoiList V v) =
          convexHull ℝ ({omegaListN V wl i | i ∈ Finset.Icc j (k - 1)} ∪
            convexHull ℝ (insert (omegaListN V v k) (voronoiList V v))) := by
        intro v hv
        obtain ⟨hb, htk⟩ := hv
        have hlen : v.length = k + 2 := hb.1
        rw [stepB v]
        have hom : ∀ i, j ≤ i → i ≤ k - 1 → omegaListN V v i = omegaListN V wl i := by
          intro i hi1 hi2
          have h5 := OMEGA_LIST_N_LEMMA V v i (k - i) (by omega)
          rw [show i + (k - i) = k from by omega] at h5
          rw [htk] at h5
          exact h5
        have himg : {omegaListN V v i | i ∈ Finset.Icc j (k - 1)} =
            {omegaListN V wl i | i ∈ Finset.Icc j (k - 1)} := by
          ext z
          simp only [Set.mem_setOf_eq, Finset.mem_Icc]
          constructor
          · rintro ⟨i, hi, rfl⟩
            refine ⟨i, hi, ?_⟩
            rw [hom i hi.1 hi.2]
          · rintro ⟨i, hi, rfl⟩
            refine ⟨i, hi, ?_⟩
            rw [hom i hi.1 hi.2]
        rw [himg]
      exact (p6_sUnion_image_congr hpt).trans
        ((p6_sUnion_image_image
            (F := {v : List V3 | barV V (k + 1) v ∧ truncateSimplex k v = wl})
            (fun v => convexHull ℝ (insert (omegaListN V v k) (voronoiList V v)))
            (fun c => convexHull ℝ ({omegaListN V wl i | i ∈ Finset.Icc j (k - 1)} ∪ c))).trans
          (hstar.symm.trans (by rw [hkC])))
    -- (A) 拆分后逐 wl 套 wl2，收回归纳假设。
    rw [p6_union_split V ul j k hjk
      (fun vl => convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j k} ∪
        voronoiList V vl))]
    refine ih.trans (p6_sUnion_image_congr ?_).symm
    intro wl hwl
    obtain ⟨hbw, -⟩ := hwl
    exact wl2 wl hbw
  ext k
  constructor
  · rintro ⟨hk, -⟩
    exact hk
  · intro hk
    have hkle : j ≤ k ∧ k ≤ 3 := Finset.mem_Icc.1 (Finset.mem_coe.1 hk)
    exact NUMSEG_SUBSET_INDUCT
      (fun k : ℕ => k ∈ (Finset.Icc j 3 : Set ℕ) ∧
        voronoiList V ul =
          ⋃₀ {convexHull ℝ ({omegaListN V vl i | i ∈ Finset.Icc j (k - 1)} ∪
            voronoiList V vl) | vl ∈ {vl : List V3 |
            barV V k vl ∧ truncateSimplex j vl = ul}})
      j 3
      ⟨Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨le_refl j, Nat.le_of_lt hj⟩), hbase⟩
      (fun k hk1 hk2 hmem =>
        ⟨Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨Nat.le_succ_of_le hk1, hk2⟩),
          hstep k hk1 hk2 hmem.2⟩)
      (Set.mem_Icc.2 hkle)

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

/-- Rogers.hl:1267 `ODIGPXU_lemma`. (The `polyhedron` hypothesis is not
needed: the equality of the two rays from `p0` through the facet points
`p`, `q` forces `q` onto the open segment `p0`–`p` unless `s ≤ t`, and the
face condition of `f'` then pulls `p0` into `f'`.) -/
theorem ODIGPXU_lemma (P f f' : Set V3) (p0 p q : V3) (t s : ℝ) (hP : polyhedron P)
    (hp0 : p0 ∈ P) (hf : p0 ∉ f ∪ f') (h1 : FacetOf f P) (h2 : FacetOf f' P)
    (hp : p ∈ f) (hq : q ∈ f') (ht : 0 < t) (hs : 0 < s)
    (heq : (1 - t) • p0 + t • p = (1 - s) • p0 + s • q) : s ≤ t := by
  by_contra hcon
  have hst : t < s := lt_of_not_ge hcon
  have hsnz : s ≠ 0 := ne_of_gt hs
  -- rewrite the ray equality as `q = p0 + (t/s) • (p - p0)`
  have hq2 : q = (1 - t / s) • p0 + (t / s) • p := by
    have h1 : s • q = (s - t) • p0 + t • p := by
      have e1 : s • q + (1 - s) • p0 = (1 - t) • p0 + t • p := by
        rw [heq]; abel
      linear_combination (norm := module) e1
    have h2 : s • q = s • ((1 - t / s) • p0 + (t / s) • p) := by
      rw [h1, smul_add, smul_smul, smul_smul]
      have hA : s * (1 - t / s) = s - t := by field_simp
      have hB : s * (t / s) = t := by field_simp
      rw [hA, hB]
    exact smul_right_injective V3 hsnz h2
  have hseg : q ∈ openSegment ℝ p0 p := by
    rw [hq2]
    simp only [openSegment, Set.mem_setOf_eq]
    refine ⟨1 - t / s, t / s, ?_, div_pos ht hs, by ring, rfl⟩
    rw [sub_pos, div_lt_one hs]
    exact hst
  obtain ⟨h2fo, -, -⟩ := h2
  obtain ⟨h1fo, -, -⟩ := h1
  have hpP : p ∈ P := h1fo.1 hp
  obtain ⟨ha, -⟩ := h2fo.2.2 p0 p q hp0 hpP hq hseg
  exact hf (Or.inr ha)

/-- Rogers.hl:1321 `ODIGPXU`. -/
theorem ODIGPXU (P f f' : Set V3) (p0 p q : V3) (t s : ℝ) (hP : polyhedron P)
    (hp0 : p0 ∈ P) (hf : p0 ∉ f ∪ f') (h1 : FacetOf f P) (h2 : FacetOf f' P)
    (hp : p ∈ f) (hq : q ∈ f') (ht : 0 < t) (hs : 0 < s)
    (heq : (1 - t) • p0 + t • p = (1 - s) • p0 + s • q) : s = t :=
  le_antisymm (ODIGPXU_lemma P f f' p0 p q t s hP hp0 hf h1 h2 hp hq ht hs heq)
    (ODIGPXU_lemma P f' f p0 q p s t hP hp0 (by rw [Set.union_comm]; exact hf) h2 h1
      hq hp hs ht heq.symm)

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

/-- Rogers.hl:1360 `OMEGA_LIST_N_IN_FACET`. -/
theorem OMEGA_LIST_N_IN_FACET (V : Set V3) (ul : List V3) (k i : ℕ) (hP : Packing V)
    (hs : saturated V) (hbar : barV V k ul) (hik : i < k) :
    ∃ F : Set V3, FacetOf F (voronoiList V (truncateSimplex i ul)) ∧
      voronoiList V (truncateSimplex (i + 1) ul) = F ∧
      ∀ j, i < j → j ≤ k → omegaListN V ul j ∈ F := by
  have hkle : k ≤ 3 := BARV_IMP_K_LE_3 V ul k hbar
  have hilt : i < 3 := by omega
  have hbi : barV V i (truncateSimplex i ul) :=
    TRUNCATE_SIMPLEX_BARV V i k ul hbar (by omega)
  refine ⟨voronoiList V (truncateSimplex (i + 1) ul), ?_, rfl, ?_⟩
  · rw [IDBEZAL V (truncateSimplex i ul) i
      (voronoiList V (truncateSimplex (i + 1) ul)) hs hP hbi hilt]
    refine ⟨truncateSimplex (i + 1) ul, rfl,
      TRUNCATE_SIMPLEX_BARV V (i + 1) k ul hbar (by omega), ?_⟩
    exact TRUNCATE_TRUNCATE_SIMPLEX ul i (i + 1) (by omega)
      (by have := hbar.1; omega)
  · intro j hj hjk
    exact voronoiList_initialSublist_mono V (truncateSimplex (i + 1) ul)
      (truncateSimplex j ul)
      (initialSublist_truncate_truncate ul (by omega) (by have := hbar.1; omega))
      (OMEGA_LIST_N_IN_VORONOI_LIST V ul k j hbar hjk)

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

/-! ### dimension/coplanarity kit（PA2 DUUNHOR 波链复制：PA2 侧 p2g_ 件为 private
不可见，自 /tmp/pa2_duu_probe.lean 探针照抄证明体，探针全绿后落盘。）-/

-- membership transport along direction inclusion
private theorem p6b_affineSpan_subset {s t : Set V3} {p : V3} (hps : p ∈ s) (hpt : p ∈ t)
    (hdir : vectorSpan ℝ s ≤ vectorSpan ℝ t) : s ⊆ (affineSpan ℝ t : Set V3) := by
  intro x hx
  have hdir2 : (x -ᵥ p : V3) ∈ (affineSpan ℝ t).direction := by
    rw [direction_affineSpan]
    exact hdir (vsub_mem_vectorSpan ℝ hx hps)
  have h0 : p ∈ (affineSpan ℝ t : Set V3) := SetLike.mem_coe.mpr (mem_affineSpan ℝ hpt)
  have hv := AffineSubspace.vadd_mem_of_mem_direction hdir2 h0
  rw [vadd_eq_add] at hv
  have hx2 : (x -ᵥ p) + p = x := by rw [← vadd_eq_add, vsub_vadd]
  rwa [hx2] at hv

-- generic: finrank of a 2-way sup ≤ sum
private theorem p6b_finrank_sup_le (M N : Submodule ℝ V3) :
    Module.finrank ℝ ↥(M ⊔ N) ≤ Module.finrank ℝ ↥M + Module.finrank ℝ ↥N := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq M N
  have h0 : (0 : ℕ) ≤ Module.finrank ℝ ↥(M ⊓ N) := Nat.zero_le _
  have h1 : (0 : ℕ) ≤ Module.finrank ℝ ↥(M ⊔ N) := Nat.zero_le _
  omega

/-- The core extraction: a submodule of finrank ≤ 2 is contained in the span of two vectors. -/
private theorem p6b_span_two_of_finrank {W : Submodule ℝ V3}
    (hfr : Module.finrank ℝ ↥W ≤ 2) :
    ∃ d : Fin 2 → V3, ↑W ≤ Submodule.span ℝ (Set.range d) := by
  classical
  set B := Module.finBasis ℝ ↥W with hBdef
  set n := Module.finrank ℝ ↥W with hn
  set g : Fin n → V3 := fun j => ((B j : ↥W) : V3) with hg
  set d : Fin 2 → V3 := fun i => if h : (i : ℕ) < n then g ⟨i, h⟩ else 0 with hddef
  refine ⟨d, ?_⟩
  have hspan : ↑W = Submodule.span ℝ (Set.range g) := by
    conv_lhs => rw [← Submodule.map_subtype_top W]
    rw [← B.span_eq, LinearMap.map_span]
    have himg : W.subtype '' Set.range B = Set.range g := by
      ext z
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨y, ⟨j, hj⟩, rfl⟩
        exact ⟨j, by show (B j : V3) = (y : V3); rw [hj]⟩
      · rintro ⟨j, rfl⟩
        exact ⟨B j, ⟨j, rfl⟩, rfl⟩
    rw [himg]
  have hsub : Set.range g ⊆ Set.range d := by
    rintro z ⟨i, rfl⟩
    have hlt : (↑i : ℕ) < 2 := lt_of_lt_of_le i.isLt hfr
    exact ⟨⟨i, hlt⟩, by simp only [hddef, dif_pos i.isLt]⟩
  rw [hspan]
  exact Submodule.span_mono hsub

/-- Rogers.hl:1521 `AFF_DIM_LE_2_IMP_COPLANAR`. -/
theorem AFF_DIM_LE_2_IMP_COPLANAR (s : Set V3) (h : affDim s ≤ 2) : Coplanar s := by
  classical
  rcases Set.eq_empty_or_nonempty s with hs0 | hsne
  · subst hs0
    exact ⟨0, 0, 0, Set.empty_subset _⟩
  · obtain ⟨p0, hp0s⟩ := hsne
    have hsne : s ≠ ∅ := nonempty_iff_ne_empty.1 ⟨p0, hp0s⟩
    rw [affDim, if_neg hsne] at h
    obtain ⟨d, hd⟩ := p6b_span_two_of_finrank (Int.ofNat_le.mp h)
    refine ⟨p0, p0 + d 0, p0 + d 1, ?_⟩
    refine p6b_affineSpan_subset hp0s (by simp) ?_
    refine le_trans hd ?_
    rw [vectorSpan_eq_span_vsub_set_right ℝ (by simp :
      p0 ∈ ({p0, p0 + d 0, p0 + d 1} : Set V3))]
    refine Submodule.span_mono ?_
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    refine ⟨p0 + d i, ?_, by simp [vsub_eq_sub]⟩
    fin_cases i <;> simp

/-- Rogers.hl:1559 `ROGERS_AFF_DIM_FULL`. -/
theorem ROGERS_AFF_DIM_FULL (V : Set V3) (ul : List V3) (hbar : barV V 3 ul)
    (hdim : affDim (rogers V ul) = 3) :
    ∀ i j : ℕ, i < 4 → j < 4 → i ≠ j → omegaListN V ul i ≠ omegaListN V ul j := by
  classical
  have h4len : ul.length = 4 := by simp [hbar.1]
  intro i j hi4 hj4 hij hcol
  set u : V3 := omegaListN V ul i with hudef
  -- the Rogers simplex is the hull of the (at most) four omega points
  set S : Set V3 := omegaListN V ul '' {k : ℕ | k < 4} with hSdef
  have hrogers : rogers V ul = convexHull ℝ S := by
    rw [rogers, h4len]
  have hSne : S.Nonempty := ⟨u, ⟨i, hi4, rfl⟩⟩
  -- the two indices other than `i` and `j` span everything once omega i = omega j
  set TT : Finset ℕ := ((Finset.range 4).erase i).erase j with hTTdef
  have hTTcard : TT.card = 2 := by
    rw [Finset.card_erase_of_mem
      (Finset.mem_erase.2 ⟨fun h => hij h.symm, Finset.mem_range.2 hj4⟩),
      Finset.card_erase_of_mem (Finset.mem_range.2 hi4)]
    simp
  have h2 : vectorSpan ℝ S ≤
      Submodule.span ℝ ↑(TT.image (fun k : ℕ => omegaListN V ul k -ᵥ u)) := by
    have huS : u ∈ S := ⟨i, hi4, rfl⟩
    rw [vectorSpan_eq_span_vsub_set_right_ne ℝ huS]
    refine Submodule.span_mono ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨hxS, hxne⟩ := (Set.mem_sdiff x).mp hx
    obtain ⟨m, hm4, rfl⟩ := hxS
    have hmi : m ≠ i := by
      intro hcon
      apply hxne
      rw [hcon]
      exact Set.mem_singleton_iff.2 hudef.symm
    have hmj : m ≠ j := by
      intro hcon
      apply hxne
      rw [hcon]
      exact Set.mem_singleton_iff.2 hcol.symm
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨m, ?_, rfl⟩)
    exact Finset.mem_erase.2 ⟨hmj, Finset.mem_erase.2 ⟨hmi, Finset.mem_range.2 hm4⟩⟩
  -- hence the vector span of the hull of S has dimension at most 2
  have hmono : vectorSpan ℝ ↑(convexHull ℝ S) ≤ vectorSpan ℝ S := by
    have hstep : vectorSpan ℝ ↑(convexHull ℝ S) ≤
        vectorSpan ℝ ↑(affineSpan ℝ S) :=
      vectorSpan_mono ℝ (convexHull_subset_affineSpan S)
    rw [← AffineSubspace.direction_eq_vectorSpan (affineSpan ℝ S),
      direction_affineSpan] at hstep
    exact hstep
  have h3 : Module.finrank ℝ (vectorSpan ℝ ↑(convexHull ℝ S)) ≤ 2 := by
    refine le_trans (Submodule.finrank_mono hmono) ?_
    set F : Finset V3 := TT.image (fun k : ℕ => omegaListN V ul k -ᵥ u) with hFdef
    calc Module.finrank ℝ (vectorSpan ℝ S)
        ≤ Module.finrank ℝ (Submodule.span ℝ (↑F : Set V3)) := Submodule.finrank_mono h2
      _ ≤ F.card :=
          le_trans (finrank_span_le_card (↑F : Set V3)) (by simp)
      _ ≤ TT.card := Finset.card_image_le
      _ = 2 := hTTcard
  -- but the hull of S is the Rogers simplex of dimension 3
  have hcne : (convexHull ℝ S) ≠ ∅ := by
    intro hcon
    obtain ⟨x, hx⟩ := hSne
    have hx' : x ∈ convexHull ℝ S := subset_convexHull ℝ S hx
    rw [hcon] at hx'
    exact hx'
  have hbound : affDim (convexHull ℝ S) ≤ 2 := by
    rw [affDim, if_neg hcne]
    exact Nat.cast_le.2 h3
  have hdimhull : affDim (convexHull ℝ S) = 3 := by
    rw [← hrogers]
    exact hdim
  linarith

set_option maxHeartbeats 1000000 in
/-- Rogers.hl:1657 `AFF_DIM_FINITE_UNION_LE`. -/
theorem AFF_DIM_FINITE_UNION_LE (s t : Set V3) (hs : s.Finite) :
    affDim (s ∪ t) ≤ (Nat.card s : ℤ) + affDim t := by
  classical
  rcases Set.eq_empty_or_nonempty s with hse | hsne
  · rw [hse, Set.empty_union]
    have h0 : (0 : ℤ) ≤ (Nat.card (↑(∅ : Set V3)) : ℤ) := by
      have hz : Nat.card (↑(∅ : Set V3)) = 0 :=
        Nat.card_eq_zero.mpr (Or.inl (⟨IsEmpty.false⟩ : IsEmpty (↑(∅ : Set V3))))
      omega
    exact le_add_of_nonneg_left h0
  · obtain ⟨y0, hy0s⟩ := hsne
    have hsne : s ≠ ∅ := nonempty_iff_ne_empty.1 ⟨y0, hy0s⟩
    haveI := hs.fintype
    set S : Finset V3 := hs.toFinset.erase y0 with hS
    set A : Finset V3 := S.image (fun x : V3 => x -ᵥ y0) with hA
    have hy0S : y0 ∈ hs.toFinset := (hs.mem_toFinset).mpr hy0s
    have hcard : Nat.card s = hs.toFinset.card := by
      rw [Nat.card_eq_fintype_card, hs.card_toFinset]
    have hScard : S.card + 1 = Nat.card s := by
      rw [hS, hcard, Finset.card_erase_add_one hy0S]
    have hspanA : Submodule.span ℝ ((fun x : V3 => x -ᵥ y0) '' s) ≤
        Submodule.span ℝ (↑A : Set V3) := by
      rw [Submodule.span_le]
      rintro z ⟨x, hx, rfl⟩
      by_cases hxy : x = y0
      · subst hxy; simp
      · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨x,
          (Finset.mem_erase.2 ⟨hxy, (hs.mem_toFinset).mpr hx⟩), rfl⟩))
    have hAfr : Module.finrank ℝ (Submodule.span ℝ (↑A : Set V3)) ≤ A.card :=
      finrank_span_finset_le_card A
    have hAcard : (A.card : ℤ) ≤ (Nat.card s : ℤ) - 1 := by
      have h2 : A.card ≤ S.card := Finset.card_image_le
      rw [hcard]
      have h3 : (S.card : ℤ) + 1 = ((hs.toFinset.card : ℕ) : ℤ) := by
        exact_mod_cast hScard.trans hcard
      linarith
    rcases Set.eq_empty_or_nonempty t with hte | htne
    · rw [hte, Set.union_empty, affDim_empty, affDim, if_neg hsne]
      have hvs : vectorSpan ℝ s = Submodule.span ℝ ((fun x : V3 => x -ᵥ y0) '' s) :=
        vectorSpan_eq_span_vsub_set_right ℝ hy0s
      rw [hvs]
      have hmono : Module.finrank ℝ (Submodule.span ℝ ((fun x : V3 => x -ᵥ y0) '' s)) ≤
          Module.finrank ℝ (Submodule.span ℝ (↑A : Set V3)) := Submodule.finrank_mono hspanA
      have h1 : (Module.finrank ℝ (Submodule.span ℝ ((fun x : V3 => x -ᵥ y0) '' s)) : ℤ)
          ≤ (Nat.card s : ℤ) - 1 := by
        have h3 := hmono
        have h4 := hAfr
        omega
      linarith
    · obtain ⟨x0, hx0⟩ := htne
      have htne : t ≠ ∅ := nonempty_iff_ne_empty.1 ⟨x0, hx0⟩
      set D : Set V3 := {(x0 -ᵥ y0 : V3)} with hD
      set BIG : Set V3 := (↑A : Set V3) ∪ ((vectorSpan ℝ t : Set V3) ∪ D) with hBIG
      have hAS : Submodule.span ℝ (↑A : Set V3) ≤ Submodule.span ℝ BIG := by
        refine Submodule.span_mono ?_
        intro z hz
        exact Set.mem_union_left _ hz
      have hTS : ∀ x ∈ vectorSpan ℝ t, (x : V3) ∈ Submodule.span ℝ BIG := by
        intro x hx
        refine Submodule.span_mono (fun w hw => Set.mem_union_right (↑A : Set V3)
          (Set.mem_union_left D hw)) (Submodule.subset_span (by exact hx))
      have hDS : Submodule.span ℝ D ≤ Submodule.span ℝ BIG := by
        refine Submodule.span_mono ?_
        intro z hz
        exact Set.mem_union_right (↑A : Set V3)
          (Set.mem_union_right (↑(vectorSpan ℝ t) : Set V3) hz)
      have hneg : ∀ {K : Submodule ℝ V3} {x : V3}, x ∈ K → -x ∈ K := fun hx => by
        simpa using Submodule.smul_mem _ (-1) hx
      have hkey : vectorSpan ℝ (s ∪ t) ≤ Submodule.span ℝ BIG := by
        rw [vectorSpan_def, Submodule.span_le]
        rintro z ⟨p, hp, q, hq, rfl⟩
        simp only [Set.mem_union] at hp hq
        have hzero' : (0 : V3) ∈ (Submodule.span ℝ BIG : Submodule ℝ V3) :=
          Submodule.zero_mem _
        have hxy2' : (x0 -ᵥ y0 : V3) ∈ (D : Set V3) := by rw [hD]; simp
        have hAdiff : ∀ x ∈ s, (x -ᵥ y0 : V3) ∈ Submodule.span ℝ (↑A : Set V3) := by
          intro x hx
          by_cases hxy : x = y0
          · subst hxy; simp
          · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨x,
              (Finset.mem_erase.2 ⟨hxy, (hs.mem_toFinset).mpr hx⟩), rfl⟩))
        have hxy2 : (x0 -ᵥ y0 : V3) ∈ Submodule.span ℝ {(x0 -ᵥ y0 : V3)} :=
          Submodule.subset_span (by simp)
        rcases hp with hp | hp <;> rcases hq with hq | hq
        · show (p -ᵥ q : V3) ∈ Submodule.span ℝ BIG
          have heq : (p -ᵥ q : V3) = (p -ᵥ y0) - (q -ᵥ y0) := by
            simp only [vsub_eq_sub]
            abel
          rw [heq]
          exact Submodule.sub_mem _ (hAS (hAdiff p hp)) (hAS (hAdiff q hq))
        · show (p -ᵥ q : V3) ∈ Submodule.span ℝ BIG
          have h1 : (p -ᵥ y0 : V3) ∈ Submodule.span ℝ BIG := hAS (hAdiff p hp)
          have h2 : -(x0 -ᵥ y0 : V3) ∈ Submodule.span ℝ BIG :=
            hDS (hneg (Submodule.subset_span hxy2'))
          have h3 : -(q -ᵥ x0 : V3) ∈ Submodule.span ℝ BIG :=
            hTS _ (hneg (vsub_mem_vectorSpan ℝ hq hx0))
          have hdecomp : (p -ᵥ q : V3) = (p -ᵥ y0) + -(x0 -ᵥ y0) + -(q -ᵥ x0) := by
            simp only [vsub_eq_sub]
            abel
          rw [hdecomp]
          exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3
        · show (p -ᵥ q : V3) ∈ Submodule.span ℝ BIG
          have h1 : (p -ᵥ x0 : V3) ∈ Submodule.span ℝ BIG :=
            hTS _ (vsub_mem_vectorSpan ℝ hp hx0)
          have h2 : (x0 -ᵥ y0 : V3) ∈ Submodule.span ℝ BIG :=
            hDS (Submodule.subset_span hxy2')
          have h3 : -(q -ᵥ y0 : V3) ∈ Submodule.span ℝ BIG :=
            hAS (hneg (hAdiff q hq))
          have hdecomp : (p -ᵥ q : V3) = (p -ᵥ x0) + (x0 -ᵥ y0) + -(q -ᵥ y0) := by
            simp only [vsub_eq_sub]
            abel
          rw [hdecomp]
          exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3
        · show (p -ᵥ q : V3) ∈ Submodule.span ℝ BIG
          exact hTS _ (vsub_mem_vectorSpan ℝ hp hq)
      -- assemble the finrank bound
      have hunion : (s ∪ t).Nonempty := ⟨y0, Set.mem_union_left _ hy0s⟩
      have hsup2 : Module.finrank ℝ (Submodule.span ℝ BIG) ≤
          A.card + Module.finrank ℝ (vectorSpan ℝ t) + 1 := by
        have hA : Module.finrank ℝ (Submodule.span ℝ (↑A : Set V3)) ≤ A.card :=
          finrank_span_finset_le_card A
        have h1 : Module.finrank ℝ (Submodule.span ℝ D) ≤ 1 := by
          rw [hD]
          by_cases hv0 : (x0 -ᵥ y0 : V3) = 0
          · have hz : (ℝ ∙ (x0 -ᵥ y0 : V3)) = (⊥ : Submodule ℝ V3) := by
              have hz0 : (x0 -ᵥ y0 : V3) = 0 := hv0
              rw [hz0]
              exact Submodule.span_singleton_eq_bot.mpr rfl
            rw [hz]; simp
          · exact le_of_eq (finrank_span_singleton hv0)
        have hT : Module.finrank ℝ (Submodule.span ℝ (↑(vectorSpan ℝ t) : Set V3))
            = Module.finrank ℝ (vectorSpan ℝ t) := by
          rw [Submodule.span_eq (vectorSpan ℝ t)]
        rw [hBIG, Submodule.span_union, Submodule.span_union]
        have e1 := p6b_finrank_sup_le (Submodule.span ℝ (↑A : Set V3))
          (Submodule.span ℝ ((↑(vectorSpan ℝ t) : Set V3) ∪ D))
        rw [Submodule.span_union] at e1
        have e2 := p6b_finrank_sup_le (Submodule.span ℝ (↑(vectorSpan ℝ t) : Set V3))
          (Submodule.span ℝ D)
        omega
      have hstep : (affDim (s ∪ t) : ℤ) ≤ (A.card : ℤ) + affDim t + 1 := by
        rw [affDim, if_neg (nonempty_iff_ne_empty.1 hunion)]
        have hmono : Module.finrank ℝ (vectorSpan ℝ (s ∪ t)) ≤
            Module.finrank ℝ (Submodule.span ℝ BIG) := Submodule.finrank_mono hkey
        have h4 : Module.finrank ℝ (vectorSpan ℝ t) = affDim t := by
          rw [affDim, if_neg htne]
        omega
      linarith

/-- Rogers.hl:1682 `DUUNHOR`: distinct Rogers simplices meet in a coplanar
set. (The `packing`/`saturated` hypotheses are consumed by
`PackingAuto2.DUUNHOR_concl`; the r2 statement-fix added them there —
see docs/statement-fix-proposals.md item 13.) -/
theorem DUUNHOR (V : Set V3) (ul vl : List V3) (hP : Packing V) (hs : saturated V)
    (hul : barV V 3 ul) (hvl : barV V 3 vl) (hne : rogers V ul ≠ rogers V vl) :
    Coplanar (rogers V ul ∩ rogers V vl) :=
  DUUNHOR_concl V ul vl hP hs hul hvl hne

/-- Rogers.hl:3106 `AFFINE_INDEPENDENT_IMP_INDEPENDENT`. -/
theorem AFFINE_INDEPENDENT_IMP_INDEPENDENT (S : Set V3) (hS : ¬affineDependent S) :
    ∀ x ∈ S, LinearIndependent ℝ (fun y : (S \ {x} : Set V3) => (y : V3) - x) := by
  intro x hx
  rw [affineDependent, not_not,
    affineIndependent_set_iff_linearIndependent_vsub (k := ℝ) hx] at hS
  -- transport the index type: the image set is the family `y ↦ y - x` in range form
  have hcoee : ((fun v : ↥((fun p : V3 => (p -ᵥ x : V3)) '' (S \ {x})) => (v : V3)) ∘
      (Equiv.Set.image (fun z : V3 => z - x) (S \ {x})
        (fun z₁ z₂ h => by
          have h2 := congrArg (fun z : V3 => z + x) h
          simpa using h2))) =
      (fun y : (S \ {x} : Set V3) => ((y : V3) - x)) := by
    funext y
    simp [Equiv.Set.image_apply]
  exact (linearIndependent_equiv'
    (Equiv.Set.image (fun z : V3 => z - x) (S \ {x})
      (fun z₁ z₂ h => by
        have h2 := congrArg (fun z : V3 => z + x) h
        simpa using h2)) hcoee).mpr hS

/-- Rogers.hl:3141 `ORTHOGONAL_TO_SPAN_EXISTS`. -/
theorem ORTHOGONAL_TO_SPAN_EXISTS (s t : Set V3)
    (h1 : s ⊆ (Submodule.span ℝ t : Set V3))
    (h2 : Module.finrank ℝ (Submodule.span ℝ s) <
      Module.finrank ℝ (Submodule.span ℝ t)) :
    ∃ v : V3, v ≠ 0 ∧ v ∈ Submodule.span ℝ t ∧ ∀ x ∈ s, x ⬝ᵥ v = 0 := by
  have hUW : (Submodule.span ℝ s : Submodule ℝ V3) ≤ Submodule.span ℝ t :=
    Submodule.span_le.2 h1
  have hfd : Module.finrank ℝ (Submodule.span ℝ s) +
      (Module.finrank ℝ (Submodule.span ℝ t) -
        Module.finrank ℝ (Submodule.span ℝ s)) =
      Module.finrank ℝ (Submodule.span ℝ t) := by omega
  have hKfr : Module.finrank ℝ ↥((Submodule.span ℝ s)ᗮ ⊓ Submodule.span ℝ t) =
      Module.finrank ℝ (Submodule.span ℝ t) -
        Module.finrank ℝ (Submodule.span ℝ s) :=
    Submodule.finrank_add_inf_finrank_orthogonal' hUW hfd
  have hKne : ((Submodule.span ℝ s)ᗮ ⊓ Submodule.span ℝ t : Submodule ℝ V3) ≠ ⊥ := by
    intro hcon
    rw [hcon] at hKfr
    have h0 : Module.finrank ℝ (Submodule.span ℝ t) -
        Module.finrank ℝ (Submodule.span ℝ s) = 0 := by
      rw [← hKfr]
      exact finrank_bot ℝ V3
    omega
  obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKne
  refine ⟨v, hv0, hvK.2, ?_⟩
  intro x hx
  have hxU : x ∈ (Submodule.span ℝ s : Submodule ℝ V3) := Submodule.subset_span hx
  have horth := (Submodule.mem_orthogonal (Submodule.span ℝ s) v).1 hvK.1 x hxU
  exact (inner_eq_dot x v).symm.trans horth

/-- Rogers.hl:3286 `ORTHOGONAL_TO_ALL_IMP_ZERO`. -/
theorem ORTHOGONAL_TO_ALL_IMP_ZERO (v : V3) (s : Set V3)
    (h1 : v ∈ Submodule.span ℝ s) (h2 : ∀ x ∈ s, v ⬝ᵥ x = 0) : v = 0 := by
  have hss : (Submodule.span ℝ s) ≤ LinearMap.ker (innerSL ℝ v).toLinearMap := by
    rw [Submodule.span_le]
    rintro x hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply]
    rw [inner_eq_dot]
    exact h2 x hx
  have hself : inner ℝ v v = 0 := by
    have hk := hss h1
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at hk
    exact hk
  rw [inner_self_eq_zero] at hself
  exact hself

/-- Rogers.hl:3224 `INDEPENDENT_EXPLICIT_NUMSEG`. -/
theorem INDEPENDENT_EXPLICIT_NUMSEG (v : ℕ → V3) (f : ℕ → ℝ) (n : ℕ)
    (h1 : ∀ i j : ℕ, i ∈ Finset.Icc 1 n → j ∈ Finset.Icc 1 n → v i = v j → i = j)
    (h2 : LinearIndependent ℝ (fun i : (Finset.Icc (1 : ℕ) n : Finset ℕ) => v (i : ℕ)))
    (h3 : (∑ i ∈ Finset.Icc (1 : ℕ) n, f i • v (i : ℕ)) = 0) :
    ∀ i ∈ Finset.Icc (1 : ℕ) n, f i = 0 := by
  have key : ∀ j : (Finset.Icc (1 : ℕ) n : Finset ℕ), f (j : ℕ) = 0 :=
    (Fintype.linearIndependent_iff.mp h2
      (fun i : (Finset.Icc (1 : ℕ) n : Finset ℕ) => f (i : ℕ))
      (by
        have heq := Finset.sum_coe_sort (Finset.Icc (1 : ℕ) n)
          (fun i : ℕ => f i • v i)
        rw [heq]
        exact h3))
  intro i hi
  exact key ⟨i, hi⟩

/-- Rogers.hl:3325 `UNIQUE_SOLUTION_lemma`. -/
theorem UNIQUE_SOLUTION_lemma (S : Set V3) (b : V3 → ℝ)
    (hS : LinearIndependent ℝ (fun x : S => (x : V3))) :
    ∃! p : V3, p ∈ Submodule.span ℝ S ∧ ∀ x ∈ S, p ⬝ᵥ x = b x := by
  classical
  have hSfin : S.Finite := hS.setFinite
  haveI : Fintype ↥S := hSfin.fintype
  have hrange : Set.range (fun x : S => (x : V3)) = (↑S : Set V3) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  have hfrU : Module.finrank ℝ (Submodule.span ℝ (↑S : Set V3)) = Fintype.card ↥S := by
    have h := finrank_span_eq_card hS
    rwa [hrange] at h
  -- the pairing linear map `p ↦ (⟪p, x⟫)_{x ∈ S}`
  set g : (Submodule.span ℝ (↑S : Set V3)) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun p x => inner ℝ (p : V3) (x : V3)
      map_add' := by
        intro p q
        funext x
        simp [Submodule.coe_add, inner_add_left]
      map_smul' := by
        intro r p
        funext x
        simp [real_inner_smul_left] } with hg
  have hgApp : ∀ (p : Submodule.span ℝ (↑S : Set V3)) (x : S),
      g p x = inner ℝ (p : V3) (x : V3) := fun p x => rfl
  -- injectivity: a vector pairing trivially with all of S and lying in the span is 0
  have hkinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro p hp
    simp only [LinearMap.mem_ker] at hp
    have hp0 : ∀ x ∈ S, inner ℝ (p : V3) (x : V3) = 0 := by
      intro x hx
      have h1 := congrFun hp ⟨x, hx⟩
      rw [hgApp] at h1
      simpa using h1
    have hsub : Submodule.span ℝ (↑S : Set V3) ≤
        LinearMap.ker (innerSL ℝ (p : V3)).toLinearMap := by
      rw [Submodule.span_le]
      rintro x hx
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        innerSL_apply_apply]
      exact hp0 x hx
    have hpp : inner ℝ (p : V3) (p : V3) = 0 := by
      have h1 := hsub p.2
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at h1
      exact h1
    rw [inner_self_eq_zero] at hpp
    exact Subtype.ext hpp
  -- equal finranks upgrade injectivity to surjectivity
  have hsurj : Function.Surjective g := by
    have hdim : Module.finrank ℝ (Submodule.span ℝ (↑S : Set V3)) =
        Module.finrank ℝ (S → ℝ) := by
      rw [Module.finrank_pi ℝ, hfrU]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hkinj
  obtain ⟨p, hp⟩ := hsurj (fun x : ↥S => b (x : V3))
  have hpPair : ∀ x ∈ S, (p : V3) ⬝ᵥ x = b x := by
    intro x hx
    have h1 := congrFun hp ⟨x, hx⟩
    rw [hgApp] at h1
    exact (inner_eq_dot (p : V3) x).symm.trans h1
  refine ⟨(p : V3), ⟨p.2, hpPair⟩, ?_⟩
  · rintro q ⟨hqU, hq⟩
    have hd : q - (p : V3) ∈ Submodule.span ℝ (↑S : Set V3) :=
      Submodule.sub_mem _ hqU p.2
    have hd0 : ∀ x ∈ S, inner ℝ (q - (p : V3)) (x : V3) = 0 := by
      intro x hx
      have h1 := hq x hx
      have h2 := hpPair x hx
      rw [inner_sub_left, inner_eq_dot, inner_eq_dot, h1, h2, sub_self]
    have hdker : Submodule.span ℝ (↑S : Set V3) ≤
        LinearMap.ker (innerSL ℝ (q - (p : V3))).toLinearMap := by
      rw [Submodule.span_le]
      rintro x hx
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        innerSL_apply_apply]
      exact hd0 x hx
    have hdd : inner ℝ (q - (p : V3)) (q - (p : V3)) = 0 := by
      have h1 := hdker hd
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at h1
      exact h1
    rw [inner_self_eq_zero] at hdd
    exact sub_eq_zero.mp hdd

/-- Rogers.hl:3609 `UNIQUE_SOLUTION_AFFINE_INDEPENDENT`. -/
theorem UNIQUE_SOLUTION_AFFINE_INDEPENDENT (S : Set V3) (b : V3 → ℝ)
    (h1 : S ≠ ∅) (h2 : ¬affineDependent S) :
    ∃! p : V3, p ∈ (affineSpan ℝ S : Set V3) ∧
      ∀ x ∈ S, ∀ y ∈ S, p ⬝ᵥ (x - y) = b x - b y := by
  classical
  obtain ⟨s0, hs0⟩ := Set.nonempty_iff_ne_empty.mpr h1
  -- linear independence of the `z ↦ z - s0` family on `S \ {s0}` (local lemma)
  have hli := AFFINE_INDEPENDENT_IMP_INDEPENDENT S h2 s0 hs0
  set T0 : Set V3 := (fun z : V3 => z - s0) '' (S \ {s0}) with hT0def
  have hzinj : Function.Injective (fun z : V3 => z - s0) := fun z₁ z₂ hz => by
    have h2' := congrArg (fun z : V3 => z + s0) hz
    simpa using h2'
  -- transport to the image set `T0` via the bijection `z ↦ z - s0`
  have hT0li : LinearIndependent ℝ (fun w : T0 => (w : V3)) := by
    have hcoee : ((fun v : ↥((fun z : V3 => z - s0) '' (S \ {s0})) => (v : V3)) ∘
        Equiv.Set.image (fun z : V3 => z - s0) (S \ {s0}) hzinj) =
        (fun y : (S \ {s0} : Set V3) => ((y : V3) - s0)) := by
      funext y
      simp [Equiv.Set.image_apply]
    exact (linearIndependent_equiv'
      (Equiv.Set.image (fun z : V3 => z - s0) (S \ {s0}) hzinj) hcoee).mp hli
  -- `cb` prescribes the pairing values on `T0` (inner form throughout)
  set cb : V3 → ℝ := fun w => b (w + s0) - b s0 - inner ℝ s0 w with hcb
  obtain ⟨q, ⟨hqmem, hqpair⟩, hquniq⟩ := UNIQUE_SOLUTION_lemma T0 cb hT0li
  have hspanT0 : Submodule.span ℝ T0 = vectorSpan ℝ S := by
    rw [hT0def]
    have hv := vectorSpan_eq_span_vsub_set_right ℝ hs0
    rw [hv]
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro w ⟨x, hxS, rfl⟩
      obtain ⟨hxin, -⟩ := (Set.mem_sdiff x).mp hxS
      exact Submodule.subset_span ⟨x, hxin, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro w ⟨x, hxin, rfl⟩
      by_cases hxs : x = s0
      · subst hxs
        simp
      · exact Submodule.subset_span ⟨x, ⟨hxin, hxs⟩, by simp [vsub_eq_sub]⟩
  refine ⟨s0 + q, ⟨?_, ?_⟩, ?_⟩
  · -- membership: s0 + q ∈ affineSpan S
    have hs0in : s0 ∈ (affineSpan ℝ S : Set V3) :=
      SetLike.mem_coe.mpr (mem_affineSpan ℝ hs0)
    have hdir : (s0 + q -ᵥ s0 : V3) ∈ (affineSpan ℝ S).direction := by
      rw [direction_affineSpan, ← hspanT0]
      simpa [vsub_eq_sub, add_sub_cancel] using hqmem
    have hv := AffineSubspace.vadd_mem_of_mem_direction hdir hs0in
    rw [vadd_eq_add] at hv
    have hx2 : (s0 + q -ᵥ s0) + s0 = s0 + q := by rw [← vadd_eq_add, vsub_vadd]
    rwa [hx2] at hv
  · -- the full pairing property
    have hpairI : ∀ z ∈ S, inner ℝ (s0 + q) (z - s0) = b z - b s0 := by
      intro z hz
      by_cases hz0 : z = s0
      · subst hz0
        rw [sub_self, inner_zero_right]
        ring
      · have hzs : z ∈ S \ {s0} := ⟨hz, by simp [Set.mem_singleton_iff, hz0]⟩
        have hzT0 : (z - s0 : V3) ∈ T0 := by
          rw [hT0def]
          exact ⟨z, hzs, rfl⟩
        have hqp : inner ℝ q (z - s0) = cb (z - s0) := by
          rw [inner_eq_dot]
          exact hqpair (z - s0) hzT0
        have hqp2 : inner ℝ q (z - s0) = b z - b s0 - inner ℝ s0 (z - s0) := by
          rw [hqp]
          show b ((z - s0) + s0) - b s0 - inner ℝ s0 (z - s0)
              = b z - b s0 - inner ℝ s0 (z - s0)
          rw [sub_add_cancel]
        rw [inner_add_left, hqp2]
        linarith
    intro x hx y hy
    have keyI : inner ℝ (s0 + q) (x - y) = b x - b y := by
      rw [(show (x : V3) - y = (x - s0) - (y - s0) from by abel), inner_sub_right,
        hpairI x hx, hpairI y hy]
      ring
    exact (inner_eq_dot (s0 + q) (x - y)).symm.trans keyI
  · -- uniqueness
    rintro p' ⟨hp'mem, hp'pair⟩
    have hp'mem' : p' ∈ (affineSpan ℝ S : Set V3) := hp'mem
    have hq'mem : p' -ᵥ s0 ∈ Submodule.span ℝ T0 := by
      rw [hspanT0, ← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction
        (SetLike.mem_coe.mp hp'mem') (SetLike.mem_coe.mpr (mem_affineSpan ℝ hs0))
    have hq'cb : ∀ w ∈ T0, (p' -ᵥ s0) ⬝ᵥ w = cb w := by
      rintro w ⟨z, hzS, rfl⟩
      have hzin : z ∈ S := hzS.1
      have hkeyI : inner ℝ p' (z - s0) = b z - b s0 := by
        rw [inner_eq_dot]
        exact hp'pair z hzin s0 hs0
      have hmain : inner ℝ (p' -ᵥ s0) (z - s0)
          = b ((z - s0) + s0) - b s0 - inner ℝ s0 (z - s0) := by
        rw [vsub_eq_sub, inner_sub_left, hkeyI, sub_add_cancel]
      exact (inner_eq_dot (p' -ᵥ s0) (z - s0)).symm.trans hmain
    have hfin := hquniq (p' -ᵥ s0) ⟨hq'mem, hq'cb⟩
    rw [vsub_eq_sub, sub_eq_iff_eq_add] at hfin
    rw [hfin, add_comm]

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
  obtain ⟨y0, hy0⟩ := Set.nonempty_iff_ne_empty.mpr h1
  refine ⟨circumcenter S, ⟨OAPVION1_concl S h1 h2, ?_⟩, ?_⟩
  · intro x hx y hy
    rw [(OAPVION2_concl S h2 x hx).symm, OAPVION2_concl S h2 y hy]
  · rintro q ⟨hqm, hq⟩
    exact OAPVION3_concl S h2 q hqm ⟨dist q y0, fun w hw => (hq y0 hy0 w hw).symm⟩

/-- Rogers.hl:3816 `CIRCUMCENTER_LEMMA`. -/
theorem CIRCUMCENTER_LEMMA (S : Set V3) (h1 : S ≠ ∅) (h2 : ¬affineDependent S) :
    ∃! p : V3, p ∈ (affineSpan ℝ S : Set V3) ∧ ∃ c : ℝ, ∀ w ∈ S, c = dist p w := by
  refine ⟨circumcenter S, ⟨OAPVION1_concl S h1 h2,
    ⟨radV S, fun w hw => OAPVION2_concl S h2 w hw⟩⟩, ?_⟩
  rintro q ⟨hqm, c, hc⟩
  exact OAPVION3_concl S h2 q hqm ⟨c, fun w hw => (hc w hw).symm⟩

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

/-- The translate of an affinely independent set is affinely independent
(used for `CIRCUMCENTER_TRANSLATION` / `RADV_TRANSLATION`). -/
private theorem p6_not_affdep_image (s : Set V3) (a : V3) (h2 : ¬affineDependent s) :
    ¬affineDependent ((fun x : V3 => a + x) '' s) := by
  let hidx : ↥s ≃ (↥((fun x : V3 => a + x) '' s : Set V3)) :=
    { toFun := fun x => ⟨a + (x : V3), ⟨x, x.2, rfl⟩⟩
      invFun := fun y => ⟨(y : V3) - a, by
        obtain ⟨z, hz, heq⟩ := y.2
        rw [← heq]
        simpa using hz⟩
      left_inv := fun x => Subtype.ext (show a + (x : V3) - a = (x : V3) from by simp)
      right_inv := fun y =>
        Subtype.ext (show a + ((y : V3) - a) = (y : V3) from by simp) }
  have hcoe : (fun y : ↥((fun x : V3 => a + x) '' s : Set V3) => (y : V3)) ∘ hidx =
      (AffineEquiv.constVAdd ℝ V3 a) ∘ (fun x : ↥s => (x : V3)) := by
    rfl
  rw [affineDependent, not_not]
  have hA : AffineIndependent ℝ
      ((fun y : ↥((fun x : V3 => a + x) '' s : Set V3) => (y : V3)) ∘ hidx) := by
    rw [hcoe, AffineEquiv.affineIndependent_iff]
    exact not_not.mp h2
  exact (affineIndependent_equiv hidx).mp hA

/-- Rogers.hl:3972 `CIRCUMCENTER_TRANSLATION`. -/
theorem CIRCUMCENTER_TRANSLATION (s : Set V3) (a : V3) (h1 : s ≠ ∅)
    (h2 : ¬affineDependent s) :
    circumcenter ((fun x : V3 => a + x) '' s) = a + circumcenter s := by
  have hind' := p6_not_affdep_image s a h2
  have hmem : (a + circumcenter s) ∈
      ((affineSpan ℝ ((fun x : V3 => a + x) '' s : Set V3) : Set V3)) := by
    have h1' : (a + circumcenter s : V3) ∈
        AffineSubspace.map (AffineEquiv.constVAdd ℝ V3 a) (affineSpan ℝ s) := by
      rw [AffineSubspace.mem_map]
      exact ⟨circumcenter s, OAPVION1_concl s h1 h2, rfl⟩
    rwa [AffineSubspace.map_span] at h1'
  refine (OAPVION3_concl _ hind' _ hmem ⟨radV s, ?_⟩).symm
  rintro w ⟨z, hz, rfl⟩
  rw [dist_add_left, OAPVION2_concl s h2 z hz]

/-- Rogers.hl:4002 `RADV_TRANSLATION`. -/
theorem RADV_TRANSLATION (s : Set V3) (a : V3) (h : ¬affineDependent s) :
    radV ((fun x : V3 => a + x) '' s) = radV s := by
  rcases eq_or_ne s ∅ with hse | hse
  · rw [hse, Set.image_empty]
  · obtain ⟨z, hzs⟩ := Set.nonempty_iff_ne_empty.mpr hse
    have hind' := p6_not_affdep_image s a h
    have hTne : ((fun x : V3 => a + x) '' s) ≠ ∅ :=
      Set.nonempty_iff_ne_empty.mp (Set.image_nonempty.mpr ⟨z, hzs⟩)
    have hzT : (a + z) ∈ ((fun x : V3 => a + x) '' s) := ⟨z, hzs, rfl⟩
    rw [OAPVION2_concl _ hind' (a + z) hzT, CIRCUMCENTER_TRANSLATION s a hse h,
      OAPVION2_concl s h z hzs, dist_add_left]

/-- Rogers.hl:4046 `AFF_INTER_SUBSET_INTER_AFF`. -/
theorem AFF_INTER_SUBSET_INTER_AFF (s t : Set V3) :
    (affineSpan ℝ (s ∩ t) : Set V3) ⊆
      (affineSpan ℝ s : Set V3) ∩ (affineSpan ℝ t : Set V3) := by
  intro x hx
  exact ⟨SetLike.le_def.mp (affineSpan_mono ℝ Set.inter_subset_left) hx,
    SetLike.le_def.mp (affineSpan_mono ℝ Set.inter_subset_right) hx⟩

/-- Dot product as ℝ-linear map (inline copy of the private `dotRight`). -/
private def p6dot (a : V3) : V3 →ₗ[ℝ] ℝ where
  toFun x := a ⬝ᵥ x
  map_add' x y := by
    show a.ofLp ⬝ᵥ (x.ofLp + y.ofLp) = a.ofLp ⬝ᵥ x.ofLp + a.ofLp ⬝ᵥ y.ofLp
    exact dotProduct_add a.ofLp x.ofLp y.ofLp
  map_smul' r x := by
    show a.ofLp ⬝ᵥ (r • x.ofLp) = (RingHom.id ℝ) r • (a.ofLp ⬝ᵥ x.ofLp)
    rw [dotProduct_smul]
    simp

private theorem p6dot_apply (a x : V3) : p6dot a x = a ⬝ᵥ x := rfl

private theorem p6_dot_sub_r (a x y : V3) : (x - y) ⬝ᵥ a = x ⬝ᵥ a - y ⬝ᵥ a :=
  sub_dotProduct x.ofLp y.ofLp a.ofLp

private theorem p6_dot_sub_l (a x y : V3) : a ⬝ᵥ (x - y) = a ⬝ᵥ x - a ⬝ᵥ y :=
  dotProduct_sub a.ofLp x.ofLp y.ofLp

private theorem p6_dot_sub_l_vsub (a x y : V3) : a ⬝ᵥ (x -ᵥ y) = a ⬝ᵥ x - a ⬝ᵥ y :=
  p6_dot_sub_l a x y

private theorem p6_dot_add_l (a x y : V3) : a ⬝ᵥ (x + y) = a ⬝ᵥ x + a ⬝ᵥ y :=
  dotProduct_add a.ofLp x.ofLp y.ofLp

private theorem p6_dot_smul_l (a x : V3) (r : ℝ) : a ⬝ᵥ (r • x) = r * (a ⬝ᵥ x) := by
  show a.ofLp ⬝ᵥ (r • x.ofLp) = r * (a.ofLp ⬝ᵥ x.ofLp)
  rw [dotProduct_smul]; simp

private theorem p6_dot_smul_r (a x : V3) (r : ℝ) : (r • a) ⬝ᵥ x = r * (a ⬝ᵥ x) := by
  show (r • a).ofLp ⬝ᵥ x.ofLp = r * (a.ofLp ⬝ᵥ x.ofLp)
  rw [WithLp.ofLp_smul, dotProduct_comm, dotProduct_smul, dotProduct_comm]; simp

private theorem p6_dot_comm (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a :=
  dotProduct_comm a.ofLp b.ofLp

/-- Squared-distance expansion. -/
private theorem p6_dot_expand (x z : V3) :
    (x - z) ⬝ᵥ (x - z) = x ⬝ᵥ x - 2 * (x ⬝ᵥ z) + z ⬝ᵥ z := by
  have h1 : (x - z) ⬝ᵥ (x - z) = (x - z) ⬝ᵥ x - (x - z) ⬝ᵥ z :=
    dotProduct_sub (x - z).ofLp x.ofLp z.ofLp
  have h2 : (x - z) ⬝ᵥ x = x ⬝ᵥ x - z ⬝ᵥ x :=
    sub_dotProduct x.ofLp z.ofLp x.ofLp
  have h3 : (x - z) ⬝ᵥ z = x ⬝ᵥ z - z ⬝ᵥ z :=
    sub_dotProduct x.ofLp z.ofLp z.ofLp
  calc (x - z) ⬝ᵥ (x - z) = (x - z) ⬝ᵥ x - (x - z) ⬝ᵥ z := h1
    _ = (x ⬝ᵥ x - z ⬝ᵥ x) - (x ⬝ᵥ z - z ⬝ᵥ z) := by rw [h2, h3]
    _ = x ⬝ᵥ x - 2 * (x ⬝ᵥ z) + z ⬝ᵥ z := by rw [dotProduct_comm z x]; ring

/-- `bis u v` in hyperplane form (HOL `BIS_EQ_HYPERPLANE`). -/
private theorem p6_bis_dot (p q x : V3) :
    x ∈ bis p q ↔ 2 * ((q - p) ⬝ᵥ x) = q ⬝ᵥ q - p ⬝ᵥ p := by
  have hsq : dist x p ^ 2 = x ⬝ᵥ x - 2 * (x ⬝ᵥ p) + p ⬝ᵥ p := by
    show ‖x - p‖ ^ 2 = x ⬝ᵥ x - 2 * (x ⬝ᵥ p) + p ⬝ᵥ p
    rw [norm_sq_eq_dot]
    exact p6_dot_expand x p
  have hsq2 : dist x q ^ 2 = x ⬝ᵥ x - 2 * (x ⬝ᵥ q) + q ⬝ᵥ q := by
    show ‖x - q‖ ^ 2 = x ⬝ᵥ x - 2 * (x ⬝ᵥ q) + q ⬝ᵥ q
    rw [norm_sq_eq_dot]
    exact p6_dot_expand x q
  have hsub : 2 * ((q - p) ⬝ᵥ x) = 2 * (x ⬝ᵥ q) - 2 * (x ⬝ᵥ p) := by
    rw [p6_dot_sub_r, dotProduct_comm q x, dotProduct_comm p x]
    ring
  constructor
  · intro h
    have hd : dist x p = dist x q := h
    have h2 : dist x p ^ 2 = dist x q ^ 2 := by rw [hd]
    rw [hsq, hsq2] at h2
    rw [hsub]
    linarith
  · intro h
    show dist x p = dist x q
    refine (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ?_
    rw [hsq, hsq2]
    rw [hsub] at h
    linarith

/-- `bis u v` is affine (HOL `BIS_EQ_HYPERPLANE` + `AFFINE_HYPERPLANE`). -/
private theorem p6_bis_affspan (p q : V3) :
    (affineSpan ℝ (bis p q) : Set V3) = bis p q := by
  by_cases hpq : p = q
  · subst hpq
    have hb : bis p p = Set.univ := by
      ext x
      simp [bis]
    rw [hb, AffineSubspace.span_univ]
    rfl
  · have hcne : (2 : ℝ) • (q - p) ≠ 0 := by
      intro h0
      rcases smul_eq_zero.mp h0 with h2 | hqp
      · norm_num at h2
      · exact hpq (sub_eq_zero.mp hqp).symm
    have hcc : ((2 : ℝ) • (q - p)) ⬝ᵥ ((2 : ℝ) • (q - p)) ≠ 0 := by
      intro h
      have hz := dotProduct_self_eq_zero.1 h
      rw [WithLp.ofLp_eq_zero] at hz
      exact hcne hz
    have hcxdot : ∀ x : V3, ((2 : ℝ) • (q - p)) ⬝ᵥ x = 2 * ((q - p) ⬝ᵥ x) :=
      fun x => p6_dot_smul_r (q - p) x 2
    set c : V3 := (2 : ℝ) • (q - p) with hcdef
    set x0 : V3 := ((q ⬝ᵥ q - p ⬝ᵥ p) / (c ⬝ᵥ c)) • c with hx0def
    have hx0 : c ⬝ᵥ x0 = q ⬝ᵥ q - p ⬝ᵥ p := by
      have h1 : c ⬝ᵥ x0 = ((q ⬝ᵥ q - p ⬝ᵥ p) / (c ⬝ᵥ c)) * (c ⬝ᵥ c) :=
        p6_dot_smul_l c c ((q ⬝ᵥ q - p ⬝ᵥ p) / (c ⬝ᵥ c))
      rw [h1]
      exact div_mul_cancel₀ _ hcc
    have hmem : ∀ x : V3, x ∈ bis p q ↔
        x -ᵥ x0 ∈ LinearMap.ker (p6dot c) := by
      intro x
      rw [p6_bis_dot, LinearMap.mem_ker, p6dot_apply]
      constructor
      · intro h
        rw [p6_dot_sub_l_vsub, hx0, sub_eq_zero, hcxdot x]
        exact h
      · intro h
        rw [p6_dot_sub_l_vsub] at h
        rw [hx0] at h
        rw [sub_eq_zero] at h
        rw [hcxdot x] at h
        exact h
    have hW : bis p q = ↑(AffineSubspace.mk' x0 (LinearMap.ker (p6dot c))) := by
      ext x
      rw [hmem x, SetLike.mem_coe, AffineSubspace.mem_mk']
    rw [hW, AffineSubspace.affineSpan_coe]

/-- `affDim` of an affine hull (HOL `AFF_DIM_AFFINE_HULL`). -/
private theorem p6_affDim_affineSpan (s : Set V3) :
    affDim ((affineSpan ℝ s : Set V3)) = affDim s := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs, affDim_empty, AffineSubspace.span_empty, AffineSubspace.bot_coe, affDim_empty]
  · have hne : s ≠ ∅ := Set.nonempty_iff_ne_empty.mp hs
    have hne2 : (affineSpan ℝ s : Set V3) ≠ ∅ := by
      intro h0
      exact hne (Set.subset_empty_iff.1 (h0 ▸ subset_affineSpan ℝ s))
    simp only [affDim, if_neg hne, if_neg hne2]
    rw [← AffineSubspace.direction_eq_vectorSpan (affineSpan ℝ s), direction_affineSpan]

/-- Equal affine dimension inside an affine set forces equal affine hulls
(HOL `AFF_DIM_EQ_AFFINE_HULL`). -/
private theorem p6_affspan_eq_of_dim (s t : Set V3) (hs : s.Nonempty) (hsub : s ⊆ t)
    (ht : (affineSpan ℝ t : Set V3) = t) (hd : affDim s = affDim t) :
    (affineSpan ℝ s : Set V3) = t := by
  have hle : affineSpan ℝ s ≤ affineSpan ℝ t := by
    refine affineSpan_le.2 ?_
    intro x hx
    have hxt : x ∈ t := hsub hx
    rw [← ht] at hxt
    exact hxt
  have hdirs : (affineSpan ℝ s).direction = (affineSpan ℝ t).direction := by
    rw [direction_affineSpan, direction_affineSpan]
    have hmono : vectorSpan ℝ s ≤ vectorSpan ℝ t := vectorSpan_mono (k := ℝ) hsub
    have hfr : Module.finrank ℝ (vectorSpan ℝ t) ≤ Module.finrank ℝ (vectorSpan ℝ s) := by
      have h1 := hd
      simp only [affDim, if_neg (Set.nonempty_iff_ne_empty.mp hs),
        if_neg (Set.nonempty_iff_ne_empty.mp (hs.mono hsub))] at h1
      exact (Nat.cast_injective h1).ge
    exact Submodule.eq_of_le_of_finrank_le hmono hfr
  have hnon : (affineSpan ℝ s : Set V3).Nonempty := by
    rcases hs with ⟨p0, hp0⟩
    exact ⟨p0, subset_affineSpan ℝ s hp0⟩
  have hEq : affineSpan ℝ s = affineSpan ℝ t :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirs hnon hle
  rw [hEq]
  exact ht

/-- Codimension-one slice: an affine set cut by a hyperplane it does not
fill, along a nonempty piece, loses one dimension (HOL
`AFF_DIM_AFFINE_INTER_HYPERPLANE` special case). Here the hyperplane is
given as `H` with an explicit nontrivial functional. -/
private theorem p6_affDim_inter_hyper (A H : Set V3) (c : V3) (d : ℝ)
    (hHmem : ∀ x : V3, x ∈ H ↔ c ⬝ᵥ x = d)
    (hcne : c ≠ 0)
    (hA : (affineSpan ℝ A : Set V3) = A) (hIntNe : (A ∩ H).Nonempty)
    (hnot : ¬ A ⊆ H) :
    affDim (A ∩ H) = affDim A - 1 := by
  classical
  have hIntNe' := hIntNe
  have hH : ∀ x : V3, x ∈ H ↔ c ⬝ᵥ x = (d : ℝ) := hHmem
  obtain ⟨p0, hp0A, hp0H⟩ := hIntNe
  have hp0H' : c ⬝ᵥ p0 = d := (hH p0).1 hp0H
  obtain ⟨z, hzA, hzH⟩ := Set.not_subset.mp hnot
  have hz' : c ⬝ᵥ z ≠ d := fun h => hzH ((hH z).2 h)
  have hfune : ∃ u ∈ vectorSpan ℝ A, c ⬝ᵥ u ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hthis : c ⬝ᵥ (z - p0) = 0 := hall _ (by
      rw [vectorSpan_def]
      exact Submodule.subset_span (Set.mem_vsub.2 ⟨z, hzA, p0, hp0A, rfl⟩))
    have hsub0 : c ⬝ᵥ z - c ⬝ᵥ p0 = 0 := Eq.trans (p6_dot_sub_l c z p0).symm hthis
    have hz2 : c ⬝ᵥ z = c ⬝ᵥ p0 := by linarith
    rw [hz2] at hz'
    exact hz' hp0H'
  obtain ⟨u, huD, hu0⟩ := hfune
  set K : Submodule ℝ V3 := vectorSpan ℝ (A ∩ H) with hKdef
  have hKkerle : vectorSpan ℝ (A ∩ H) ≤ LinearMap.ker (p6dot c) := by
    rw [vectorSpan_def, Submodule.span_le]
    intro g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.1 hg
    rw [SetLike.mem_coe, LinearMap.mem_ker, p6dot_apply]
    exact Eq.trans (p6_dot_sub_l_vsub c x y)
      (by rw [(hH x).1 hx.2, (hH y).1 hy.2, sub_self])
  have hKle : K ≤ vectorSpan ℝ A := vectorSpan_mono (k := ℝ) Set.inter_subset_left
  have hkerD : ∀ w ∈ vectorSpan ℝ A, c ⬝ᵥ w = 0 → w ∈ K := by
    intro w hwD hw0
    have hp0aff : p0 ∈ (affineSpan ℝ A : Set V3) := subset_affineSpan ℝ A hp0A
    have hwdir : w ∈ (affineSpan ℝ A).direction := by
      rw [direction_affineSpan]; exact hwD
    have hmemA : w +ᵥ p0 ∈ (affineSpan ℝ A : Set V3) :=
      AffineSubspace.vadd_mem_of_mem_direction hwdir hp0aff
    have hmemH : c ⬝ᵥ (w +ᵥ p0) = d := by
      have h1 : (w +ᵥ p0 : V3) = p0 + w := by rw [vadd_eq_add, add_comm]
      have h2 : c ⬝ᵥ (w +ᵥ p0) = c ⬝ᵥ p0 + c ⬝ᵥ w := by rw [h1]; exact p6_dot_add_l c p0 w
      rw [h2, hp0H', hw0, add_zero]
    have hmem : w +ᵥ p0 ∈ A ∩ H :=
      ⟨hA ▸ hmemA, (hH _).2 hmemH⟩
    have hp0mem : p0 ∈ A ∩ H := ⟨hp0A, hp0H⟩
    rw [hKdef, vectorSpan_def]
    refine Submodule.subset_span (Set.mem_vsub.2 ⟨w +ᵥ p0, hmem, p0, hp0mem, ?_⟩)
    have hvsub : ((w +ᵥ p0 : V3) -ᵥ p0) = w := by simp
    exact hvsub
  have hsup : vectorSpan ℝ A = K ⊔ Submodule.span ℝ {u} := by
    have h1 : K ⊔ Submodule.span ℝ {u} ≤ vectorSpan ℝ A := by
      intro w hw
      rcases Submodule.mem_sup.1 hw with ⟨a, ha, b, hb, hab⟩
      have haD : a ∈ vectorSpan ℝ A := hKle ha
      have hbD : b ∈ vectorSpan ℝ A := by
        have hsb : Submodule.span ℝ {u} ≤ vectorSpan ℝ A := Submodule.span_le.2
          (Set.singleton_subset_iff.2 huD)
        exact hsb hb
      rw [← hab]
      exact add_mem haD hbD
    have h2 : vectorSpan ℝ A ≤ K ⊔ Submodule.span ℝ {u} := by
      intro w hwD
      by_cases hw0 : c ⬝ᵥ w = 0
      · exact Submodule.mem_sup.2 ⟨w, hkerD w hwD hw0, 0, Submodule.zero_mem _, by rw [add_zero]⟩
      · have hsm : (c ⬝ᵥ w / c ⬝ᵥ u) • u ∈ vectorSpan ℝ A := Submodule.smul_mem _ _ huD
        have hwm : w - (c ⬝ᵥ w / c ⬝ᵥ u) • u ∈ vectorSpan ℝ A :=
          add_mem hwD (neg_mem hsm)
        refine Submodule.mem_sup.2 ⟨w - (c ⬝ᵥ w / c ⬝ᵥ u) • u, hkerD _ hwm ?_,
          (c ⬝ᵥ w / c ⬝ᵥ u) • u, Submodule.mem_span_singleton.2 ⟨_, rfl⟩, by
            rw [sub_add_cancel]⟩
        · calc c ⬝ᵥ (w - (c ⬝ᵥ w / c ⬝ᵥ u) • u)
              = c ⬝ᵥ w - c ⬝ᵥ ((c ⬝ᵥ w / c ⬝ᵥ u) • u) := p6_dot_sub_l c w _
            _ = c ⬝ᵥ w - (c ⬝ᵥ w / c ⬝ᵥ u) * (c ⬝ᵥ u) := by rw [p6_dot_smul_l]
            _ = 0 := by
                rw [div_mul_cancel₀ _ hu0]
                ring
    exact le_antisymm h2 h1
  have hinf : K ⊓ Submodule.span ℝ {u} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwK : w ∈ K := (Submodule.mem_inf.1 hw).1
    have hwS := (Submodule.mem_inf.1 hw).2
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hwS
    have h1 : c ⬝ᵥ (s • u) = 0 := by
      have hk := hKkerle hwK
      rw [LinearMap.mem_ker, p6dot_apply] at hk
      exact hk
    rw [p6_dot_smul_l] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · rw [h]; simp
    · exact absurd h hu0
  have hune : u ≠ 0 := by
    intro h
    apply hu0
    rw [h]
    simp
  have hfr : Module.finrank ℝ K + 1 = Module.finrank ℝ (vectorSpan ℝ A) := by
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq K (Submodule.span ℝ {u})
    rw [hinf, finrank_bot] at h2
    have h3 : Module.finrank ℝ (Submodule.span ℝ {u}) = 1 := finrank_span_singleton hune
    rw [h3] at h2
    rw [hsup]
    omega
  rcases hIntNe' with ⟨q0, hq0⟩
  have hne' : A ∩ H ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨q0, hq0⟩
  have hneA' : A ≠ ∅ := fun h0 => hne' (by rw [h0]; simp)
  simp only [affDim, if_neg hne', if_neg hneA']
  rw [<- hKdef]
  have hfr'' : (Module.finrank ℝ K : ℤ) + 1
      = (Module.finrank ℝ (vectorSpan ℝ A) : ℤ) := by
    exact_mod_cast hfr
  linarith

/-- The affine hull of an affine set cut by the coe of an affine
subspace is that intersection. -/
private theorem p6_affspan_inter_coe (s : Set V3) (W : AffineSubspace ℝ V3)
    (hs : (affineSpan ℝ s : Set V3) = s) :
    (affineSpan ℝ (s ∩ (↑W : Set V3)) : Set V3) = s ∩ (↑W : Set V3) := by
  refine le_antisymm ?_ (subset_affineSpan ℝ _)
  intro x hx
  refine ⟨?_, ?_⟩
  · have h1 : (affineSpan ℝ (s ∩ (↑W : Set V3)) : AffineSubspace ℝ V3)
        ≤ affineSpan ℝ s := affineSpan_mono ℝ Set.inter_subset_left
    have hx1 : x ∈ (affineSpan ℝ s : Set V3) := (AffineSubspace.le_def _ _).mp h1 hx
    rw [hs] at hx1
    exact hx1
  · have h2 : (affineSpan ℝ (s ∩ (↑W : Set V3)) : AffineSubspace ℝ V3) ≤ W := by
      refine le_trans (affineSpan_mono ℝ Set.inter_subset_right) ?_
      exact (AffineSubspace.affineSpan_coe W).le
    exact (AffineSubspace.le_def _ _).mp h2 hx

/-- The hyperplane-intersection fact for a bisector (bridges `p6_bis_dot`
to `p6_affDim_inter_hyper`). -/
private theorem p6_affDim_inter_bis (A : Set V3) (p q : V3)
    (hA : (affineSpan ℝ A : Set V3) = A) (hIntNe : (A ∩ bis p q).Nonempty)
    (hnot : ¬ A ⊆ bis p q) :
    affDim (A ∩ bis p q) = affDim A - 1 := by
  have hcxdot : ∀ x : V3, ((2 : ℝ) • (q - p)) ⬝ᵥ x = 2 * ((q - p) ⬝ᵥ x) :=
    fun x => p6_dot_smul_r (q - p) x 2
  refine p6_affDim_inter_hyper A (bis p q) ((2 : ℝ) • (q - p))
    (q ⬝ᵥ q - p ⬝ᵥ p) (fun x => ?_) ?_ hA hIntNe hnot
  · rw [p6_bis_dot, hcxdot x]
  · intro h0
    apply hnot
    rw [(smul_eq_zero.mp h0).elim (fun h2 => absurd h2 (by norm_num))
      (fun hqp => sub_eq_zero.mp hqp)]
    intro x _
    exact rfl

/-- Rogers.hl:4053 `MHFTTZN_lemma`. -/
theorem MHFTTZN_lemma (V : Set V3) (ul : List V3) (k : ℕ) (hP : Packing V)
    (hbar : barV V k ul) :
    (affineSpan ℝ (voronoiList V ul) : Set V3) =
      ⋂₀ {bis (hdV ul) u | u ∈ setOfList ul} := by

  revert ul
  induction k with
  | zero =>
    intro ul hbar
    have h1 := hbar.1
    have hVh : hdV ul ∈ V := BARV_SUBSET V 0 ul hbar (HD_IN_SET_OF_LIST ul (by omega))
    have hball : Metric.ball (hdV [hdV ul]) 1 ⊆ voronoiClosed V (hdV [hdV ul]) := by
      intro x hx w hw
      rcases eq_or_ne w (hdV [hdV ul]) with rfl | hne
      · exact le_refl _
      · have hge : 2 ≤ dist w (hdV [hdV ul]) := by
          by_contra hc
          exact hne ((packing_lt V).mp hP w (hdV [hdV ul]) hw hVh (not_le.1 hc))
        have hlt : dist x (hdV [hdV ul]) < 1 := Metric.mem_ball.1 hx
        have htri : dist w (hdV [hdV ul]) ≤ dist w x + dist x (hdV [hdV ul]) :=
          dist_triangle w x (hdV [hdV ul])
        have hcomm : dist w x = dist x w := dist_comm w x
        linarith
    have hLHS : (affineSpan ℝ (voronoiList V [hdV ul]) : Set V3) = Set.univ := by
      have htop := CONTAINS_BALL_AFFINE_HULL (voronoiClosed V (hdV ul)) (hdV ul) 1 one_pos hball
      rw [VORONOI_LIST_SING, htop, AffineSubspace.top_coe]
    have hRHS : (⋂₀ {bis (hdV [hdV ul]) u | u ∈ setOfList [hdV ul]} : Set V3) = Set.univ := by
      have hset : setOfList [hdV ul] = ({hdV ul} : Set V3) := by simp [setOfList]
      rw [hset]
      have himg : {bis (hdV [hdV ul]) u | u ∈ ({hdV ul} : Set V3)}
          = {bis (hdV [hdV ul]) (hdV ul)} := by
        ext T
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨u, rfl, rfl⟩
          rfl
        · intro h
          exact ⟨hdV ul, rfl, h.symm⟩
      rw [himg, Set.sInter_singleton]
      ext x
      simp [bis, hdV]
    rw [LENGTH_1_LEMMA ul h1, hLHS, hRHS]
  | succ k ih =>
    intro ul hbar
    have hkle : k + 1 ≤ 3 := BARV_IMP_K_LE_3 V ul (k + 1) hbar
    have hlen : ul.length = k + 1 + 1 := hbar.1
    have h2le : 2 ≤ ul.length := by omega
    have htr : truncateSimplex k ul = ul.dropLast := by
      have h := TRUNCATE_SIMPLEX_EQ_BUTLAST ul h2le
      rwa [show ul.length - 2 = k from by omega] at h
    have hbarv : barV V k (truncateSimplex k ul) :=
      TRUNCATE_SIMPLEX_BARV V k (k + 1) ul hbar (by omega)
    have hbarvl : barV V k ul.dropLast := htr ▸ hbarv
    have hhdv : hdV ul.dropLast = hdV ul := by
      rw [← htr]
      exact HD_TRUNCATE_SIMPLEX ul k (by omega)
    have ihvl := ih ul.dropLast hbarvl
    rw [hhdv] at ihvl
    have hlt : ul.length - 1 < ul.length := by omega
    have hlast : elV ul (ul.length - 1) ∈ setOfList ul := by
      have h1 : elV ul (ul.length - 1) = ul[ul.length - 1] :=
        List.getD_eq_getElem (l := ul) (0:V3) hlt
      have h2 : ul[ul.length - 1] ∈ ul := List.getElem_mem hlt
      rw [h1]
      exact h2
    have hlastV : elV ul (ul.length - 1) ∈ V := BARV_SUBSET V (k + 1) ul hbar hlast
    have happend : ul = ul.dropLast ++ [elV ul (ul.length - 1)] := by
      have hLE := LIST_EQ_TRUNCATE_SIMPLEX_APPEND_LAST ul h2le
      rw [show ul.length - 2 = k from by omega, htr] at hLE
      exact hLE
    have hdl1 : 1 ≤ ul.dropLast.length := by
      have hbl := LENGTH_BUTLAST ul (by omega)
      omega
    obtain ⟨h0, tl0, hcons0⟩ := LENGTH_IMP_CONS ul.dropLast hdl1
    have hh0 : h0 = hdV ul.dropLast := by rw [hcons0]; simp [hdV]
    have hB1 := VORONOI_LIST_INTER_BIS V ul.dropLast (elV ul (ul.length - 1)) h0 tl0
      (BARV_SUBSET V k ul.dropLast hbarvl) hlastV hcons0
    rw [hh0, hhdv] at hB1
    have hB1' : voronoiList V ul.dropLast ∩ bis (hdV ul) (elV ul (ul.length - 1))
        = voronoiList V ul := by
      rw [hB1]
      conv_rhs => rw [happend]
    have hsetsplit : setOfList ul
        = insert (elV ul (ul.length - 1)) (setOfList ul.dropLast) := by
      conv_lhs => rw [happend]
      ext x
      simp only [setOfList, Set.mem_setOf_eq, List.mem_append, List.mem_singleton,
        Set.mem_insert_iff]
      tauto
    have himg : {bis (hdV ul) u | u ∈ insert (elV ul (ul.length - 1)) (setOfList ul.dropLast)}
        = insert (bis (hdV ul) (elV ul (ul.length - 1)))
            {bis (hdV ul) u | u ∈ setOfList ul.dropLast} := by
      ext T
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
      constructor
      · rintro ⟨u, (rfl | hu), rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨u, hu, rfl⟩
      · rintro (rfl | ⟨u, hu, rfl⟩)
        · exact ⟨elV ul (ul.length - 1), Or.inl rfl, rfl⟩
        · exact ⟨u, Or.inr hu, rfl⟩
    set A0 := (affineSpan ℝ (voronoiList V ul.dropLast) : Set V3) with hA0def
    rw [← hB1', hsetsplit, himg, Set.sInter_insert]
    by_cases hcase : A0 ⊆ bis (hdV ul) (elV ul (ul.length - 1))
    · have hveq : voronoiList V ul.dropLast ∩ bis (hdV ul) (elV ul (ul.length - 1))
          = voronoiList V ul.dropLast :=
        Set.inter_eq_self_of_subset_left (fun x hx => hcase (subset_affineSpan ℝ _ hx))
      have hsub2 : ⋂₀ {bis (hdV ul) u | u ∈ setOfList ul.dropLast}
          ⊆ bis (hdV ul) (elV ul (ul.length - 1)) := by
        intro x hx
        refine hcase ?_
        rw [ihvl]
        exact hx
      rw [hveq, ← hA0def, ihvl, Set.inter_comm, Set.inter_eq_self_of_subset_left hsub2]
    · have hsubA1 : voronoiList V ul.dropLast ∩ bis (hdV ul) (elV ul (ul.length - 1))
          ⊆ A0 ∩ bis (hdV ul) (elV ul (ul.length - 1)) :=
        Set.inter_subset_inter (fun x hx => subset_affineSpan ℝ _ hx) Subset.rfl
      have hvne : (voronoiList V ul).Nonempty := by
        by_contra h0
        have h0' : voronoiList V ul = ∅ := Set.not_nonempty_iff_eq_empty.mp h0
        have hdim := AFF_DIM_VORONOI_LIST V ul (k + 1) hbar
        rw [h0', affDim_empty] at hdim
        omega
      have hvne2 : (voronoiList V ul.dropLast
          ∩ bis (hdV ul) (elV ul (ul.length - 1))).Nonempty := by
        rw [← hB1'] at hvne
        exact hvne
      have hIntNe : (A0 ∩ bis (hdV ul) (elV ul (ul.length - 1))).Nonempty :=
        ⟨hvne2.choose, hsubA1 hvne2.choose_spec⟩
      have hAaff : (affineSpan ℝ A0 : Set V3) = A0 := by
        rw [hA0def, AffineSubspace.affineSpan_coe]
      have hdimA0 : affDim A0 = 3 - k := by
        rw [hA0def, p6_affDim_affineSpan]
        exact AFF_DIM_VORONOI_LIST V ul.dropLast k hbarvl
      have hdimA1 : affDim (A0 ∩ bis (hdV ul) (elV ul (ul.length - 1)))
          = affDim (voronoiList V ul) := by
        rw [p6_affDim_inter_bis A0 (hdV ul) (elV ul (ul.length - 1)) hAaff hIntNe hcase,
          hdimA0, AFF_DIM_VORONOI_LIST V ul (k + 1) hbar]
        omega
      refine (p6_affspan_eq_of_dim
        (voronoiList V ul.dropLast ∩ bis (hdV ul) (elV ul (ul.length - 1)))
        (A0 ∩ bis (hdV ul) (elV ul (ul.length - 1))) hvne2 hsubA1 ?_ ?_).trans ?_
      · rw [← p6_bis_affspan]
        exact p6_affspan_inter_coe A0
          (affineSpan ℝ (bis (hdV ul) (elV ul (ul.length - 1)))) hAaff
      · rw [hB1', AFF_DIM_VORONOI_LIST V ul (k + 1) hbar,
          p6_affDim_inter_bis A0 (hdV ul) (elV ul (ul.length - 1)) hAaff hIntNe hcase, hdimA0]
        omega
      · rw [ihvl, Set.inter_comm]


/-- HOL `AFF_DIM_LE_CARD` content (Mathlib side): for a nonempty finite set,
`affDim S + 1 ≤ Nat.card S`. -/
private theorem p6_affDim_le_card (S : Set V3) (hfin : S.Finite) (hne : S.Nonempty) :
    affDim S + 1 ≤ (Nat.card S : ℤ) := by
  haveI : Fintype ↥S := hfin.fintype
  haveI : Nonempty ↥S := ⟨hne.choose, hne.choose_spec⟩
  have hne' : S ≠ ∅ := Set.nonempty_iff_ne_empty.mp hne
  have hrange : Set.range (fun x : ↥S => (x : V3)) = S := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact x.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  have h1 := finrank_vectorSpan_range_add_one_le (k := ℝ) (V := V3) (P := V3)
    (fun x : ↥S => (x : V3))
  rw [hrange] at h1
  have hdim : affDim S = (Module.finrank ℝ (vectorSpan ℝ S) : ℤ) := if_neg hne'
  rw [hdim]
  have h3 : (Nat.card S : ℤ) = ((Fintype.card ↥S : ℕ) : ℤ) := by
    rw [Nat.card_eq_fintype_card]
  omega

/-- HOL `AFFINE_INDEPENDENT_IFF_CARD` direction (Rogers.hl:4934 usage inside
`MHFTTZN3`): a finite set with `Nat.card S ≤ affDim S + 1` is affinely
independent. This is the `BARV_AFFINE_INDEPENDENT` unlock key for PA18 (via
`MHFTTZN1` + `BARV_IMP_LENGTH_EQ_CARD`). -/
theorem p6_affdep_of_dim (S : Set V3) (hfin : S.Finite)
    (h : (Nat.card S : ℤ) ≤ affDim S + 1) : ¬affineDependent S := by
  rw [affineDependent, not_not]
  rcases S.eq_empty_or_nonempty with hE | hne
  · have hsub : Subsingleton ↥S := by
      rw [hE]
      exact ⟨fun a b => absurd a.2 (Set.notMem_empty _)⟩
    exact affineIndependent_of_subsingleton ℝ _
  · haveI : Fintype ↥S := hfin.fintype
    haveI : Nonempty ↥S := ⟨hne.choose, hne.choose_spec⟩
    have hcardpos : 0 < Nat.card S := Nat.card_pos
    have hdim : affDim S = (Module.finrank ℝ (vectorSpan ℝ S) : ℤ) :=
      if_neg (Set.nonempty_iff_ne_empty.mp hne)
    have hle : Nat.card S - 1 ≤ Module.finrank ℝ (vectorSpan ℝ S) := by
      rw [hdim] at h
      omega
    have hrange : Set.range (fun x : ↥S => (x : V3)) = S := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩; exact x.2
      · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
    have hpos : 0 < Fintype.card ↥S := Fintype.card_pos
    rw [affineIndependent_iff_le_finrank_vectorSpan ℝ (fun x : ↥S => (x : V3))
      (show Fintype.card ↥S = Nat.card S - 1 + 1 by
        rw [Nat.card_eq_fintype_card]; omega), hrange]
    exact hle

/-- Inserting a point outside the affine span raises the affine dimension
by one (HOL `AFF_DIM_INSERT` content). -/
private theorem p6_affDim_insert (S : Set V3) (y : V3) (hne : S.Nonempty)
    (hy : y ∉ (affineSpan ℝ S : Set V3)) :
    affDim (insert y S) = affDim S + 1 := by
  obtain ⟨y0, hy0⟩ := hne
  have hy0S : y0 ∈ (affineSpan ℝ S : Set V3) := subset_affineSpan ℝ S hy0
  set D := vectorSpan ℝ S with hD
  have mD : ∀ a ∈ S, ∀ b ∈ S, (a - b) ∈ D := by
    intro a ha b hb
    rw [hD, vectorSpan_def]
    exact Submodule.subset_span (Set.mem_vsub.2 ⟨a, ha, b, hb, rfl⟩)
  have hvec : vectorSpan ℝ (insert y S) = D ⊔ Submodule.span ℝ {y - y0} := by
    have hgen : (y - y0) ∈ vectorSpan ℝ (insert y S) := by
      rw [vectorSpan_def]
      exact Submodule.subset_span (Set.mem_vsub.2 ⟨y, Set.mem_insert _ _,
        y0, Set.mem_insert_of_mem _ hy0, rfl⟩)
    have hmono : vectorSpan ℝ S ≤ vectorSpan ℝ (insert y S) :=
      vectorSpan_mono (k := ℝ) (Set.subset_insert y S)
    have hsb : ∀ r ∈ Submodule.span ℝ {y - y0}, r ∈ vectorSpan ℝ (insert y S) := by
      intro r hm
      rw [Submodule.mem_span_singleton] at hm
      obtain ⟨s, rfl⟩ := hm
      exact Submodule.smul_mem _ s hgen
    refine le_antisymm ?_ ?_
    · rw [vectorSpan_def, Submodule.span_le]
      intro g hg
      obtain ⟨x, hx, x', hx', rfl⟩ := Set.mem_vsub.1 hg
      rw [SetLike.mem_coe]
      rcases Set.mem_insert_iff.1 hx with hxe | hx
      · rcases Set.mem_insert_iff.1 hx' with hxe' | hx'
        · rw [hxe, hxe', vsub_self]
          exact Submodule.zero_mem _
        · rw [hxe, vsub_eq_sub]
          have hv : (y - x' : V3) = (y - y0) + -(x' - y0) := by abel
          have hA : (x' - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_left (mD x' hx' y0 hy0)
          have hC : (y - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_right (Submodule.subset_span
              (Set.mem_singleton (y - y0)))
          rw [hv]
          exact Submodule.add_mem (D ⊔ Submodule.span ℝ {y - y0}) hC
            (Submodule.neg_mem (D ⊔ Submodule.span ℝ {y - y0}) hA)
      · rcases Set.mem_insert_iff.1 hx' with hxe' | hx'
        · rw [hxe', vsub_eq_sub]
          have hv : (x - y : V3) = (x - y0) + -(y - y0) := by abel
          have hA : (x - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_left (mD x hx y0 hy0)
          have hC : (y - y0 : V3) ∈ D ⊔ Submodule.span ℝ {y - y0} :=
            Submodule.mem_sup_right (Submodule.subset_span
              (Set.mem_singleton (y - y0)))
          rw [hv]
          exact Submodule.add_mem (D ⊔ Submodule.span ℝ {y - y0}) hA
            (Submodule.neg_mem (D ⊔ Submodule.span ℝ {y - y0}) hC)
        · exact Submodule.mem_sup_left (mD x hx x' hx')
    · intro w hw
      rcases Submodule.mem_sup.1 hw with ⟨a, ha, b, hb, hab⟩
      have haD : a ∈ vectorSpan ℝ (insert y S) := hmono ha
      have hbD : b ∈ vectorSpan ℝ (insert y S) := hsb b hb
      rw [← hab]
      exact add_mem haD hbD
  have hvD : y - y0 ∉ D := by
    intro h
    apply hy
    have hmem : (y - y0) +ᵥ y0 ∈ (affineSpan ℝ S : Set V3) :=
      AffineSubspace.vadd_mem_of_mem_direction
        (by rw [direction_affineSpan]; exact h) hy0S
    have h2 : (y - y0 : V3) +ᵥ y0 = y := by rw [vadd_eq_add]; abel
    rw [h2] at hmem
    exact hmem
  have hinf : D ⊓ Submodule.span ℝ {y - y0} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hwK : w ∈ D := (Submodule.mem_inf.1 hw).1
    have hwS := (Submodule.mem_inf.1 hw).2
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hwS
    have hs0 : s = 0 := by
      by_contra hs0
      have hinv : s⁻¹ * s = 1 := inv_mul_cancel₀ hs0
      have h2 : (s⁻¹ • (s • (y - y0)) : V3) ∈ D := Submodule.smul_mem _ _ hwK
      rw [smul_smul, hinv, one_smul] at h2
      exact hvD h2
    rw [hs0, zero_smul]
  have hvyne : (y - y0 : V3) ≠ 0 := by
    intro h0
    rw [h0] at hvD
    exact hvD (Submodule.zero_mem D)
  have hfr : Module.finrank ℝ (vectorSpan ℝ (insert y S))
      = Module.finrank ℝ (vectorSpan ℝ S) + 1 := by
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq D (Submodule.span ℝ {y - y0})
    rw [hinf, finrank_bot] at h2
    have h3 : Module.finrank ℝ (Submodule.span ℝ {y - y0}) = 1 :=
      finrank_span_singleton hvyne
    rw [h3] at h2
    rw [hvec]
    omega
  have hneI : (insert y S).Nonempty := ⟨y0, Set.mem_insert_of_mem _ hy0⟩
  have hneI' : insert y S ≠ ∅ := Set.nonempty_iff_ne_empty.mp hneI
  simp only [affDim, if_neg hneI', if_neg (Set.nonempty_iff_ne_empty.mp ⟨y0, hy0⟩)]
  rw [hfr]
  omega

/-- Rogers.hl:4340 `MHFTTZN_lemma2`. -/
theorem MHFTTZN_lemma2 (V : Set V3) (ul : List V3) (k : ℕ) (hP : Packing V)
    (hbar : barV V k ul) :
    affDim (setOfList ul) = (k : ℤ) ∧
      ∀ u v : V3, u ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) →
        v ∈ (affineSpan ℝ (setOfList ul) : Set V3) →
          (u - circumcenter (setOfList ul)) ⬝ᵥ (v - circumcenter (setOfList ul)) = 0 := by
  revert ul
  induction k with
  | zero =>
    intro ul hbar
    have h1 := hbar.1
    rw [LENGTH_1_LEMMA ul h1]
    have hset : setOfList [hdV ul] = ({hdV ul} : Set V3) := by simp [setOfList]
    constructor
    · rw [hset, affDim_singleton]
      simp
    · intro u v hu hv
      have hcirc : circumcenter (setOfList [hdV ul]) = hdV [hdV ul] := by
        rw [hset]
        exact CIRCUMCENTER_1 (hdV ul)
      rw [hset] at hv
      have h2 : (affineSpan ℝ ({hdV ul} : Set V3) : Set V3) = {hdV ul} := by
        ext z
        simp [AffineSubspace.mem_affineSpan_singleton]
      rw [h2, Set.mem_singleton_iff] at hv
      rw [hcirc, hv, show ((hdV [hdV ul] : V3) = hdV ul) from rfl, sub_self,
        dotProduct_zero]
  | succ k ih =>
    intro ul hbar
    have hkle : k + 1 ≤ 3 := BARV_IMP_K_LE_3 V ul (k + 1) hbar
    have hlen : ul.length = k + 1 + 1 := hbar.1
    have h2le : 2 ≤ ul.length := by omega
    have htr : truncateSimplex k ul = ul.dropLast := by
      have h := TRUNCATE_SIMPLEX_EQ_BUTLAST ul h2le
      rwa [show ul.length - 2 = k from by omega] at h
    have hbarv : barV V k (truncateSimplex k ul) :=
      TRUNCATE_SIMPLEX_BARV V k (k + 1) ul hbar (by omega)
    have hbarvl : barV V k ul.dropLast := htr ▸ hbarv
    have hhdv : hdV ul.dropLast = hdV ul := by
      rw [← htr]
      exact HD_TRUNCATE_SIMPLEX ul k (by omega)
    have ihvl := ih ul.dropLast hbarvl
    have hlt : ul.length - 1 < ul.length := by omega
    have hlast : elV ul (ul.length - 1) ∈ setOfList ul := by
      have h1 : elV ul (ul.length - 1) = ul[ul.length - 1] :=
        List.getD_eq_getElem (l := ul) (0:V3) hlt
      have h2 : ul[ul.length - 1] ∈ ul := List.getElem_mem hlt
      rw [h1]
      exact h2
    have hlastV : elV ul (ul.length - 1) ∈ V := BARV_SUBSET V (k + 1) ul hbar hlast
    have happend : ul = ul.dropLast ++ [elV ul (ul.length - 1)] := by
      have hLE := LIST_EQ_TRUNCATE_SIMPLEX_APPEND_LAST ul h2le
      rw [show ul.length - 2 = k from by omega, htr] at hLE
      exact hLE
    have hsetsplit : setOfList ul
        = insert (elV ul (ul.length - 1)) (setOfList ul.dropLast) := by
      conv_lhs => rw [happend]
      ext x
      simp only [setOfList, Set.mem_setOf_eq, List.mem_append, List.mem_singleton,
        Set.mem_insert_iff]
      tauto
    have hsub : setOfList ul.dropLast ⊆ setOfList ul := by
      rw [hsetsplit]
      intro x hx
      exact Set.mem_insert_of_mem _ hx
    have hdl1 : 1 ≤ ul.dropLast.length := by
      have hbl := LENGTH_BUTLAST ul (by omega)
      omega
    have hneSvl : (setOfList ul.dropLast).Nonempty :=
      ⟨hdV ul.dropLast, HD_IN_SET_OF_LIST ul.dropLast hdl1⟩
    have hfinS : (setOfList ul).Finite := by
      have hE : (setOfList ul : Set V3) = (ul.toFinset : Set V3) := by
        ext x
        simp [setOfList]
      exact hE ▸ ul.toFinset.finite_toSet
    have hcardle : Nat.card (setOfList ul) ≤ k + 1 + 1 := by
      have hE : (setOfList ul : Set V3) = (ul.toFinset : Set V3) := by
        ext x
        simp [setOfList]
      have h2 : Nat.card (setOfList ul) = ul.toFinset.card := by
        rw [hE, Nat.card_coe_set_eq, ncard_coe_finset]
      rw [h2]
      exact (List.toFinset_card_le ul).trans (le_of_eq hlen)
    have hSne : (setOfList ul).Nonempty := ⟨hdV ul, HD_IN_SET_OF_LIST ul (by omega)⟩
    -- Part 1
    have hA1 : affDim (setOfList ul) = (k : ℤ) + 1 := by
      by_cases hge : (k : ℤ) + 1 ≤ affDim (setOfList ul)
      · have hle : affDim (setOfList ul) ≤ (k : ℤ) + 1 := by
          have h1 := p6_affDim_le_card (setOfList ul) hfinS hSne
          have h2 := hcardle
          omega
        omega
      · exfalso
        have hdimSle : affDim (setOfList ul) ≤ (k : ℤ) := by omega
        have hyin : elV ul (ul.length - 1)
            ∈ (affineSpan ℝ (setOfList ul.dropLast) : Set V3) := by
          by_contra hcon
          have hins := p6_affDim_insert (setOfList ul.dropLast) (elV ul (ul.length - 1))
            hneSvl hcon
          rw [← hsetsplit] at hins
          have hmono := affDim_mono hsub hneSvl
          have h1 := ihvl.1
          omega
        -- the algebra: hull vl ⊆ hull ul forces a dimension drop
        set A0 := (affineSpan ℝ (voronoiList V ul.dropLast) : Set V3) with hA0def
        have hA0ih : A0 = ⋂₀ {bis (hdV ul) u | u ∈ setOfList ul.dropLast} := by
          have h := MHFTTZN_lemma V ul.dropLast k hP hbarvl
          rw [hhdv] at h
          exact h
        have hyA0 : elV ul (ul.length - 1) ∈
            (affineSpan ℝ (setOfList ul.dropLast) : Set V3) := hyin
        have hHDmem0 : hdV ul ∈ setOfList ul.dropLast := by
          rw [← hhdv]
          exact HD_IN_SET_OF_LIST ul.dropLast hdl1
        have hHDhull : hdV ul ∈ (affineSpan ℝ (setOfList ul.dropLast) : Set V3) :=
          subset_affineSpan ℝ (setOfList ul.dropLast) hHDmem0
        have hHDmem : hdV ul ∈ (affineSpan ℝ (setOfList ul.dropLast) : Set V3) :=
          hHDhull
        set y := elV ul (ul.length - 1) with hy
        set HD := hdV ul with hHDdef
        have hconst : ∀ p ∈ A0, (y - HD) ⬝ᵥ p = (y - HD) ⬝ᵥ circumcenter (setOfList ul.dropLast) := by
          intro p hp
          have h1 := ihvl.2 p y hp hyA0
          have h2 := ihvl.2 p HD hp hHDmem
          have h3 : (y - HD) ⬝ᵥ (p - circumcenter (setOfList ul.dropLast))
              = (y - HD) ⬝ᵥ p - (y - HD) ⬝ᵥ circumcenter (setOfList ul.dropLast) :=
            p6_dot_sub_l (y - HD) p _
          have h4 : (y - HD) ⬝ᵥ (p - circumcenter (setOfList ul.dropLast)) = 0 := by
            show (y - HD).ofLp ⬝ᵥ
              (p.ofLp - (circumcenter (setOfList ul.dropLast)).ofLp) = 0
            have h1' := h1
            have h2' := h2
            rw [WithLp.ofLp_sub, dotProduct_comm, sub_dotProduct, dotProduct_sub,
              dotProduct_sub] at h1'
            rw [WithLp.ofLp_sub, dotProduct_comm, sub_dotProduct, dotProduct_sub,
              dotProduct_sub] at h2'
            rw [WithLp.ofLp_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
            linarith
          linarith
        have hwne : (voronoiList V ul).Nonempty := by
          by_contra h0
          have h0' : voronoiList V ul = ∅ := Set.not_nonempty_iff_eq_empty.mp h0
          have hdim := AFF_DIM_VORONOI_LIST V ul (k + 1) hbar
          rw [h0', affDim_empty] at hdim
          omega
        have hsplitA1 : (affineSpan ℝ (voronoiList V ul) : Set V3)
            = A0 ∩ bis (hdV ul) y := by
          rw [MHFTTZN_lemma V ul (k + 1) hP hbar, hsetsplit]
          have himg2 : {bis (hdV ul) u
                | u ∈ insert (elV ul (ul.length - 1)) (setOfList ul.dropLast)}
              = insert (bis (hdV ul) (elV ul (ul.length - 1)))
                  {bis (hdV ul) u | u ∈ setOfList ul.dropLast} := by
            ext T
            simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
              Set.mem_image]
            constructor
            · rintro ⟨u, (rfl | hu), rfl⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨u, hu, rfl⟩
            · rintro (rfl | ⟨u, hu, rfl⟩)
              · exact ⟨elV ul (ul.length - 1), Or.inl rfl, rfl⟩
              · exact ⟨u, Or.inr hu, rfl⟩
          rw [himg2, Set.sInter_insert, ← hA0ih, Set.inter_comm]
        have hwmem : hwne.choose ∈ (affineSpan ℝ (voronoiList V ul) : Set V3) :=
          subset_affineSpan ℝ _ hwne.choose_spec
        have hw2 : hwne.choose ∈ A0 ∩ bis (hdV ul) y := by
          rw [← hsplitA1]
          exact hwmem
        have hwA0 : hwne.choose ∈ A0 := hw2.1
        have hwconst := hconst hwne.choose hwA0
        have hwbis : hwne.choose ∈ bis (hdV ul) y := hw2.2
        have hconstbis : 2 * ((y - HD) ⬝ᵥ hwne.choose) = y ⬝ᵥ y - HD ⬝ᵥ HD :=
          (p6_bis_dot (hdV ul) y hwne.choose).1 hwbis
        have hsubhull : (affineSpan ℝ (voronoiList V ul.dropLast) : Set V3)
            ⊆ (affineSpan ℝ (voronoiList V ul) : Set V3) := by
          intro p hp
          have hpA0 : p ∈ A0 := hp
          have hpconst := hconst p hpA0
          have hdotp : 2 * ((y - HD) ⬝ᵥ p) = y ⬝ᵥ y - HD ⬝ᵥ HD := by
            rw [hpconst, ← hwconst, hconstbis]
          rw [hsplitA1]
          exact ⟨hpA0, (p6_bis_dot (hdV ul) y p).2 hdotp⟩
        have hd1 : affDim (affineSpan ℝ (voronoiList V ul.dropLast) : Set V3) = 3 - k := by
          rw [p6_affDim_affineSpan]
          exact AFF_DIM_VORONOI_LIST V ul.dropLast k hbarvl
        have hd2 : affDim (affineSpan ℝ (voronoiList V ul) : Set V3) = 3 - (k + 1) := by
          rw [p6_affDim_affineSpan]
          exact AFF_DIM_VORONOI_LIST V ul (k + 1) hbar
        have hvnevl : (voronoiList V ul.dropLast).Nonempty := by
          by_contra h0
          have h0' : voronoiList V ul.dropLast = ∅ := Set.not_nonempty_iff_eq_empty.mp h0
          have hdim := AFF_DIM_VORONOI_LIST V ul.dropLast k hbarvl
          rw [h0', affDim_empty] at hdim
          omega
        have hsubdim : affDim (affineSpan ℝ (voronoiList V ul.dropLast) : Set V3)
            ≤ affDim (affineSpan ℝ (voronoiList V ul) : Set V3) := by
          refine affDim_mono hsubhull ⟨hvnevl.choose, ?_⟩
          rw [← hA0def]
          exact subset_affineSpan ℝ _ hvnevl.choose_spec
        omega
    -- Part 2
    refine ⟨hA1, ?_⟩
    intro u v hu hv
    have hcard : Nat.card (setOfList ul) = k + 1 + 1 := by
      have hcard_ge : (k + 1 + 1 : ℕ) ≤ Nat.card (setOfList ul) := by
        have h1 := p6_affDim_le_card (setOfList ul) hfinS hSne
        rw [hA1] at h1
        omega
      omega
    have hdep : ¬affineDependent (setOfList ul) :=
      p6_affdep_of_dim _ hfinS (by rw [hA1]; omega)
    have hHDmem : hdV ul ∈ setOfList ul := by
      apply hsub
      rw [← hhdv]
      exact HD_IN_SET_OF_LIST ul.dropLast hdl1
    set qc := circumcenter (setOfList ul) with hqc
    set HD := hdV ul with hHDdef
    have hqcHull : qc ∈ (affineSpan ℝ (setOfList ul) : Set V3) :=
      OAPVION1 (setOfList ul) (Set.nonempty_iff_ne_empty.mp hSne) hdep
    have hsplit2 : (affineSpan ℝ (voronoiList V ul) : Set V3)
        = ⋂₀ {bis (hdV ul) t | t ∈ setOfList ul} := MHFTTZN_lemma V ul (k + 1) hP hbar
    rw [hsplit2] at hu
    have key0 : ∀ y' ∈ setOfList ul, (u - qc) ⬝ᵥ (y' - HD) = 0 := by
      intro y' hy'
      have hubis : u ∈ bis (hdV ul) y' := hu (bis (hdV ul) y') ⟨y', hy', rfl⟩
      have hqdist1 := OAPVION2 (setOfList ul) hdep (hdV ul) hHDmem
      have hqdist2 := OAPVION2 (setOfList ul) hdep y' hy'
      have hqcbis : qc ∈ bis (hdV ul) y' := by
        show dist qc (hdV ul) = dist qc y'
        rw [← hqdist1, ← hqdist2]
      have h1 : 2 * ((y' - HD) ⬝ᵥ u) = y' ⬝ᵥ y' - HD ⬝ᵥ HD :=
        (p6_bis_dot (hdV ul) y' u).1 hubis
      have h2 : 2 * ((y' - HD) ⬝ᵥ qc) = y' ⬝ᵥ y' - HD ⬝ᵥ HD :=
        (p6_bis_dot (hdV ul) y' qc).1 hqcbis
      -- bridge the wrapped/distributed `ofLp` orientations explicitly
      have hc1 : u ⬝ᵥ (y' - HD) = (y' - HD) ⬝ᵥ u := p6_dot_comm u (y' - HD)
      have hc2 : qc ⬝ᵥ (y' - HD) = (y' - HD) ⬝ᵥ qc := p6_dot_comm qc (y' - HD)
      show (u - qc).ofLp ⬝ᵥ (y'.ofLp - HD.ofLp) = 0
      rw [WithLp.ofLp_sub, sub_dotProduct, hc1, hc2]
      linarith
    have hKle : vectorSpan ℝ (setOfList ul) ≤ LinearMap.ker (p6dot (u - qc)) := by
      rw [vectorSpan_def, Submodule.span_le]
      intro g hg
      obtain ⟨x, hx, y', hy', rfl⟩ := Set.mem_vsub.1 hg
      rw [SetLike.mem_coe, LinearMap.mem_ker, p6dot_apply]
      have hxe : (u - qc) ⬝ᵥ x = (u - qc) ⬝ᵥ HD := by
        have hk := key0 x hx
        have he : (u - qc) ⬝ᵥ (x - HD) = (u - qc) ⬝ᵥ x - (u - qc) ⬝ᵥ HD :=
          dotProduct_sub (u - qc).ofLp x.ofLp HD.ofLp
        rw [he] at hk
        linarith
      have hye : (u - qc) ⬝ᵥ y' = (u - qc) ⬝ᵥ HD := by
        have hk := key0 y' hy'
        have he : (u - qc) ⬝ᵥ (y' - HD) = (u - qc) ⬝ᵥ y' - (u - qc) ⬝ᵥ HD :=
          dotProduct_sub (u - qc).ofLp y'.ofLp HD.ofLp
        rw [he] at hk
        linarith
      rw [p6_dot_sub_l_vsub, hxe, hye, sub_self]
    have hvsp : (v - qc) ∈ vectorSpan ℝ (setOfList ul) := by
      rw [← direction_affineSpan]
      exact AffineSubspace.vsub_mem_direction hv hqcHull
    have hz := hKle hvsp
    rw [LinearMap.mem_ker, p6dot_apply] at hz
    exact hz


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
  have hlen : ul.length = k + 1 := hbar.1
  have hulne : ul ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hhd : hdV ul ∈ setOfList ul := by
    cases ul with
    | nil => exact absurd rfl hulne
    | cons a t => simp [setOfList, hdV]
  have hne : (setOfList ul).Nonempty := ⟨hdV ul, hhd⟩
  have hne' : setOfList ul ≠ ∅ := Set.nonempty_iff_ne_empty.mp hne
  have hE : (setOfList ul : Set V3) = (ul.toFinset : Set V3) := by
    ext x
    simp [setOfList]
  have hfinS : (setOfList ul).Finite := hE ▸ ul.toFinset.finite_toSet
  -- `CARD (set_of_list ul) = k + 1` (HOL:4922): `≤` via the list, `≥` via the dimension
  have hcard_le : Nat.card (setOfList ul) ≤ k + 1 := by
    have h2 : Nat.card (setOfList ul) = ul.toFinset.card := by
      rw [hE, Nat.card_coe_set_eq, ncard_coe_finset]
    rw [h2]
    exact (List.toFinset_card_le ul).trans (le_of_eq hlen)
  have hcard_ge : (k + 1 : ℕ) ≤ Nat.card (setOfList ul) := by
    have h1 := p6_affDim_le_card (setOfList ul) hfinS hne
    rw [MHFTTZN1 V ul k hP hbar] at h1
    omega
  have hcard : Nat.card (setOfList ul) = k + 1 := le_antisymm hcard_le hcard_ge
  have hdep : ¬affineDependent (setOfList ul) :=
    p6_affdep_of_dim _ hfinS (by rw [hcard, MHFTTZN1 V ul k hP hbar]; omega)
  -- `⊆`: orthogonality at `u := v := w` forces `w = circumcenter`
  ext w
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw1, hw2⟩
    have hkey := (MHFTTZN_lemma2 V ul k hP hbar).2 w w hw1 hw2
    have hzero : inner ℝ (w - circumcenter (setOfList ul))
        (w - circumcenter (setOfList ul)) = 0 := by
      rw [inner_eq_dot]
      exact hkey
    have hw0 : w - circumcenter (setOfList ul) = 0 := inner_self_eq_zero.mp hzero
    rw [sub_eq_zero] at hw0
    exact hw0
  · rintro rfl
    refine ⟨(MHFTTZN2 V ul k hP hbar _).mpr ?_, OAPVION1 _ hne' hdep⟩
    intro u hu
    have h1 := OAPVION2 (setOfList ul) hdep u hu
    have h2 := OAPVION2 (setOfList ul) hdep (hdV ul) hhd
    show dist (circumcenter (setOfList ul)) (hdV ul) = dist (circumcenter (setOfList ul)) u
    rw [← h1, ← h2]

/-- Rogers.hl:4985 `MHFTTZN4`. -/
theorem MHFTTZN4 (V : Set V3) (ul : List V3) (k : ℕ) (u v : V3) (hP : Packing V)
    (hbar : barV V k ul)
    (hu : u ∈ (affineSpan ℝ (voronoiList V ul) : Set V3))
    (hv : v ∈ (affineSpan ℝ (setOfList ul) : Set V3)) :
    (u - circumcenter (setOfList ul)) ⬝ᵥ (v - circumcenter (setOfList ul)) = 0 :=
  (MHFTTZN_lemma2 V ul k hP hbar).2 u v hu hv

/-! ### Private π/2–cosine bridge (HOL proves these inline; same content as
the `p7_*` helpers of PackingAuto7) -/

/-- For `a ∈ [0,π]`: `π/2 < a ↔ cos a < 0`. -/
private theorem p6_pi2_cos (a : ℝ) (h0 : 0 ≤ a) (hp : a ≤ Real.pi) :
    Real.pi / 2 < a ↔ Real.cos a < 0 := by
  constructor
  · intro h
    have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 2) (y := a)
      (by linarith [Real.pi_pos]) hp h
    rwa [Real.cos_pi_div_two] at h2
  · intro h
    by_contra hc
    have h2 : Real.cos (Real.pi / 2) ≤ Real.cos a :=
      Real.strictAntiOn_cos.antitoneOn (a := a) (b := Real.pi / 2) ⟨h0, hp⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by linarith)
    rw [Real.cos_pi_div_two] at h2
    exact absurd h (not_lt.mpr h2)

/-- Vector-level π/2 bridge (inner form). -/
private theorem p6_vec_pi2 (x y : V3) :
    Real.pi / 2 < InnerProductGeometry.angle x y ↔ inner ℝ x y < 0 := by
  have hrange := p6_pi2_cos (InnerProductGeometry.angle x y)
    (InnerProductGeometry.angle_nonneg x y) (InnerProductGeometry.angle_le_pi x y)
  rw [hrange, InnerProductGeometry.cos_angle]
  by_cases hnorm : ‖(x : V3)‖ * ‖(y : V3)‖ = 0
  · rw [hnorm, div_zero]
    have hx0 : inner ℝ x y = 0 := by
      rcases mul_eq_zero.mp hnorm with hx | hy
      · rw [norm_eq_zero.mp hx]; exact inner_zero_left y
      · rw [norm_eq_zero.mp hy]; exact inner_zero_right x
    simp [hx0]
  · have hpos : (0:ℝ) < ‖(x : V3)‖ * ‖(y : V3)‖ :=
      mul_pos (norm_pos_iff.mpr fun hz => hnorm (by simp [hz]))
        (norm_pos_iff.mpr fun hz => hnorm (by simp [hz]))
    constructor
    · intro h
      have h2 := mul_lt_mul_of_pos_right h hpos
      rw [div_mul_cancel₀ _ (ne_of_gt hpos), zero_mul] at h2
      exact h2
    · intro h
      by_contra hc
      have hc' : 0 ≤ inner ℝ x y / (‖(x : V3)‖ * ‖(y : V3)‖) := le_of_not_gt hc
      have h2 := mul_nonneg hc' (le_of_lt hpos)
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
      exact absurd h (not_lt.mpr h2)

/-- Vector-level π/2 bridge (dot form). -/
private theorem p6_vec_pi2_dot (x y : V3) :
    Real.pi / 2 < InnerProductGeometry.angle x y ↔ x ⬝ᵥ y < 0 := by
  rw [← inner_eq_dot x y]
  exact p6_vec_pi2 x y

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

/-- `arcV` is symmetric in its last two arguments. -/
private theorem p6_arcV_comm (p u v : V3) : arcV p u v = arcV p v u := by
  unfold arcV
  simp only [WithLp.ofLp_sub]
  rw [dotProduct_comm, mul_comm]

/-- `arcV` expressed through Mathlib's real inner product (local copy of
`LocalAuto6.arcV_eq`, needed before that file can be imported). -/
private theorem p6_arcV_eq (u v w : V3) :
    arcV u v w = Real.arccos (inner ℝ (v - u) (w - u) / (dist v u * dist w u)) := by
  rw [arcV, ← inner_eq_dot]
  rfl

/-- Rogers.hl:5022 `XYOFCGX_lemma0`. -/
theorem XYOFCGX_lemma0 (V S : Set V3) (p w : V3) (hV : Packing V) (hSV : S ⊆ V)
    (hS : ¬affineDependent S) (hp : p = circumcenter S) (hr : radV S < Real.sqrt 2)
    (hw : w ∈ V \ S) (hdw : dist p w ≤ radV S) (hcard : 1 < Nat.card S) :
    (∀ u ∈ S, Real.pi / 2 < arcV p w u) ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Real.pi / 2 < arcV p u v := by
  -- key geometry: two points at distance `< √2` from `a` and at distance `≥ 2`
  -- from each other subtend an obtuse angle at `a` (law of cosines).
  have key : ∀ a b c : V3, a ≠ b → a ≠ c → dist a b < Real.sqrt 2 →
      dist a c < Real.sqrt 2 → 2 ≤ dist b c → Real.cos (arcV a b c) < 0 := by
    intro a b c hab hac hdb hdc hbc
    have hid : 2 * ((b - a) ⬝ᵥ (c - a)) =
        dist a b ^ 2 + dist a c ^ 2 - dist b c ^ 2 := by
      have h := norm_sub_sq_real (b - a) (c - a)
      rw [inner_eq_dot] at h
      simp only [WithLp.ofLp_sub] at h ⊢
      have hsub : (b - a) - (c - a) = b - c := by abel
      rw [hsub] at h
      rw [dist_eq_norm, norm_sub_rev a b, dist_eq_norm, norm_sub_rev a c, dist_eq_norm]
      linarith
    have h1 : dist a b ^ 2 < 2 := by
      have hlt : |dist a b| < |Real.sqrt 2| := by
        rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (Real.sqrt_nonneg 2)]
        exact hdb
      have := (sq_lt_sq).mpr hlt
      rwa [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at this
    have h3 : dist a c ^ 2 < 2 := by
      have hlt : |dist a c| < |Real.sqrt 2| := by
        rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (Real.sqrt_nonneg 2)]
        exact hdc
      have := (sq_lt_sq).mpr hlt
      rwa [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at this
    have h4 : 4 ≤ dist b c ^ 2 := by
      have hle : |(2:ℝ)| ≤ |dist b c| := by
        rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg dist_nonneg]
        exact hbc
      have := (sq_le_sq).mpr hle
      norm_num at this ⊢
      exact this
    have hdot : (b - a) ⬝ᵥ (c - a) < 0 := by linarith [hid, h1, h3, h4]
    have hcs : |(b - a) ⬝ᵥ (c - a)| ≤ dist b a * dist c a := by
      have h := norm_inner_le_norm (𝕜 := ℝ) (b - a) (c - a)
      rw [inner_eq_dot, Real.norm_eq_abs, ← dist_eq_norm, ← dist_eq_norm] at h
      exact h
    have hden : 0 < dist b a * dist c a :=
      mul_pos (dist_pos.mpr (Ne.symm hab)) (dist_pos.mpr (Ne.symm hac))
    rw [arcV]
    have hq1 : -(1:ℝ) ≤ ((b - a) ⬝ᵥ (c - a)) / (dist b a * dist c a) := by
      rw [le_div_iff₀ hden]
      nlinarith [(abs_le.mp hcs).1]
    have hq2 : ((b - a) ⬝ᵥ (c - a)) / (dist b a * dist c a) ≤ 1 := by
      rw [div_le_iff₀ hden]
      nlinarith [(abs_le.mp hcs).2]
    rw [Real.cos_arccos hq1 hq2]
    exact div_neg_of_neg_of_pos hdot hden
  have hSne : S.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [h] at hcard
    simp at hcard
  have hp_ne (u : V3) (hu : u ∈ S) : p ≠ u := by
    rw [hp]
    exact CIRCUMCENTER_NOT_EQ S hS hcard u hu
  have hp_dist (u : V3) (hu : u ∈ S) : dist p u < Real.sqrt 2 := by
    rw [hp, ← OAPVION2 S hS u hu]
    exact hr
  have hpw : p ≠ w := by
    obtain ⟨u₀, hu₀⟩ := hSne
    intro hpeq
    have h1 : dist w u₀ < Real.sqrt 2 := by rw [← hpeq]; exact hp_dist u₀ hu₀
    have h2 : 2 ≤ dist w u₀ :=
      hV.dist_ge_two hw.1 (hSV hu₀) (by rintro rfl; exact hw.2 hu₀)
    have h3 : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    linarith
  constructor
  · intro u hu
    refine (ARCV_GT_PI2 p w u).mpr ?_
    rw [p6_arcV_comm p w u]
    exact key p u w (hp_ne u hu) hpw (hp_dist u hu) (lt_of_le_of_lt hdw hr)
      (hV.dist_ge_two (hSV hu) hw.1 (by rintro rfl; exact hw.2 hu))
  · intro u hu v hv huv
    exact (ARCV_GT_PI2 p u v).mpr
      (key p u v (hp_ne u hu) (hp_ne v hv) (hp_dist u hu) (hp_dist v hv)
        (hV.dist_ge_two (hSV hu) (hSV hv) huv))

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
  intro u hu v hv
  have hfin : S.Finite :=
    finite_set_of_fin_dim_affineIndependent (k := ℝ) (not_not.mp hS)
  have hpos : 0 < Nat.card S := Nat.card_pos_iff.mpr ⟨⟨u, hu⟩, hfin⟩
  have hcard1 : Nat.card S = 1 := by omega
  obtain ⟨x, hx⟩ := CARD_1_IMP_SING S hfin hcard1
  have hux : u = x := by rw [hx] at hu; simpa using hu
  have hvx : v ≠ x := by
    intro h
    exact hv.2 (by rw [hx, h]; simp)
  rw [hp, hx, CIRCUMCENTER_1, hux, dist_self]
  exact dist_pos.mpr hvx

/-- Rogers.hl:5222 `CIRCUMCENTER_2`. (HOL `midpoint (a,b)`; Mathlib
`midpoint ℝ a b`.) -/
theorem CIRCUMCENTER_2 (a b : V3) : circumcenter {a, b} = midpoint ℝ a b := by
  rcases eq_or_ne a b with hab | hab
  · subst hab
    have hset : ({a, a} : Set V3) = {a} := by simp
    rw [hset, CIRCUMCENTER_1, midpoint_self]
  · have hmem_a : (a : V3) ∈ ({a, b} : Set V3) := by simp
    have hmem_b : (b : V3) ∈ ({a, b} : Set V3) := by simp
    have hsing : ({a, b} : Set V3) \ {a} = {b} := by
      ext z
      by_cases hz : z = a
      · subst hz; simp [hab]
      · by_cases hz2 : z = b
        · subst hz2; simp [hz]
        · simp [hz, hz2]
    have hsubne : (b - a) ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have key : AffineIndependent ℝ (fun x : ({a, b} : Set V3) => (x : V3)) := by
      rw [affineIndependent_set_iff_linearIndependent_vsub (k := ℝ) hmem_a]
      rw [hsing, Set.image_singleton, vsub_eq_sub]
      rw [linearIndependent_unique_iff]
      exact hsubne
    have hma : (a : V3) ∈ ((affineSpan ℝ ({a, b} : Set V3) : Set V3)) :=
      SetLike.mem_coe.mpr (mem_affineSpan ℝ hmem_a)
    have hmb : (b : V3) ∈ ((affineSpan ℝ ({a, b} : Set V3) : Set V3)) :=
      SetLike.mem_coe.mpr (mem_affineSpan ℝ hmem_b)
    have hmid : (midpoint ℝ a b) ∈
        ((affineSpan ℝ ({a, b} : Set V3) : Set V3)) :=
      Convex.midpoint_mem (AffineSubspace.convex _) hma hmb
    refine OAPVION3_concl _ (not_not_intro key) _ hmid ⟨dist a b / 2, ?_⟩ |>.symm
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | rfl
    · rw [dist_midpoint_left, show ‖(2 : ℝ)‖⁻¹ = (1:ℝ) / 2 from by norm_num]; ring
    · rw [dist_midpoint_right, show ‖(2 : ℝ)‖⁻¹ = (1:ℝ) / 2 from by norm_num]; ring

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

/-- `b - midpoint a b = -(a - midpoint a b)`: the two endpoints of the
midpoint are opposite vectors from it. -/
private theorem p6_midpoint_sub (a b : V3) :
    b - midpoint ℝ a b = -(a - midpoint ℝ a b) := by
  rw [left_sub_midpoint, right_sub_midpoint, ← smul_neg, neg_sub]

/-- The angles from a point `v` to the two endpoints of a midpoint are
supplementary: `arcV m v b = π - arcV m v a`. -/
private theorem p6_arcV_midpoint (a b v : V3) :
    arcV (midpoint ℝ a b) v b = Real.pi - arcV (midpoint ℝ a b) v a := by
  set m := midpoint ℝ a b
  have hsub : b - m = -(a - m) := p6_midpoint_sub a b
  have hdist : dist b m = dist a m := by
    rw [dist_comm b, dist_comm a, dist_midpoint_left, dist_midpoint_right]
  rw [p6_arcV_eq, p6_arcV_eq]
  have harg : inner ℝ (v - m) (b - m) / (dist v m * dist b m) =
      -(inner ℝ (v - m) (a - m) / (dist v m * dist a m)) := by
    rw [hsub, hdist, inner_neg_right]
    ring
  rw [harg, Real.arccos_neg]

/-- Rogers.hl:5252 `XYOFCGX_2`. -/
theorem XYOFCGX_2 (V S : Set V3) (p : V3) (hV : Packing V) (hSV : S ⊆ V)
    (hS : ¬affineDependent S) (hp : p = circumcenter S) (hr : radV S < Real.sqrt 2)
    (hcard : Nat.card S = 2) :
    ∀ u ∈ S, ∀ v ∈ V \ S, dist v p > dist u p := by
  intro u hu v hv
  by_contra hcon
  have hle : dist v p ≤ dist u p := le_of_not_gt hcon
  have hurad : radV S = dist u p := by
    rw [hp, dist_comm]; exact OAPVION2 S hS u hu
  have hdv : dist p v ≤ radV S := by rw [dist_comm, hurad]; exact hle
  -- `v` also lies within the circumradius, so `XYOFCGX_lemma0` bounds the
  -- angles from `v` to every point of `S`.
  have h0 := (XYOFCGX_lemma0 V S p v hV hSV hS hp hr hv hdv (by omega)).1
  have hfin : S.Finite :=
    finite_set_of_fin_dim_affineIndependent (k := ℝ) (not_not.mp hS)
  obtain ⟨a, b, hSab, hab⟩ := CARD_2_IMP_DOUBLE S hfin hcard
  have ha : a ∈ S := by rw [hSab]; simp
  have hb : b ∈ S := by rw [hSab]; simp
  have hpa : p = midpoint ℝ a b := by rw [hp, hSab, CIRCUMCENTER_2]
  have hA : Real.pi / 2 < arcV p v a := h0 a ha
  have hB : Real.pi / 2 < arcV p v b := h0 b hb
  -- the two angles are supplementary, so they cannot both exceed `π/2`.
  have hrel : arcV p v b = Real.pi - arcV p v a := by
    rw [hpa]; exact p6_arcV_midpoint a b v
  rw [hrel] at hB
  linarith

/-- Rogers.hl:5292 `ANGLE_GT_PI2`. (HOL `angle (a,b,c)`; Mathlib
`EuclideanGeometry.angle a b c`, the angle at `b`.) -/
theorem ANGLE_GT_PI2 (a b c : V3) :
    Real.pi / 2 < EuclideanGeometry.angle a b c ↔ (a - b) ⬝ᵥ (c - b) < 0 :=
  p6_vec_pi2_dot (a - b) (c - b)

/-- Rogers.hl:5348 `AZIM_COMPL_EXT`. -/
theorem AZIM_COMPL_EXT (v w a b : V3) :
    azim v w b a =
      if azim v w a b = 0 then 0 else 2 * Real.pi - azim v w a b := by
  by_cases ha : Collinear3 v w a
  · simp [azim, ha]
  · by_cases hb : Collinear3 v w b
    · simp [azim, hb]
    · exact azim_compl ha hb

/-- Rogers.hl:5365 `AZIM_EQ_SYM`. (Part A boundary; part B
(`STRICT_CYCLIC_IMP_FAN`, Rogers.hl:5373) in `Kepler/Text/PackingAuto7`.) -/
theorem AZIM_EQ_SYM (v w a b c : V3) :
    azim v w b a = azim v w c a ↔ azim v w a b = azim v w a c := by
  by_cases ha : Collinear3 v w a
  · simp [azim, ha]
  · by_cases hb : Collinear3 v w b
    · have h0b : azim v w b a = 0 ∧ azim v w a b = 0 :=
        ⟨by simp [azim, hb], by simp [azim, hb]⟩
      by_cases hc : Collinear3 v w c
      · have h0c : azim v w c a = 0 ∧ azim v w a c = 0 :=
          ⟨by simp [azim, hc], by simp [azim, hc]⟩
        simp [h0b.1, h0b.2, h0c.1, h0c.2]
      · constructor
        · intro h
          have hca : azim v w c a = 0 := h.symm.trans h0b.1
          have hac : azim v w a c = 0 := (azim_eq_zero_symm hc ha).mp hca
          rw [h0b.2, hac]
        · intro h
          have hac : azim v w a c = 0 := h.symm.trans h0b.2
          have hca : azim v w c a = 0 := (azim_eq_zero_symm hc ha).mpr hac
          rw [h0b.1, hca]
    · by_cases hc : Collinear3 v w c
      · have h0c : azim v w c a = 0 ∧ azim v w a c = 0 :=
          ⟨by simp [azim, hc], by simp [azim, hc]⟩
        constructor
        · intro h
          have hba : azim v w b a = 0 := h.trans h0c.1
          have hab : azim v w a b = 0 := (azim_eq_zero_symm hb ha).mp hba
          rw [hab, h0c.2]
        · intro h
          have hab : azim v w a b = 0 := h.trans h0c.2
          have hba : azim v w b a = 0 := (azim_eq_zero_symm hb ha).mpr hab
          rw [hba, h0c.1]
      · constructor
        · intro h
          rw [azim_compl hb ha, azim_compl hc ha, h]
        · intro h
          rw [azim_compl ha hb, azim_compl ha hc, h]

end Kepler.Text
