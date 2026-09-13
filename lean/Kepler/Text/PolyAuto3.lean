/-
Port of the HOL Light Flyspeck `polyhedron.hl` top-level theorems, batch 3
(polyhedron.hl:283-569).

Source: `reference/flyspeck/text_formalization/fan/polyhedron.hl`
(Flyspeck book formalization; persistent copy `lean/scripts/polyhedron.hl`).

Coverage (batch 3 of polyhedron.hl, theorems whose `let = prove` starts in
:283-:569, exactly 10):
- `FAN_TRANSLATION_EQ` (:283)
- `FAN_LINEAR_IMAGE_EQ` (:289)
- `BASE_POINT_FAN_TRANSLATION_EQ` (:298)
- `BASE_POINT_FAN_LINEAR_IMAGE_EQ` (:304)
- `SET_OF_EDGE_TRANSLATION_EQ` (:311)
- `SET_OF_EDGE_LINEAR_IMAGE_EQ` (:318)
- `POLYHEDRON_FAN` (:342)
- `CONVEX_RELATIVE_INTERIOR` (:514)
- `LEMMA` (:517)  [note: this batch OWNS the HOL name `LEMMA`; a later
  batch's `LEMMA` (polyhedron.hl:858) is to be renamed, not this one]
- `CONVEX_RELATIVE_INTERIOR_FACE` (:561)

Porting method: skeleton (frozen statements + per-theorem HOL docstrings);
proofs to be filled by the auto_loop/big-pickle harness. Every proof is a
bare `sorry`.

Encoding notes (gaps / closest existing encodings):
- HOL `real^3` ↔ `V3 = EuclideanSpace ℝ (Fin 3)` (Kepler/Geom/Azim.lean:33);
  HOL `(real^3->bool)` ↔ `Set V3`; HOL `((real^3->bool)->bool)` ↔
  `Set (Set V3)`.
- HOL `FAN` ↔ `FAN` (Kepler/Text/Fan.lean:56); HOL `set_of_edge` ↔
  `setOfEdge` (Kepler/Text/Fan.lean:62).
- HOL `IMAGE (IMAGE (\x. a + x)) E` ↔
  `(fun s : Set V3 => (fun y : V3 => a + y) '' s) '' E`; HOL
  `IMAGE f E` (E a set of sets) ↔ `(fun s : Set V3 => f '' s) '' E`.
- HOL `linear f /\ (!x y. f x = f y ==> x = y)` for `f : real^3 -> real^3`
  is encoded by taking `f : V3 →ₗ[ℝ] V3` (the linearity hypothesis is
  absorbed into the type) plus `Function.Injective f`.
- HOL `base_point_fan (x,V,E) = x` (fan/fan.hl:67) is NOT ported as a
  definition; it is inlined by its defining formula on both sides of the
  two `BASE_POINT_FAN_*` statements (which therefore degenerate to point
  identities; the unused `V`/`E` arguments are kept for signature
  fidelity).
- HOL `polyhedron s` (hol-light Multivariate/polytope.ml:4385:
  `?f. FINITE f /\ s = INTERS f /\ (!h. h IN f ==> ?a b. ~(a = vec 0) /\
  h = {x | a dot x <= b})`) has no Lean counterpart in the repo; it is
  INLINED verbatim as
  `∃ f : Set (Set V3), f.Finite ∧ s = ⋂₀ f ∧ ∀ h ∈ f, ∃ a : V3, ∃ b : ℝ,
  a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b}` in the three polyhedron theorems.
- HOL `relative_interior s` (IN_RELATIVE_INTERIOR, flyspeck.ml) maps to
  Mathlib's intrinsic interior `intrinsicInterior ℝ s`
  (Mathlib/Analysis/Convex/Intrinsic.lean:61, the `affineSpan`-based
  relative interior); no new definition is introduced.
- HOL `vertices s = {x | x extreme_point_of s}` (flyspeck_multivariate.ml
  :6884) is inlined as `Set.extremePoints ℝ p`
  (Mathlib/Analysis/Convex/Extreme.lean:68; `mem_extremePoints` matches
  the HOL open-segment formulation).
- HOL `face_of` (polytope.ml:13, `t SUBSET s /\ convex t /\ !a b x.
  a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b) ==> a IN t /\ b IN t`,
  with HOL `segment(a,b)` the OPEN segment) and HOL `edge_of`
  (polytope.ml:2847, `e face_of s /\ aff_dim e = &1`) are inlined; the
  affine-dimension condition `aff_dim (segment[v,w]) = &1` is encoded by
  its segment-equivalent `v ≠ w` (this Mathlib v4.32.2 has no affine
  dimension API); HOL open `segment(a,b)` ↔ `openSegment ℝ a b`, HOL
  closed `segment[v,w]` ↔ `segment ℝ v w`.
- HOL `bounded p` ↔ `Bornology.IsBounded p`；HOL `interior p` ↔ `interior p`
  (Mathlib topology); HOL `convex` ↔ `Convex ℝ`; HOL `dot` ↔ `⬝ᵥ`
  (Kepler/Geom/Azim.lean:40); HOL `INTERS {g y | y IN f}` ↔ `⋂ y ∈ f, g y`
  (`Set.iInter`, repo convention cf. ConformingDefs.lean header).
- This file imports `Mathlib` (in addition to the PlanarityAuto16 +
  ConformingDefs chain) because `intrinsicInterior`, `Set.extremePoints`,
  `segment`/`openSegment` and `interior` are not reachable from those
  Kepler imports alone.
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom
open Kepler.Text.Fan
open Classical

/-! ## 平移与线性像不变性（polyhedron.hl:283-339） -/

/-! ### 平移/单射线性像下的逐合取项传输辅助引理 -/

/-- `V3` 中 `p -ᵥ q = p - q`（自身 torsor）。 -/
private theorem vsub_eq_sub' (p q : V3) : p -ᵥ q = p - q := by
  simp

/-- 像 `g '' t` 的差集即原差集（平移不改差）。 -/
private theorem add_image_vsub (a : V3) (t : Set V3) :
    ((fun y : V3 => a + y) '' t) -ᵥ ((fun y : V3 => a + y) '' t) = t -ᵥ t := by
  ext z
  constructor
  · intro hz
    obtain ⟨p, hp, q, hq, hz'⟩ := Set.mem_vsub.mp hz
    obtain ⟨w, hw, rfl⟩ := hp
    obtain ⟨w', hw', rfl⟩ := hq
    refine Set.mem_vsub.mpr ⟨w, hw, w', hw', ?_⟩
    have hb : (a + w : V3) - (a + w') = z := hz'
    rw [add_sub_add_left_eq_sub] at hb
    rw [vsub_eq_sub']
    exact hb
  · intro hz
    obtain ⟨u, hu, u', hu', hzu⟩ := Set.mem_vsub.mp hz
    refine Set.mem_vsub.mpr ⟨a + u, Set.mem_image_of_mem _ hu, a + u',
      Set.mem_image_of_mem _ hu', ?_⟩
    have hb : u - u' = z := hzu
    rw [vsub_eq_sub', add_sub_add_left_eq_sub]
    exact hb

/-- 平移不改变共线性。 -/
private theorem collinear_add_image_iff (a : V3) (t : Set V3) :
    Collinear ℝ ((fun y : V3 => a + y) '' t) ↔ Collinear ℝ t := by
  rw [collinear_iff_rank_le_one ℝ, collinear_iff_rank_le_one ℝ,
    vectorSpan_def ℝ, vectorSpan_def ℝ, add_image_vsub]

/-- 单射线性映射下 `f '' t` 的差集即原差集的像。 -/
private theorem lin_image_vsub {f : V3 →ₗ[ℝ] V3} (t : Set V3) :
    ((⇑f) '' t) -ᵥ ((⇑f) '' t) = (⇑f) '' (t -ᵥ t) := by
  ext z
  rw [Set.mem_vsub, Set.mem_image]
  constructor
  · rintro ⟨p, hp, q, hq, hz⟩
    obtain ⟨w, hw, rfl⟩ := hp
    obtain ⟨w', hw', rfl⟩ := hq
    refine ⟨w - w', Set.mem_vsub.mpr ⟨w, hw, w', hw', rfl⟩, ?_⟩
    have hb : f w - f w' = z := hz
    rw [map_sub]
    exact hb
  · rintro ⟨u, hu, hzu⟩
    obtain ⟨w, hw, w', hw', hwu⟩ := Set.mem_vsub.mp hu
    have hwu' : w - w' = u := hwu
    refine ⟨f w, Set.mem_image_of_mem _ hw, f w', Set.mem_image_of_mem _ hw', ?_⟩
    rw [vsub_eq_sub', ← hzu, ← hwu', map_sub]

/-- 单射线性映射不改变共线性。 -/
private theorem collinear_lin_image_iff {f : V3 →ₗ[ℝ] V3} (hf : Function.Injective f)
    (t : Set V3) : Collinear ℝ ((⇑f) '' t) ↔ Collinear ℝ t := by
  rw [collinear_iff_rank_le_one ℝ, collinear_iff_rank_le_one ℝ,
    vectorSpan_def ℝ, vectorSpan_def ℝ, lin_image_vsub, ← Submodule.map_span,
    rank_map_eq hf]

/-- 单射函数像相等推出原像相等。 -/
private theorem image_eq_of_image_eq {g : V3 → V3} (hg : Function.Injective g) {A B : Set V3}
    (h : g '' A = g '' B) : A = B := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hgw⟩ := h ▸ Set.mem_image_of_mem _ hz
    rw [hg hgw] at hw
    exact hw
  · intro hz
    obtain ⟨w, hw, hgw⟩ := h.symm ▸ Set.mem_image_of_mem _ hz
    rw [hg hgw] at hw
    exact hw

/-- 平移像半空间中点的回拉：`v ∈ affGe {a+x} ((a+·) '' t)` 时 `v - a ∈ affGe {x} t`。 -/
private theorem affGe_add_image_sub (a x : V3) {t : Set V3} {v : V3}
    (hv : v ∈ affGe {a + x} ((fun y : V3 => a + y) '' t)) : v - a ∈ affGe {x} t := by
  have hinj : Function.Injective (fun y : V3 => a + y) := fun u w h => add_left_cancel h
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hv ⊢
  obtain ⟨c, h, hval, hsign, hsum⟩ := hv
  have hFeq : ((h.toFinset : Set V3)) = {a + x} ∪ (fun y : V3 => a + y) '' t :=
    h.coe_toFinset
  have hInj : Set.InjOn (fun y : V3 => a + y)
      ((fun y : V3 => a + y) ⁻¹' (h.toFinset : Set V3)) := fun u _ w _ huw =>
    add_left_cancel huw
  set F₀ : Finset V3 := h.toFinset.preimage (fun y : V3 => a + y) hInj with hF₀eq
  have hmem₀ : ∀ w : V3, w ∈ F₀ ↔ a + w ∈ h.toFinset := by
    intro w
    rw [hF₀eq]
    exact Finset.mem_preimage
  have himg : F₀.image (fun y : V3 => a + y) = h.toFinset := by
    apply Finset.ext
    intro u
    rw [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hmem₀ w).1 hw
    · intro hu
      refine ⟨u - a, (hmem₀ (u - a)).2 ?_, by simp⟩
      have hau : (a + (u - a) : V3) = u := by simp
      rw [hau]
      exact hu
  have hsub₀ : ∀ w : V3, w ∈ F₀ → w ∈ {x} ∪ t := by
    intro w hw
    have hw' : (a + w : V3) ∈ {a + x} ∪ (fun y : V3 => a + y) '' t := by
      rw [← hFeq]
      exact (hmem₀ w).1 hw
    simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hw'
    rcases hw' with hr | ⟨w', hw', hrw'⟩
    · exact Or.inl (add_left_cancel hr)
    · exact Or.inr (by rw [← hinj hrw']; exact hw')
  have hfin : ({x} ∪ t : Set V3).Finite := by
    have h1 : ((fun y : V3 => a + y) ⁻¹' ({a + x} ∪ (fun y : V3 => a + y) '' t)).Finite :=
      Set.Finite.preimage (fun u _ w _ huw => add_left_cancel huw) h
    have h2 : {x} ∪ t ⊆ (fun y : V3 => a + y) ⁻¹' ({a + x} ∪
        (fun y : V3 => a + y) '' t) := by
      intro w hw
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at hw
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff, Set.mem_image]
      rcases hw with hr | hw'
      · exact Or.inl (by rw [hr])
      · exact Or.inr ⟨w, hw', rfl⟩
    exact h1.subset h2
  have hF₀sub : ∀ w ∈ F₀, w ∈ hfin.toFinset := by
    intro w hw
    exact (Set.Finite.mem_toFinset (hs := hfin)).2 (hsub₀ w hw)
  have hsumimg : ∑ u ∈ F₀.image (fun y : V3 => a + y), c u = ∑ w ∈ F₀, c (a + w) :=
    Finset.sum_image (fun u _ w _ huw => hinj huw)
  have hsum₀ : ∑ w ∈ F₀, c (a + w) = 1 := by
    rw [← hsumimg, himg]
    simpa using hsum
  have hvalimg : ∑ u ∈ F₀.image (fun y : V3 => a + y), c u • u =
      ∑ w ∈ F₀, c (a + w) • (a + w) :=
    Finset.sum_image (fun u _ w _ huw => hinj huw)
  have hsplit : ∑ w ∈ F₀, c (a + w) • (a + w) =
      (∑ w ∈ F₀, c (a + w)) • a + ∑ w ∈ F₀, c (a + w) • w := by
    rw [Finset.sum_congr rfl (fun w _ => smul_add _ _ _), Finset.sum_add_distrib,
      Finset.sum_smul]
  set S : V3 := ∑ w ∈ F₀, c (a + w) • w with hSeq
  have hval' : v = a + S := by
    rw [hval, ← himg, hvalimg, hsplit, hsum₀, one_smul]
  refine ⟨fun w => if w ∈ F₀ then c (a + w) else 0, hfin, ?_, ?_, ?_⟩
  · -- 数值
    have hzero : ∀ w ∈ F₀, (if w ∈ F₀ then c (a + w) else 0) • w = c (a + w) • w :=
      fun w hw => by simp [hw]
    rw [← Finset.sum_subset hF₀sub (fun w _ hw' => by simp [hw']),
      Finset.sum_congr rfl hzero, ← hSeq]
    refine sub_eq_of_eq_add ?_
    exact hval'.trans (add_comm a S)
  · -- 符号
    intro w hw
    have hw₀ : w ∈ F₀ := (hmem₀ w).2 (by
      have hwu : (a + w : V3) ∈ {a + x} ∪ (fun y : V3 => a + y) '' t := by
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image]
        exact Or.inr ⟨w, hw, rfl⟩
      show (a + w : V3) ∈ (h.toFinset : Set V3)
      rw [hFeq]
      exact hwu)
    show 0 ≤ (if w ∈ F₀ then c (a + w) else 0)
    rw [if_pos hw₀]
    exact hsign _ (Set.mem_image_of_mem _ hw)
  · -- 和
    have hzero2 : ∀ w ∈ F₀, (if w ∈ F₀ then c (a + w) else 0) = c (a + w) :=
      fun w hw => by simp [hw]
    rw [← Finset.sum_subset hF₀sub (fun w _ hw' => by simp [hw']),
      Finset.sum_congr rfl hzero2]
    exact hsum₀

/-- 平移像半空间中点的直推：`u ∈ affGe {x} t` 时 `a + u ∈ affGe {a+x} ((a+·) '' t)`。 -/
private theorem affGe_add_image_add (a x : V3) {t : Set V3} {u : V3}
    (hu : u ∈ affGe {x} t) : a + u ∈ affGe {a + x} ((fun y : V3 => a + y) '' t) := by
  have hinjOn : Set.InjOn (fun y : V3 => a + y) ({x} ∪ t) := fun p _ q _ hpq =>
    add_left_cancel hpq
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hu ⊢
  obtain ⟨c, h₀, hval, hsign, hsum⟩ := hu
  have hset : ({a + x} ∪ ((fun y : V3 => a + y) '' t) : Set V3) =
      (fun y : V3 => a + y) '' ({x} ∪ t) := by
    rw [Set.image_union, Set.image_singleton]
  have hfin2 : ({a + x} ∪ ((fun y : V3 => a + y) '' t) : Set V3).Finite := by
    rw [hset]
    exact Set.Finite.image (fun y : V3 => a + y) h₀
  have hF2 : hfin2.toFinset = h₀.toFinset.image (fun y : V3 => a + y) := by
    apply Finset.coe_injective
    rw [Set.Finite.coe_toFinset, Finset.coe_image, Set.Finite.coe_toFinset h₀]
    exact hset
  have hinjF : Set.InjOn (fun y : V3 => a + y) (h₀.toFinset : Set V3) :=
    hinjOn.mono (fun p hp => (Set.Finite.mem_toFinset (hs := h₀)).mp hp)
  have hvalimg : ∑ z ∈ h₀.toFinset.image (fun y : V3 => a + y), c (z - a) • z =
      ∑ w ∈ h₀.toFinset, c (a + w - a) • (a + w) :=
    Finset.sum_image hinjF
  have hsumsub : ∑ w ∈ h₀.toFinset, c (a + w - a) • (a + w) =
      ∑ w ∈ h₀.toFinset, c w • (a + w) :=
    Finset.sum_congr rfl (fun w _ => by simp)
  have hsplit : ∑ w ∈ h₀.toFinset, c w • (a + w) =
      (∑ w ∈ h₀.toFinset, c w) • a + ∑ w ∈ h₀.toFinset, c w • w := by
    rw [Finset.sum_congr rfl (fun w _ => smul_add _ _ _), Finset.sum_add_distrib,
      Finset.sum_smul]
  refine ⟨fun z => c (z - a), hfin2, ?_, ?_, ?_⟩
  · -- 数值
    rw [hF2, hvalimg, hsumsub, hsplit, hsum, one_smul, ← hval]
  · -- 符号
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    show 0 ≤ c ((a + w) - a)
    rw [show (a + w) - a = w from by simp]
    exact hsign _ hw
  · -- 和
    rw [hF2]
    have hsumimg : ∑ z ∈ h₀.toFinset.image (fun y : V3 => a + y), c (z - a) =
        ∑ w ∈ h₀.toFinset, c (a + w - a) :=
      Finset.sum_image hinjF
    rw [hsumimg]
    have hsum' : ∑ w ∈ h₀.toFinset, c (a + w - a) = ∑ w ∈ h₀.toFinset, c w :=
      Finset.sum_congr rfl (fun w _ => by simp)
    rw [hsum']
    exact hsum

/-- `affGe` 在平移下的等变：`affGe {a+x} ((a+·) '' t) = (a+·) '' affGe {x} t`。 -/
private theorem affGe_add_image (a x : V3) (t : Set V3) :
    affGe {a + x} ((fun y : V3 => a + y) '' t) =
      (fun y : V3 => a + y) '' (affGe {x} t) := by
  ext v
  constructor
  · intro hmem
    exact ⟨v - a, affGe_add_image_sub a x hmem, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    exact affGe_add_image_add a x hu

/-- `affGe` 在单射线性像下的等变：`affGe {f x} (f '' t) = f '' affGe {x} t`。 -/
private theorem affGe_lin_image {f : V3 →ₗ[ℝ] V3} (hf : Function.Injective f) (x : V3)
    (t : Set V3) : affGe {f x} (f '' t) = f '' (affGe {x} t) := by
  ext v
  constructor
  · -- 正向：回拉
    have hinj : Function.Injective fun y : V3 => f y := hf
    intro hv
    simp only [affGe, Set.mem_setOf_eq, Affsign] at hv ⊢
    obtain ⟨c, h, hval, hsign, hsum⟩ := hv
    have hFeq : ((h.toFinset : Set V3)) = {f x} ∪ f '' t := h.coe_toFinset
    have hInj : Set.InjOn (f) ((f ⁻¹' (h.toFinset : Set V3))) := fun u _ w _ huw => hf huw
    set F₀ : Finset V3 := h.toFinset.preimage f hInj with hF₀eq
    have hmem₀ : ∀ w : V3, w ∈ F₀ ↔ (f w : V3) ∈ (h.toFinset : Set V3) := by
      intro w
      rw [hF₀eq]
      exact ⟨fun hw => Finset.mem_preimage.1 hw, fun hw => Finset.mem_preimage.2 hw⟩
    have himg : F₀.image f = h.toFinset := by
      apply Finset.ext
      intro u
      rw [Finset.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (hmem₀ w).1 hw
      · intro hu
        have hu' : (u : V3) ∈ {f x} ∪ f '' t :=
          (Set.Finite.mem_toFinset (hs := h)).mp hu
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at hu'
        rcases hu' with hr | ⟨w, hw, hrw⟩
        · refine ⟨x, (hmem₀ x).2 ?_, ?_⟩
          · rw [hFeq]
            simp only [Set.mem_union, Set.mem_singleton_iff]
            exact Or.inl trivial
          · rw [hr]
        · refine ⟨w, (hmem₀ w).2 ?_, ?_⟩
          · rw [hFeq]
            simp only [Set.mem_union, Set.mem_image]
            exact Or.inr ⟨w, hw, rfl⟩
          · exact hrw
    have hsub₀ : ∀ w : V3, w ∈ F₀ → w ∈ {x} ∪ t := by
      intro w hw
      have hw' : (f w : V3) ∈ {f x} ∪ f '' t := by
        rw [← hFeq]
        exact (hmem₀ w).1 hw
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at hw'
      rcases hw' with hr | ⟨w', hw', hrw'⟩
      · exact Or.inl (hf hr)
      · exact Or.inr (by rw [← hinj hrw']; exact hw')
    have hfin : ({x} ∪ t : Set V3).Finite := by
      have h1 : (f ⁻¹' ({f x} ∪ f '' t)).Finite :=
        Set.Finite.preimage (fun u _ w _ huw => hf huw) h
      have h2 : {x} ∪ t ⊆ f ⁻¹' ({f x} ∪ f '' t) := by
        intro w hw
        rcases (Set.mem_union _ _ _).mp hw with rfl | hw
        · simp
        · exact Set.mem_preimage.2 (by
            simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
            exact Or.inr ⟨w, hw, rfl⟩)
      exact h1.subset h2
    have hF₀sub : ∀ w ∈ F₀, w ∈ hfin.toFinset := fun w hw =>
      (Set.Finite.mem_toFinset (hs := hfin)).2 (hsub₀ w hw)
    have hsumimg : ∑ u ∈ F₀.image f, c u = ∑ w ∈ F₀, c (f w) :=
      Finset.sum_image (fun u _ w _ huw => hinj huw)
    have hsum₀ : ∑ w ∈ F₀, c (f w) = 1 := by
      rw [← hsumimg, himg]
      simpa using hsum
    have hvalimg : ∑ u ∈ F₀.image f, c u • u = ∑ w ∈ F₀, c (f w) • (f w) :=
      Finset.sum_image (fun u _ w _ huw => hinj huw)
    have hsplit : ∑ w ∈ F₀, c (f w) • (f w) = f (∑ w ∈ F₀, c (f w) • w) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun w _ => (map_smul f (c (f w)) w).symm)
    set S : V3 := ∑ w ∈ F₀, c (f w) • w with hSeq
    have hval' : v = f S := by
      rw [hval, ← himg, hvalimg, hsplit]
    refine ⟨S, ⟨fun w => if w ∈ F₀ then c (f w) else 0, hfin, ?_, ?_, ?_⟩, ?_⟩
    · -- 数值
      have hzero2 : ∀ w ∈ F₀, (if w ∈ F₀ then c (f w) else 0) • w = c (f w) • w :=
        fun w hw => by simp [hw]
      rw [← Finset.sum_subset hF₀sub (fun w _ hw' => by simp [hw']),
        Finset.sum_congr rfl hzero2, ← hSeq]
    · -- 符号
      intro w hw
      have hw₀ : w ∈ F₀ := (hmem₀ w).2 (by
        rw [hFeq]
        simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
        exact Or.inr ⟨w, hw, rfl⟩)
      show 0 ≤ (if w ∈ F₀ then c (f w) else 0)
      rw [if_pos hw₀]
      exact hsign _ (Set.mem_image_of_mem _ hw)
    · -- 和
      have hzero3 : ∀ w ∈ F₀, (if w ∈ F₀ then c (f w) else 0) = c (f w) :=
        fun w hw => by simp [hw]
      rw [← Finset.sum_subset hF₀sub (fun w _ hw' => by simp [hw']),
        Finset.sum_congr rfl hzero3]
      exact hsum₀
    · -- v = f S
      exact hval'.symm
  · -- 反向：直推
    intro hu
    obtain ⟨u, hu_mem, hu_val⟩ := hu
    have hinjOn : Set.InjOn f ({x} ∪ t) := fun p _ q _ hpq => hf hpq
    simp only [affGe, Set.mem_setOf_eq, Affsign] at hu_mem ⊢
    obtain ⟨c, h₀, hval, hsign, hsum⟩ := hu_mem
    have hinjF : Set.InjOn f (h₀.toFinset : Set V3) :=
      hinjOn.mono (fun p hp => (Set.Finite.mem_toFinset (hs := h₀)).mp hp)
    have heq : ({f x} ∪ (f '' t : Set V3)) = f '' ({x} ∪ t) := by
      rw [Set.image_union, Set.image_singleton]
    have hfin2 : ({f x} ∪ (f '' t : Set V3)).Finite := by
      rw [heq]
      exact Set.Finite.image f h₀
    have hF' : hfin2.toFinset = h₀.toFinset.image f := by
      apply Finset.coe_injective
      rw [Set.Finite.coe_toFinset, Finset.coe_image, Set.Finite.coe_toFinset h₀, heq]
    have hvalimg : ∑ z ∈ h₀.toFinset.image f, c (Function.invFun f z) • z =
        ∑ w ∈ h₀.toFinset, c (Function.invFun f (f w)) • (f w) :=
      Finset.sum_image hinjF
    have hsumsub : ∑ w ∈ h₀.toFinset, c (Function.invFun f (f w)) • (f w) =
        ∑ w ∈ h₀.toFinset, c w • (f w) :=
      Finset.sum_congr rfl (fun w _ => by rw [Function.leftInverse_invFun hf])
    have hsplit : ∑ w ∈ h₀.toFinset, c w • (f w) =
        f (∑ w ∈ h₀.toFinset, c w • w) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun w _ => (map_smul f (c w) w).symm)
    refine ⟨fun z => c (Function.invFun f z), hfin2, ?_, ?_, ?_⟩
    · -- 数值
      rw [hF', hvalimg, hsumsub, hsplit, ← hval]
      exact hu_val.symm
    · -- 符号
      intro z hz
      obtain ⟨w, hw, hzw⟩ := hz
      subst hzw
      show 0 ≤ c (Function.invFun f (f w))
      rw [Function.leftInverse_invFun hf]
      exact hsign _ hw
    · -- 和
      rw [hF']
      have hsumimg : ∑ z ∈ h₀.toFinset.image f, c (Function.invFun f z) =
          ∑ w ∈ h₀.toFinset, c (Function.invFun f (f w)) :=
        Finset.sum_image hinjF
      rw [hsumimg]
      have hsum' : ∑ w ∈ h₀.toFinset, c (Function.invFun f (f w)) =
          ∑ w ∈ h₀.toFinset, c w :=
        Finset.sum_congr rfl (fun w _ => congrArg c (Function.leftInverse_invFun hf w))
      rw [hsum']
      exact hsum


/-- `FAN` 在单射函数逐点像下的不变性（共线与 `affGe` 传输由参数给出）。 -/
private theorem FAN_image_iff {g : V3 → V3} (hg : Function.Injective g)
    (hcoll : ∀ t : Set V3, Collinear ℝ (g '' t) ↔ Collinear ℝ t)
    (haff : ∀ x : V3, ∀ t : Set V3, affGe {g x} (g '' t) = g '' (affGe {x} t))
    (x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN (g x) (g '' V) ((fun s : Set V3 => g '' s) '' E) ↔ FAN x V E := by
  constructor
  · rintro ⟨hsup, hgraph, h1, h2, h6, h7⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ⋃₀ E ⊆ V
      intro z hz
      have hz' : (g z : V3) ∈ ⋃₀ ((fun s : Set V3 => g '' s) '' E) := by
        obtain ⟨e, he, hze⟩ := hz
        exact Set.mem_sUnion.mpr ⟨g '' e, ⟨e, he, rfl⟩, Set.mem_image_of_mem _ hze⟩
      obtain ⟨v, hv, hgv⟩ := hsup hz'
      have hvz : v = z := hg hgv
      rw [← hvz]
      exact hv
    · -- Graph E
      intro e he
      obtain ⟨hf, hcard⟩ := hgraph (g '' e) ⟨e, he, rfl⟩
      have hfe : e.Finite := by
        have h1' : (g ⁻¹' (g '' e)).Finite :=
          Set.Finite.preimage (fun u _ w _ huw => hg huw) hf
        have h2' : e ⊆ g ⁻¹' (g '' e) := fun w hw =>
          Set.mem_preimage.2 (Set.mem_image_of_mem _ hw)
        exact h1'.subset h2'
      refine ⟨hfe, ?_⟩
      have himg : hf.toFinset = hfe.toFinset.image g :=
        Set.Finite.toFinset_image g hfe hf
      have hc : hfe.toFinset.card = hf.toFinset.card := by
        rw [← Finset.card_image_of_injective hfe.toFinset hg, ← himg]
      rw [hc]
      exact hcard
    · -- fan1
      have hvf : (g '' V).Finite := h1.1
      have hvf' : V.Finite := by
        have h1' : (g ⁻¹' (g '' V)).Finite :=
          Set.Finite.preimage (fun u _ w _ huw => hg huw) hvf
        have h2' : V ⊆ g ⁻¹' (g '' V) := fun w hw =>
          Set.mem_preimage.2 (Set.mem_image_of_mem _ hw)
        exact h1'.subset h2'
      refine ⟨hvf', ?_⟩
      intro hV
      apply h1.2
      exact Set.image_eq_empty.2 hV
    · -- fan2
      exact fun hV => h2 (Set.mem_image_of_mem _ hV)
    · -- fan6
      intro e he hm
      apply h6 (g '' e) ⟨e, he, rfl⟩
      have hcol : Collinear ℝ (g '' (insert x e)) := (hcoll (insert x e)).mpr hm
      rwa [Set.image_insert_eq] at hcol
    · -- fan7
      intro e1 he1 e2 he2
      have hdom : ∀ e ∈ E ∪ {s | ∃ v ∈ V, s = {v}},
          g '' e ∈ ((fun s : Set V3 => g '' s) '' E) ∪ {s | ∃ v ∈ g '' V, s = {v}} := by
        intro e he
        rcases (Set.mem_union _ _ _).mp he with he' | ⟨v, hv, rfl⟩
        · exact (Set.mem_union _ _ _).mpr (Or.inl ⟨e, he', rfl⟩)
        · rw [Set.image_singleton]
          exact (Set.mem_union _ _ _).mpr (Or.inr ⟨g v, Set.mem_image_of_mem _ hv, rfl⟩)
      have hin : (g '' e1) ∩ (g '' e2) = g '' (e1 ∩ e2) := (Set.image_inter hg).symm
      have hkey := h7 (g '' e1) (hdom e1 he1) (g '' e2) (hdom e2 he2)
      rw [haff x e1, haff x e2, ← Set.image_inter hg, hin, haff x (e1 ∩ e2)] at hkey
      exact image_eq_of_image_eq hg hkey
  · rintro ⟨hsup, hgraph, h1, h2, h6, h7⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ⋃₀ 像 ⊆ g '' V
      intro y hy
      obtain ⟨s, hs, hys⟩ := hy
      obtain ⟨e, he, rfl⟩ := hs
      obtain ⟨z, hz, hyz⟩ := hys
      have hsub : g '' e ⊆ g '' V := by
        intro w hw
        obtain ⟨u, hu, hwu⟩ := hw
        exact ⟨u, hsup (Set.mem_sUnion.mpr ⟨e, he, hu⟩), hwu⟩
      obtain ⟨v, hv, hgv⟩ := hsub (Set.mem_image_of_mem g hz)
      have hvz : v = z := hg hgv
      rw [← hyz, ← hvz]
      exact ⟨v, hv, rfl⟩
    · -- Graph (像)
      intro e' he'
      obtain ⟨e, he, rfl⟩ := he'
      obtain ⟨hf, hcard⟩ := hgraph e he
      have hfe : (g '' e).Finite := Set.Finite.image g hf
      refine ⟨hfe, ?_⟩
      rw [Set.Finite.toFinset_image g hf hfe, Finset.card_image_of_injective hf.toFinset hg]
      exact hcard
    · -- fan1 (像)
      refine ⟨Set.Finite.image g h1.1, ?_⟩
      intro hV
      apply h1.2
      exact Set.image_eq_empty.mp hV
    · -- fan2 (像)
      intro hm
      obtain ⟨v, hv, hgv⟩ := hm
      apply h2
      rw [← hg hgv]
      exact hv
    · -- fan6 (像)
      intro e' he' hm
      obtain ⟨e, he, rfl⟩ := he'
      apply h6 e he
      rw [← hcoll (insert x e), Set.image_insert_eq]
      exact hm
    · -- fan7 (像)
      intro e1' he1' e2' he2'
      have hpre1 : ∃ e : Set V3, e ∈ E ∪ {s | ∃ v ∈ V, s = {v}} ∧ g '' e = e1' := by
        rcases (Set.mem_union _ _ _).mp he1' with h | h
        · obtain ⟨e, hE, rfl'⟩ := h
          exact ⟨e, Set.mem_union_left _ hE, rfl'⟩
        · obtain ⟨v, hv, rfl'⟩ := h
          obtain ⟨v₀, hv₀, rfl''⟩ := hv
          have hem : ({v₀} : Set V3) ∈ E ∪ {s | ∃ v ∈ V, s = {v}} :=
            Set.mem_union_right _ ⟨v₀, hv₀, rfl⟩
          have heq : g '' {v₀} = e1' := by
            rw [Set.image_singleton, rfl'']
            exact rfl'.symm
          exact ⟨{v₀}, hem, heq⟩
      obtain ⟨e1, he1, rfl⟩ := hpre1
      have hpre2 : ∃ e : Set V3, e ∈ E ∪ {s | ∃ v ∈ V, s = {v}} ∧ g '' e = e2' := by
        rcases (Set.mem_union _ _ _).mp he2' with h | h
        · obtain ⟨e, hE, rfl'⟩ := h
          exact ⟨e, Set.mem_union_left _ hE, rfl'⟩
        · obtain ⟨v, hv, rfl'⟩ := h
          obtain ⟨v₀, hv₀, rfl''⟩ := hv
          have hem : ({v₀} : Set V3) ∈ E ∪ {s | ∃ v ∈ V, s = {v}} :=
            Set.mem_union_right _ ⟨v₀, hv₀, rfl⟩
          have heq : g '' {v₀} = e2' := by
            rw [Set.image_singleton, rfl'']
            exact rfl'.symm
          exact ⟨{v₀}, hem, heq⟩
      obtain ⟨e2, he2, rfl⟩ := hpre2
      have hdom1 : e1 ∈ E ∪ {s | ∃ v ∈ V, s = {v}} := by
        rcases (Set.mem_union _ _ _).mp he1 with h | ⟨v, hv, rfl⟩
        · exact (Set.mem_union _ _ _).mpr (Or.inl h)
        · exact (Set.mem_union _ _ _).mpr (Or.inr ⟨v, hv, rfl⟩)
      have hdom2 : e2 ∈ E ∪ {s | ∃ v ∈ V, s = {v}} := by
        rcases (Set.mem_union _ _ _).mp he2 with h | ⟨v, hv, rfl⟩
        · exact (Set.mem_union _ _ _).mpr (Or.inl h)
        · exact (Set.mem_union _ _ _).mpr (Or.inr ⟨v, hv, rfl⟩)
      have hin : (g '' e1) ∩ (g '' e2) = g '' (e1 ∩ e2) := (Set.image_inter hg).symm
      have hkey := h7 e1 hdom1 e2 hdom2
      rw [haff x e1, haff x e2, hin, ← Set.image_inter hg, haff x (e1 ∩ e2), hkey]

theorem FAN_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    FAN (a + x) ((fun y : V3 => a + y) '' V)
        ((fun s : Set V3 => (fun y : V3 => a + y) '' s) '' E) ↔
      FAN x V E := by
  refine FAN_image_iff (fun u v h => add_left_cancel h)
    (fun t => collinear_add_image_iff a t) (fun x' t => affGe_add_image a x' t) x V E

/-- HOL polyhedron.hl :289-297 `FAN_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
 linear f /\ (!x y. f x = f y ==> x = y)
 ==> (FAN(f x,IMAGE f V,IMAGE (IMAGE f) E) <=> FAN(x,V,E))
```

编码说明：`linear f ∧ injective` 编码为 `f : V3 →ₗ[ℝ] V3` +
`Function.Injective f`（线性假设吸收进类型）；`IMAGE (IMAGE f) E` 编码为
`(fun s => f '' s) '' E`。

证明思路：同 `FAN_TRANSLATION_EQ`，逐合取项化简；线性双射保持
`Collinear`、`affGe`（`affGe` 对线性像的等变性）与有限性/非空性。

候选已有引理：
- `FAN`、`fan1`、`fan2`、`fan6`、`fan7`、`Graph`（Kepler/Text/Fan.lean:37-56）
- `Set.image_pair`、`Function.Injective`（Mathlib）
- 缺口：`affGe`/`Collinear` 在可逆线性像下的等变引理 repo 无现成陈述 -/

theorem FAN_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (x : V3) (V : Set V3)
    (E : Set (Set V3)) (hf : Function.Injective f) :
    FAN (f x) (f '' V) ((fun s : Set V3 => f '' s) '' E) ↔ FAN x V E :=
  FAN_image_iff hf (fun t => collinear_lin_image_iff hf t)
    (fun x' t => affGe_lin_image hf x' t) x V E

/-- HOL polyhedron.hl :298-303 `BASE_POINT_FAN_TRANSLATION_EQ`

HOL 原文：
```
!a x V E.
  base_point_fan(a + x,IMAGE (\x. a + x) V,IMAGE (IMAGE (\x. a + x)) E) =
  a + base_point_fan(x,V,E)
```

编码说明（缺口）：HOL `base_point_fan (x,V,E) = x`（fan/fan.hl:67）未
移植，按定义式在两边就地展开：左边展开为 `a + x`，右边为 `a + x`，陈述
退化为点的恒等式；`V`、`E` 仅为保持 HOL 签名（无实际约束）。

证明思路：定义式展开后即 `a + x = a + x`（`rfl` 量级的平凡恒等式）。

候选已有引理：
- `base_point_fan` 定义 fan/fan.hl:67（未移植，就地展开）
- `add_self`/`rfl`（Lean 核心） -/
theorem BASE_POINT_FAN_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    a + x = a + x := rfl

/-- HOL polyhedron.hl :304-310 `BASE_POINT_FAN_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
      linear f
      ==> base_point_fan(f x,IMAGE f V,IMAGE (IMAGE f) E) =
          f(base_point_fan(x,V,E))
```

编码说明（缺口）：HOL `base_point_fan (x,V,E) = x`（fan/fan.hl:67）未
移植，按定义式在两边就地展开：左边展开为 `f x`，右边为 `f x`；HOL
`linear f` 由 `f : V3 →ₗ[ℝ] V3` 的类型吸收，陈述退化为点的恒等式；
`V`、`E` 仅为保持 HOL 签名。

证明思路：定义式展开后即 `f x = f x`（`rfl` 量级）。

候选已有引理：
- `base_point_fan` 定义 fan/fan.hl:67（未移植，就地展开）
- `rfl`（Lean 核心） -/
theorem BASE_POINT_FAN_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (x : V3) (V : Set V3)
    (E : Set (Set V3)) : f x = f x := rfl

/-- 平移下的双边像成员等价：`{a+x, a+u}` 在 `E` 的平移像中 ⟺ `{x, u} ∈ E`。 -/
private theorem pair_mem_image_add_iff (a x : V3) (E : Set (Set V3)) (u : V3) :
    ({a + x, a + u} ∈
        ((fun s : Set V3 => (fun y : V3 => a + y) '' s) '' E)) ↔ {x, u} ∈ E := by
  constructor
  · rintro ⟨e, he, hae⟩
    obtain ⟨z, hz, hzx⟩ : a + x ∈ (fun s : Set V3 => (fun y : V3 => a + y) '' s) e := by
      rw [hae]; simp
    have hx : x ∈ e := by
      rw [add_left_cancel hzx] at hz
      exact hz
    obtain ⟨z, hz, hzu⟩ : a + u ∈ (fun s : Set V3 => (fun y : V3 => a + y) '' s) e := by
      rw [hae]; simp
    have hu : u ∈ e := by
      rw [add_left_cancel hzu] at hz
      exact hz
    have hsub : e ⊆ {x, u} := by
      intro z hz
      have hmem : (a + z : V3) ∈ ({a + x, a + u} : Set V3) := by
        rw [← hae]
        exact Set.mem_image_of_mem _ hz
      rcases hmem with h | h
      · exact Or.inl (add_left_cancel h)
      · exact Or.inr (add_left_cancel h)
    have hsub' : e = {x, u} := by
      apply Set.ext
      intro z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hz
        rcases hsub hz with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact hx
        · exact hu
    rw [hsub'] at he
    exact he
  · rintro he
    refine ⟨{x, u}, he, ?_⟩
    show (fun y : V3 => a + y) '' {x, u} = {a + x, a + u}
    rw [Set.image_insert_eq, Set.image_singleton]

/-- HOL polyhedron.hl :311-317 `SET_OF_EDGE_TRANSLATION_EQ`

HOL 原文：
```
!a:real^N x V E.
      set_of_edge (a + x) (IMAGE (\x. a + x) V)
                  (IMAGE (IMAGE (\x. a + x)) E) =
      IMAGE (\x. a + x) (set_of_edge x V E)
```

编码说明：HOL `set_of_edge` ↔ `setOfEdge`（Kepler/Text/Fan.lean:62：
`{w | {v, w} ∈ E ∧ w ∈ V}`）。

证明思路：`setOfEdge` 按定义展开后，两边均为
`{w | w ∈ (a + ·) '' V ∧ {a + x, a + w} ∈ (a + ·) '' (a + ·) '' E}`-型
集合；用 `Set.mem_image`、`Set.image_image` 与加法消去
（`(a + u = a + v) ↔ u = v`）收口。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.mem_image`、`Set.image_image`、`Set.ext_iff`（Mathlib）
- `V3` 的 `add_right_cancel`（Mathlib） -/
theorem SET_OF_EDGE_TRANSLATION_EQ (a x : V3) (V : Set V3) (E : Set (Set V3)) :
    setOfEdge (a + x) ((fun y : V3 => a + y) '' V)
        ((fun s : Set V3 => (fun y : V3 => a + y) '' s) '' E) =
      (fun y : V3 => a + y) '' (setOfEdge x V E) := by
  ext w
  simp only [setOfEdge, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hedge, hV⟩
    obtain ⟨v, hvV, hvw⟩ := hV
    rw [← hvw] at hedge
    rw [pair_mem_image_add_iff a x E v] at hedge
    exact ⟨v, ⟨hedge, hvV⟩, hvw⟩
  · rintro ⟨u, ⟨huE, huV⟩, haw⟩
    rw [← haw]
    refine ⟨?_, ?_⟩
    · rw [pair_mem_image_add_iff a x E u]
      exact huE
    · exact Set.mem_image_of_mem _ huV

/-- 单射线性像下的双边像成员等价：`{f x, f u}` 在 `E` 的像中 ⟺ `{x, u} ∈ E`。 -/
private theorem pair_mem_image_lin_iff {f : V3 →ₗ[ℝ] V3} (hf : Function.Injective f)
    (x : V3) (E : Set (Set V3)) (u : V3) :
    ({f x, f u} ∈ ((fun s : Set V3 => f '' s) '' E)) ↔ {x, u} ∈ E := by
  constructor
  · rintro ⟨e, he, hae⟩
    obtain ⟨z, hz, hzx⟩ : f x ∈ (fun s : Set V3 => f '' s) e := by
      rw [hae]; simp
    have hx : x ∈ e := by
      rw [hf hzx] at hz
      exact hz
    obtain ⟨z, hz, hzu⟩ : f u ∈ (fun s : Set V3 => f '' s) e := by
      rw [hae]; simp
    have hu : u ∈ e := by
      rw [hf hzu] at hz
      exact hz
    have hsub : e ⊆ {x, u} := by
      intro z hz
      have hmem : (f z : V3) ∈ ({f x, f u} : Set V3) := by
        rw [← hae]
        exact Set.mem_image_of_mem _ hz
      rcases hmem with h | h
      · exact Or.inl (hf h)
      · exact Or.inr (hf h)
    have hsub' : e = {x, u} := by
      apply Set.ext
      intro z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hz
        rcases hsub hz with h | h
        · exact Or.inl h
        · exact Or.inr h
      · rintro (rfl | rfl)
        · exact hx
        · exact hu
    rw [hsub'] at he
    exact he
  · rintro he
    refine ⟨{x, u}, he, ?_⟩
    show (fun y : V3 => f y) '' {x, u} = {f x, f u}
    rw [Set.image_insert_eq, Set.image_singleton]

/-- HOL polyhedron.hl :318-339 `SET_OF_EDGE_LINEAR_IMAGE_EQ`

HOL 原文：
```
!f:real^M->real^N x V E.
      linear f /\ (!x y. f x = f y ==> x = y)
      ==> set_of_edge (f x) (IMAGE f V) (IMAGE (IMAGE f) E) =
          IMAGE f (set_of_edge x V E)
```

编码说明：`linear f ∧ injective` 编码为 `f : V3 →ₗ[ℝ] V3` +
`Function.Injective f`；`set_of_edge` ↔ `setOfEdge`
（Kepler/Text/Fan.lean:62）。

证明思路：`setOfEdge` 展开后用 `Set.mem_image` 拆两边；`f` 单射给出
`{f v, f w} ∈ ...` 与 `{v, w} ∈ ...` 的相互转移（`Set.mem_image` +
`map_le_map_iff`-型单射参数），其余为集合演算。

候选已有引理：
- `setOfEdge`（Kepler/Text/Fan.lean:62）
- `Set.mem_image`、`Set.image_image`、`Set.image_congr`（Mathlib）
- `LinearMap.injective` 应用场景 `Set.injOn_of_injective`-族（Mathlib） -/
theorem SET_OF_EDGE_LINEAR_IMAGE_EQ (f : V3 →ₗ[ℝ] V3) (x : V3) (V : Set V3)
    (E : Set (Set V3)) (hf : Function.Injective f) :
    setOfEdge (f x) (f '' V) ((fun s : Set V3 => f '' s) '' E) =
      f '' (setOfEdge x V E) := by
  ext w
  simp only [setOfEdge, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hedge, hV⟩
    obtain ⟨v, hvV, hvw⟩ := hV
    rw [← hvw] at hedge
    rw [pair_mem_image_lin_iff hf x E v] at hedge
    exact ⟨v, ⟨hedge, hvV⟩, hvw⟩
  · rintro ⟨v, ⟨huE, huV⟩, hvw⟩
    rw [← hvw]
    refine ⟨?_, ?_⟩
    · rw [pair_mem_image_lin_iff hf x E v]
      exact huE
    · exact Set.mem_image_of_mem _ huV

/-! ## 多面体导出扇（polyhedron.hl:342-513） -/

/-- HOL polyhedron.hl :342-513 `POLYHEDRON_FAN`

HOL 原文：
```
!p z:real^3.
    bounded p /\ polyhedron p /\ z IN interior p
    ==> FAN(z,vertices p,edges p)
```

编码说明（缺口）：HOL `polyhedron p`（polytope.ml:4385）、`vertices p`
（flyspeck_multivariate.ml:6884）、`edges p`（:6887）、`face_of`
（polytope.ml:13，开 `segment(a,b)`）均未移植，全部按定义式就地展开；
`aff_dim (segment[v,w]) = &1`（`edge_of` 条件）以段上等价条件 `v ≠ w`
编码（本 Mathlib 无仿射维数 API）；`relative_interior` 见批头说明。
因此结论为 `FAN z (Set.extremePoints ℝ p) {e | ∃ v w, e = {v, w} ∧
v ≠ w ∧ face_of 条件(内联)}`。

证明思路（HOL 六合取项）：(1) `⋃₀ E ⊆ vertices p`：`edge_of ⊆ vertices`
经 `face_of` 传递性与 `EXTREME_POINT_OF_SEGMENT`；(2) `Graph E`：边由
`v ≠ w` 保证基数 2；(3) `fan1`：`FINITE_POLYHEDRON_EXTREME_POINTS` +
`EXTREME_POINT_EXISTS_CONVEX`（紧凸集有极值点）；(4) `fan2`：
`EXTREME_POINT_NOT_IN_INTERIOR`；(5) `fan6`：设 `{x,v,w}` 共线导出
`t % v` 型内点矛盾（`FACE_OF_DISJOINT_INTERIOR` +
`POLYHEDRON_COLLINEAR_FACES`）；(6) `fan7`：内联引理（两条 `face_of` 段
要么重合要么交于端点并）+ `AFF_GE_0_CONVEX_HULL_ALT` 与
`POLYHEDRON_COLLINEAR_FACES`。

候选已有引理：
- `FAN`、`fan1`、`fan2`、`fan6`、`fan7`、`Graph`（Kepler/Text/Fan.lean:37-56）
- `Set.extremePoints`、`mem_extremePoints`（Mathlib Analysis/Convex/Extreme.lean:68,133）
- `segment`、`openSegment`、`convex_segment`（Mathlib Analysis/Convex/Segment.lean）
- `IsBounded`（Mathlib Topology/Bornology/Basic.lean:99；HOL `bounded`）、
  `interior`、`interior_subset`（Mathlib）
- 缺口：`POLYHEDRON_COLLINEAR_FACES`、`EXTREME_POINT_EXISTS_CONVEX`、
  `FACE_OF_DISJOINT_INTERIOR` 等上游引理 repo 均未移植 -/
theorem POLYHEDRON_FAN {p : Set V3} {z : V3} (hb : Bornology.IsBounded p)
    (hp : ∃ f : Set (Set V3), f.Finite ∧ p = ⋂₀ f ∧
      ∀ h ∈ f, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b})
    (hz : z ∈ interior p) :
    FAN z (Set.extremePoints ℝ p)
      {e : Set V3 | ∃ v w : V3, e = {v, w} ∧ v ≠ w ∧
        segment ℝ v w ⊆ p ∧ Convex ℝ (segment ℝ v w) ∧
        ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ segment ℝ v w →
          y ∈ openSegment ℝ c d → c ∈ segment ℝ v w ∧ d ∈ segment ℝ v w} := by
  sorry

/-! ## 相对内部的凸性（polyhedron.hl:514-569，Truong 添加部分） -/

/-- 半空间（点积形式）的凸性。 -/
private theorem convex_halfspace_dot (a : V3) (b : ℝ) : Convex ℝ {y : V3 | a ⬝ᵥ y ≤ b} := by
  intro u hu v hv c1 c2 hc1 hc2 hsum
  simp only [Set.mem_setOf_eq] at hu hv ⊢
  show a.ofLp ⬝ᵥ (c1 • u.ofLp + c2 • v.ofLp) ≤ b
  have hsplit : a.ofLp ⬝ᵥ (c1 • u.ofLp + c2 • v.ofLp) = c1 * (a.ofLp ⬝ᵥ u.ofLp) + c2 * (a.ofLp ⬝ᵥ v.ofLp) := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp
  rw [hsplit]
  have h1 : c1 * (a.ofLp ⬝ᵥ u.ofLp) ≤ c1 * b := mul_le_mul_of_nonneg_left hu hc1
  have h2 : c2 * (a.ofLp ⬝ᵥ v.ofLp) ≤ c2 * b := mul_le_mul_of_nonneg_left hv hc2
  have key : c1 * b + c2 * b = b := by rw [← add_mul, hsum, one_mul]
  have h3 : c1 * (a.ofLp ⬝ᵥ u.ofLp) + c2 * (a.ofLp ⬝ᵥ v.ofLp) ≤ c1 * b + c2 * b :=
    add_le_add h1 h2
  rw [key] at h3
  exact h3

/-- 凸集的相对内部（内蕴内部）是凸的。 -/
private theorem convex_intrinsicInterior {s : Set V3} (hs : Convex ℝ s) :
    Convex ℝ (intrinsicInterior ℝ s) := by
  rcases s.eq_empty_or_nonempty with h | h
  · subst h
    simp only [intrinsicInterior_empty]
    exact convex_empty
  · -- 阻塞：需证明 ↥(affineSpan ℝ s) 上的 interior (subtype ⁻¹' s) 的凸性。
    -- ↥(affineSpan ℝ s) 只是 torsor（非 module），`Convex.affine_preimage` 的
    -- source-instance 无法合成；Mathlib 自身 `Set.Nonempty.intrinsicInterior`
    -- 用 `AffineIsometryEquiv.constVSub` 做了 V3-传输，但仅得到非空性。
    sorry


/-- HOL polyhedron.hl :514-516 `CONVEX_RELATIVE_INTERIOR`

HOL 原文：
```
!p:real^3->bool. polyhedron p ==> convex (relative_interior p)
```

编码说明（缺口）：HOL `polyhedron p` 就地展开（见批头）；HOL
`relative_interior p` ↔ `intrinsicInterior ℝ p`
（Mathlib Analysis/Convex/Intrinsic.lean:61）。

证明思路（HOL）：由 `POLYHEDRON_INTER_AFFINE_MINIMAL` 取 `p =
affine hull p ∩ ⋂ f`，用 `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT` 得
`relative_interior p = p ∩ {x | ∀ h ∈ f, a h ⬝ x < b h}`，再
`CONVEX_INTER`（`p` 凸：`POLYHEDRON_EQ_FINITE_FACES`）+ `CONVEX_INTERS`
+ `LEMMA`（本文件）+ `CONVEX_HALFSPACE_LT`。

候选已有引理：
- `intrinsicInterior ℝ`（Mathlib Analysis/Convex/Intrinsic.lean:61）
- `Convex.inter`、`convex_iInter`-型、`Convex.halfspace_lt`（Mathlib：
  `convex_halfspace_lt`）
- `LEMMA`（本文件 PolyAuto3.lean）
- 缺口：`RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT`、
  `POLYHEDRON_INTER_AFFINE_MINIMAL` 未移植 -/
theorem CONVEX_RELATIVE_INTERIOR {p : Set V3}
    (hp : ∃ f : Set (Set V3), f.Finite ∧ p = ⋂₀ f ∧
      ∀ h ∈ f, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b}) :
    Convex ℝ (intrinsicInterior ℝ p) := by
  obtain ⟨f, -, hp0, hdesc⟩ := hp
  subst hp0
  refine convex_intrinsicInterior (convex_sInter ?_)
  intro t ht
  obtain ⟨a, b, -, rfl⟩ := hdesc t ht
  exact convex_halfspace_dot a b

/-- HOL polyhedron.hl :517-560 `LEMMA`

HOL 原文：
```
!f:(real^3->bool)->bool (a:(real^3->bool)->real^3) (b:(real^3->bool)->real).
{x | !h. h IN f ==> a h dot x < b h} = INTERS{{x | a h dot x < b h}| h IN f}
```

（本批独占 HOL 名 `LEMMA`；后一批的同名 `LEMMA`（polyhedron.hl:858）
届时改名，非本批职责。）

编码说明：纯集合论恒等式；`INTERS {g h | h ∈ f}` ↔ `⋂ h ∈ f, g h`
（repo 约定）；`dot` ↔ `⬝ᵥ`。

证明思路：`Set.ext_iff` + `mem_iInter`：左边逐点语句
`x ∈ {x | ∀ h ∈ f, ...}` 与右边逐 h 交成员互推（每步取 `h` 作见证，
`⟨h, hf, rfl⟩` 型收口）。

候选已有引理：
- `Set.ext_iff`、`Set.mem_iInter`、`Set.mem_setOf_eq`（Mathlib） -/
theorem LEMMA (f : Set (Set V3)) (a : Set V3 → V3) (b : Set V3 → ℝ) :
    {x : V3 | ∀ h : Set V3, h ∈ f → a h ⬝ᵥ x < b h} =
      ⋂ h ∈ f, {x : V3 | a h ⬝ᵥ x < b h} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter]

/-- HOL polyhedron.hl :561-566 `CONVEX_RELATIVE_INTERIOR_FACE`

HOL 原文：
```
!p f:(real^3->bool). polyhedron p /\ f face_of p
==> convex (relative_interior f)
```

编码说明（缺口）：HOL `polyhedron p` 与 `face_of`（polytope.ml:13，
开 `segment(a,b)`）均未移植，按定义式就地展开；`relative_interior` ↔
`intrinsicInterior ℝ p`。

证明思路（HOL）：`FACE_OF_POLYHEDRON_POLYHEDRON`（面的多项式性，HOL
polytope.ml:5278）把 `face_of p` 转成 `polyhedron f`，再用本文件
`CONVEX_RELATIVE_INTERIOR`。

候选已有引理：
- `CONVEX_RELATIVE_INTERIOR`（本文件 PolyAuto3.lean）
- `intrinsicInterior ℝ`（Mathlib Analysis/Convex/Intrinsic.lean:61）
- 缺口：`FACE_OF_POLYHEDRON_POLYHEDRON` 未移植 -/
theorem CONVEX_RELATIVE_INTERIOR_FACE {p f : Set V3}
    (hp : ∃ g : Set (Set V3), g.Finite ∧ p = ⋂₀ g ∧
      ∀ h ∈ g, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b})
    (hf : f ⊆ p ∧ Convex ℝ f ∧
      ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ f →
        y ∈ openSegment ℝ c d → c ∈ f ∧ d ∈ f) :
    Convex ℝ (intrinsicInterior ℝ f) :=
  convex_intrinsicInterior hf.2.1

end Kepler.Text
