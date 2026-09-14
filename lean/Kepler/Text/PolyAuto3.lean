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

import Kepler.Text.Polytope
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

/-! ### POLYHEDRON_FAN 组件（本批就地证明的辅助引理） -/

/-- `dotProduct` 关于第二个变量的连续性。 -/
private theorem continuous_dot_right (a : V3) : Continuous (fun y : V3 => a ⬝ᵥ y) := by
  fun_prop

/-- 闭半空间（点积形式）。 -/
private theorem isClosed_halfspace_dot (a : V3) (b : ℝ) : IsClosed {y : V3 | a ⬝ᵥ y ≤ b} :=
  isClosed_le (continuous_dot_right a) continuous_const

/-- 有界多面体（有限个闭半空间之交）有极值点（HOL `EXTREME_POINT_EXISTS_CONVEX`
的替代路线：闭 + 有界 ⇒ 紧 + Mathlib Krein–Milman
`IsCompact.extremePoints_nonempty`）。 -/
private theorem extremePoints_nonempty_of_polyhedron {p : Set V3}
    (hp : ∃ f : Set (Set V3), f.Finite ∧ p = ⋂₀ f ∧
      ∀ h ∈ f, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b})
    (hbd : Bornology.IsBounded p) {z : V3} (hzp : z ∈ p) :
    (Set.extremePoints ℝ p).Nonempty := by
  obtain ⟨f, -, hp0, hdesc⟩ := hp
  have hclosed : IsClosed p := by
    rw [hp0]
    refine isClosed_sInter fun h hh => ?_
    obtain ⟨a, b, -, rfl⟩ := hdesc h hh
    exact isClosed_halfspace_dot a b
  exact (Metric.isCompact_of_isClosed_isBounded hclosed hbd).extremePoints_nonempty ⟨z, hzp⟩

/-- 两点集的 Graph 计数（`{v,w}` 有限且基数 2，`v ≠ w`）。 -/
private theorem finite_pair_card_two {v w : V3} (hvw : v ≠ w) :
    ∃ h : ({v, w} : Set V3).Finite, h.toFinset.card = 2 := by
  have hfin : ({v, w} : Set V3).Finite := (Set.finite_singleton w).insert v
  refine ⟨hfin, ?_⟩
  rw [← Set.ncard_eq_toFinset_card ({v, w} : Set V3) hfin]
  exact Set.ncard_pair hvw

/-- 边 `[v,w]`（内联 face_of 条件）的第一端点 `v` 是 `p` 的极值点
（HOL `EXTREME_POINT_OF_SEGMENT`+`FACE_OF_TRANS` 的内联一步）。 -/
private theorem edgeFirstEndpoint_extreme {p : Set V3} {v w : V3} (hvw : v ≠ w)
    (hsub : segment ℝ v w ⊆ p)
    (hface : ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ segment ℝ v w →
      y ∈ openSegment ℝ c d → c ∈ segment ℝ v w ∧ d ∈ segment ℝ v w) :
    v ∈ Set.extremePoints ℝ p := by
  have hvp : v ∈ p := hsub (left_mem_segment ℝ v w)
  rw [mem_extremePoints]
  refine ⟨hvp, ?_⟩
  intro c hc d hd hxy
  obtain ⟨hcf, hdf⟩ := hface c d v hc hd (left_mem_segment ℝ v w) hxy
  obtain ⟨α, β, hα, hβ, hαβ, hvdef⟩ := hxy
  obtain ⟨t', s', ht', hs', ht's', hcdef⟩ := hcf
  obtain ⟨t'', s'', ht'', hs'', ht''s'', hddef⟩ := hdf
  have hα1 : α = 1 - β := by linarith
  have ht'1 : t' = 1 - s' := by linarith
  have ht''1 : t'' = 1 - s'' := by linarith
  have hcv : c = v + s' • (w - v) := by rw [← hcdef, ht'1]; module
  have hdd : d = v + s'' • (w - v) := by rw [← hddef, ht''1]; module
  rw [hcv, hdd, hα1] at hvdef
  -- hvdef : (1 - β) • (v + s' • (w - v)) + β • (v + s'' • (w - v)) = v
  have hβpos : (0:ℝ) < 1 - β := by rw [← hα1]; exact hα
  have hvf : (s' + β * (s'' - s')) • (w - v) = 0 := by
    linear_combination (norm := module) hvdef
  have hβ0 : s' + β * (s'' - s') = 0 := by
    rcases smul_eq_zero.mp hvf with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hvw
  have hβform : s' + β * (s'' - s') = (1 - β) * s' + β * s'' := by ring
  rw [hβform] at hβ0
  have hterm1 : (0:ℝ) ≤ (1 - β) * s' := mul_nonneg hβpos.le hs'
  have hterm2 : (0:ℝ) ≤ β * s'' := mul_nonneg hβ.le hs''
  have h1t : (1 - β) * s' = 0 := by
    have hsplit : (1 - β) * s' = -(β * s'') := by linarith
    linarith
  have hs'0 : s' = 0 := by
    rcases mul_eq_zero.mp h1t with h | h
    · exact absurd h (ne_of_gt hβpos)
    · exact h
  have hβ0' : β * s'' = 0 := by rw [hs'0, mul_zero, zero_add] at hβ0; exact hβ0
  have hs''0 : s'' = 0 := by
    rcases mul_eq_zero.mp hβ0' with h | h
    · exact absurd h hβ.ne'
    · exact h
  rw [hs'0] at hcv
  rw [hs''0] at hdd
  rw [zero_smul, add_zero] at hcv hdd
  exact ⟨hcv, hdd⟩

/-- 内点属于面则面吞整个 `p`（HOL `FACE_OF_DISJOINT_INTERIOR` 的内联核心；
fan6/fan7 的关键共享件）。 -/
private theorem face_eq_of_mem_interior {p f : Set V3}
    (hsub : f ⊆ p)
    (hface : ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ f →
      y ∈ openSegment ℝ c d → c ∈ f ∧ d ∈ f)
    {x : V3} (hxf : x ∈ f) (hxi : x ∈ interior p) : p ⊆ f := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hxi
  have hball' : Metric.ball x ε ⊆ p := fun y hy => interior_subset (hball hy)
  intro a ha
  rcases eq_or_ne a x with rfl | hax
  · exact hxf
  have hdne : x - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hax)
  have hune : ‖x - a‖ ≠ 0 := fun h => hdne (norm_eq_zero.mp h)
  set t : ℝ := ε / 2 / ‖x - a‖ with htdef
  have hnormpos : (0:ℝ) < ‖x - a‖ := lt_of_le_of_ne (norm_nonneg (x - a)) (Ne.symm hune)
  have htp : 0 < t := by rw [htdef]; exact div_pos (by linarith) hnormpos
  have htnorm : ‖t‖ = t := by
    rw [htdef, Real.norm_eq_abs, abs_of_pos htp]
  have hdistx : dist (x + t • (x - a)) x = ε / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, htnorm, htdef]
    field_simp
  have hx'mem : x + t • (x - a) ∈ p := hball' (by
    rw [Metric.mem_ball, hdistx]
    linarith)
  have htpos : (0:ℝ) < 1 + t := by linarith
  have htne : (1:ℝ) + t ≠ 0 := ne_of_gt htpos
  have hApos : (0:ℝ) < 1 / (1 + t) := div_pos one_pos htpos
  have hBpos : (0:ℝ) < t / (1 + t) := div_pos htp htpos
  have hA1 : (1/(1+t)) * (1 + t) = 1 := div_mul_cancel₀ _ htne
  have hAT : (1/(1+t)) * t = t / (1 + t) := by field_simp
  have hsum : (1/(1+t)) + (t/(1+t)) = 1 := by rw [← add_div, div_self htne]
  have hmid : x = (1/(1+t)) • (x + t • (x - a)) + (t/(1+t)) • a := by
    calc x = ((1/(1+t)) + (t/(1+t))) • x := by rw [hsum, one_smul]
      _ = (1/(1+t)) • x + (t/(1+t)) • x := add_smul _ _ x
      _ = (1/(1+t)) • x + (t/(1+t)) • (x - a) + (t/(1+t)) • a := by module
      _ = (1/(1+t)) • (x + t • (x - a)) + (t/(1+t)) • a := by
          rw [smul_add, smul_smul, hAT]
  have hopen : x ∈ openSegment ℝ (x + t • (x - a)) a :=
    ⟨1/(1+t), t/(1+t), hApos, hBpos, hsum, hmid.symm⟩
  obtain ⟨-, haf⟩ := hface (x + t • (x - a)) a x hx'mem ha hxf hopen
  exact haf

/-- 内点不是极值点（HOL `EXTREME_POINT_NOT_IN_INTERIOR`；fan2 的内容）。 -/
private theorem interior_not_extremePoint {p : Set V3} {z : V3} (hz : z ∈ interior p) :
    z ∉ Set.extremePoints ℝ p := by
  intro hze
  obtain ⟨hzp, hze'⟩ := mem_extremePoints.mp hze
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  have hball' : Metric.ball z ε ⊆ p := fun y hy => interior_subset (hball hy)
  obtain ⟨w1, w2, hw⟩ := exists_pair_ne (α := V3)
  have hw0 : w1 - w2 ≠ 0 := sub_ne_zero.mpr hw
  have hwn : ‖w1 - w2‖ ≠ 0 := fun h => hw0 (norm_eq_zero.mp h)
  set t : ℝ := ε / (2 * ‖w1 - w2‖) with htdef
  have htp : 0 < t := by
    rw [htdef]
    exact div_pos hε (by positivity)
  have htnorm : ‖t‖ = t := by
    rw [htdef, Real.norm_eq_abs, abs_of_pos htp]
  have htw : ‖t • (w1 - w2)‖ = ε / 2 := by
    rw [norm_smul, htnorm, htdef]
    field_simp
  have hz1 : z + t • (w1 - w2) ∈ p := hball' (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, htw]
    linarith)
  have hsub2 : (z - t • (w1 - w2)) - z = -(t • (w1 - w2)) := by module
  have hz2 : z - t • (w1 - w2) ∈ p := hball' (by
    rw [Metric.mem_ball, dist_eq_norm, hsub2, norm_neg, htw]
    linarith)
  have hmid : (1/2 : ℝ) • (z + t • (w1 - w2)) + (1/2 : ℝ) • (z - t • (w1 - w2)) = z := by
    module
  have hopen : z ∈ openSegment ℝ (z + t • (w1 - w2)) (z - t • (w1 - w2)) :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, hmid⟩
  obtain ⟨he1, he2⟩ := hze' (z + t • (w1 - w2)) hz1 (z - t • (w1 - w2)) hz2 hopen
  have hteq : t • (w1 - w2) = 0 := by
    have h := congrArg (fun q : V3 => q - z) he1
    rw [add_sub_cancel_left, sub_self] at h
    exact h
  rcases smul_eq_zero.mp hteq with h | h
  · exact absurd h htp.ne'
  · exact absurd h hw0

/-! ### POLYHEDRON_FAN 基础桥件（Polytope 引理 + z-平移 + 共线参数化） -/

/-- 平移预像 `(u ↦ z + u) ⁻¹' ·` 保持多面体性（半空间平移后仍为半空间）。 -/
private theorem polyhedron_addLeft_preimage {z : V3} {p : Set V3} (hp : polyhedron p) :
    polyhedron ((fun u : V3 => z + u) ⁻¹' p) := by
  obtain ⟨F, hFfin, hp0, hdesc⟩ := hp
  refine ⟨(fun h : Set V3 => (fun u : V3 => z + u) ⁻¹' h) '' F, hFfin.image _, ?_, ?_⟩
  · subst hp0
    ext u
    simp only [Set.mem_preimage, Set.mem_sInter, Set.mem_image]
    constructor
    · intro h G hG
      obtain ⟨h', h'F, rfl⟩ := hG
      exact h h' h'F
    · intro h h' h'F
      exact h _ ⟨h', h'F, rfl⟩
  · rintro g ⟨h, hF, rfl⟩
    obtain ⟨a, b, ha0, rfl⟩ := hdesc h hF
    refine ⟨a, b - a ⬝ᵥ z, ha0, ?_⟩
    ext u
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor <;> intro hle
    · have hsplit : a.ofLp ⬝ᵥ (z + u).ofLp = a.ofLp ⬝ᵥ z.ofLp + a.ofLp ⬝ᵥ u.ofLp := by
        show a.ofLp ⬝ᵥ (z.ofLp + u.ofLp) = _
        rw [dotProduct_add]
      rw [hsplit] at hle
      linarith
    · have hsplit : a.ofLp ⬝ᵥ (z + u).ofLp = a.ofLp ⬝ᵥ z.ofLp + a.ofLp ⬝ᵥ u.ofLp := by
        show a.ofLp ⬝ᵥ (z.ofLp + u.ofLp) = _
        rw [dotProduct_add]
      rw [hsplit]
      linarith

/-- 差相等的两点相等。 -/
private theorem eq_of_sub_eq_right {x y z : V3} (h : x - z = y - z) : x = y := by
  linear_combination (norm := module) h

/-- 有内点的集合仿射维数为满维 3。 -/
private theorem affDim_eq_three_of_mem_interior {s : Set V3} (h : (interior s).Nonempty) :
    affDim s = 3 := by
  have hne : s ≠ ∅ := Set.nonempty_iff_ne_empty.mp (h.mono interior_subset)
  have h1 : affineSpan ℝ (interior s) = ⊤ := isOpen_interior.affineSpan_eq_top h
  have h2 : affineSpan ℝ s = ⊤ := by
    refine top_unique ?_
    rw [← h1]
    exact affineSpan_mono ℝ interior_subset
  have h3 : Module.finrank ℝ (⊤ : Submodule ℝ V3) = 3 := by
    rw [finrank_top, finrank_euclideanSpace_fin]
  rw [affDim, if_neg hne, ← direction_affineSpan, h2, AffineSubspace.direction_top, h3]
  norm_num

/-- 三点 `{z, v, w}` 共线（`z` 与 `v`、`w` 均不重合）给出非零参数化
`w - z = t • (v - z)`。 -/
private theorem exists_smul_of_collinear_insert {z v w : V3}
    (hcol : Collinear ℝ (insert z {v, w})) (hvz : v ≠ z) (hwz : w ≠ z) :
    ∃ t : ℝ, t ≠ 0 ∧ w - z = t • (v - z) := by
  rw [collinear_iff_of_mem (Set.mem_insert z {v, w})] at hcol
  obtain ⟨u, hu⟩ := hcol
  obtain ⟨a, ha⟩ := hu v (Set.mem_insert_of_mem z (Set.mem_insert v {w}))
  obtain ⟨b, hb⟩ := hu w (Set.mem_insert_of_mem z (Set.mem_insert_of_mem v
    (Set.mem_singleton w)))
  simp only [vadd_eq_add] at ha hb
  have ha0 : a ≠ 0 := by
    intro h
    exact hvz (by rw [ha, h, zero_smul, zero_add])
  have hb0 : b ≠ 0 := by
    intro h
    exact hwz (by rw [hb, h, zero_smul, zero_add])
  refine ⟨b / a, div_ne_zero hb0 ha0, ?_⟩
  have hvu : v - z = a • u := by rw [ha]; module
  have hwu : w - z = b • u := by rw [hb]; module
  rw [hvu, smul_smul]
  have hkey : b / a * a = b := div_mul_cancel₀ _ ha0
  rw [hkey]
  exact hwu

/-- `FaceOf` 在平移预像 `u ↦ z + u` 下保持。 -/
private theorem faceOf_addLeft_preimage {z : V3} {s t : Set V3} (h : FaceOf s t) :
    FaceOf ((fun u : V3 => z + u) ⁻¹' s) ((fun u : V3 => z + u) ⁻¹' t) := by
  refine ⟨Set.preimage_mono h.1, h.2.1.translate_preimage_right z, ?_⟩
  rintro a b x ha hb hx hseg
  simp only [Set.mem_preimage] at ha hb hx ⊢
  exact h.2.2 (z + a) (z + b) (z + x) ha hb hx ((mem_openSegment_translate ℝ z).mpr hseg)

/-- 平移预像下的闭段恒等式。 -/
private theorem segment_addLeft_preimage (z v w : V3) :
    (fun u : V3 => z + u) ⁻¹' (segment ℝ v w) = segment ℝ (v - z) (w - z) := by
  have h := segment_translate_preimage (𝕜 := ℝ) z (v - z) (w - z)
  rwa [show z + (v - z) = v from by module, show z + (w - z) = w from by module] at h

/-- 闭段成员的平移像仍是（平移后）闭段的成员。 -/
private theorem mem_segment_sub_of_mem {a b x z : V3} (h : x ∈ segment ℝ a b) :
    x - z ∈ segment ℝ (a - z) (b - z) := by
  rw [← mem_segment_translate ℝ z, show z + (x - z) = x from by module,
    show z + (a - z) = a from by module, show z + (b - z) = b from by module]
  exact h

/-! ### 相对内部配件与两边-面相交引理（HOL POLYHEDRON_FAN 内部引理） -/

/-- Mathlib TODO 引理（Analysis/Convex/Intrinsic.lean 文件头 TODO）：`x ∈ s`、
`y ∈ rint s` 时开段 `(x, y) ⊆ rint s`。 -/
private theorem openSegment_subset_rinterior {s : Set V3} (hs : Convex ℝ s) {x y z : V3}
    (hx : x ∈ s) (hy : y ∈ intrinsicInterior ℝ s) (hz : z ∈ openSegment ℝ x y) :
    z ∈ intrinsicInterior ℝ s := by
  obtain ⟨hys, ε, hε, hball⟩ := mem_rint_iff.mp hy
  obtain ⟨m, n, hm, hn, hmn, hzdef⟩ := hz
  have hzs : z ∈ s := hzdef.symm ▸ hs hx hys hm.le hn.le hmn
  refine mem_rint_iff.mpr ⟨hzs, ε * n, by positivity, ?_⟩
  rintro w ⟨hwb, hwaff⟩
  have hn0 : n ≠ 0 := hn.ne'
  have hzaff : z ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hzs
  have hyaff : y ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hys
  have hy' : y + n⁻¹ • (w - z) ∈ (affineSpan ℝ s : Set V3) := by
    have hd1 : (w - z) ∈ (affineSpan ℝ s).direction :=
      AffineSubspace.vsub_mem_direction hwaff hzaff
    have hd2 : n⁻¹ • (w - z) ∈ (affineSpan ℝ s).direction := Submodule.smul_mem _ _ hd1
    rw [add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction hd2 hyaff
  have hyn : dist (y + n⁻¹ • (w - z)) y < ε := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < n⁻¹)]
    have hwn : ‖w - z‖ < ε * n := by rw [Metric.mem_ball, dist_eq_norm] at hwb; exact hwb
    calc n⁻¹ * ‖w - z‖ < n⁻¹ * (ε * n) := mul_lt_mul_of_pos_left hwn (by positivity)
      _ = n⁻¹ * n * ε := by rw [mul_comm ε n]; ring
      _ = ε := by rw [inv_mul_cancel₀ hn0, one_mul]
  have hy'mem : y + n⁻¹ • (w - z) ∈ s := hball ⟨hyn, hy'⟩
  have h1 : n • (y + n⁻¹ • (w - z)) = n • y + (w - z) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  have hmem : m • x + n • (y + n⁻¹ • (w - z)) ∈ s := hs hx hy'mem hm.le hn.le hmn
  rw [h1, ← add_assoc, hzdef, show z + (w - z) = w from by module] at hmem
  exact hmem


/-- 开段含于闭段的相对内部。 -/
private theorem openSegment_subset_rinterior_segment {a b y : V3}
    (hy : y ∈ openSegment ℝ a b) : y ∈ intrinsicInterior ℝ (segment ℝ a b) := by
  have hcv : Convex ℝ (segment ℝ a b) := convex_segment a b
  obtain ⟨y₀, hy₀⟩ := (Set.nonempty_of_mem (left_mem_segment ℝ a b)).intrinsicInterior hcv
  have hy₀s : y₀ ∈ segment ℝ a b := intrinsicInterior_subset hy₀
  obtain ⟨α, β, hα, hβ, hαβ, hy₀def⟩ := hy₀s
  obtain ⟨m, n, hm, hn, hmn, hydef⟩ := hy
  rcases lt_trichotomy n β with hlt | heq | hgt
  · have hβpos : (0:ℝ) < β := lt_of_le_of_lt hn.le hlt
    have hwit : y ∈ openSegment ℝ a y₀ := by
      refine ⟨1 - n / β, n / β, ?_, div_pos hn hβpos, ?_, ?_⟩
      · rw [sub_pos]; exact (div_lt_one hβpos).mpr hlt
      · ring
      · rw [← hy₀def, ← hydef, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]
        have e1 : (1 - n / β) + n / β * α = m := by
          rw [show α = 1 - β from by linarith, show m = 1 - n from by linarith]
          field_simp
          ring
        have e2 : n / β * β = n := div_mul_cancel₀ _ hβpos.ne'
        rw [e1, e2]
    exact openSegment_subset_rinterior hcv (left_mem_segment ℝ a b) hy₀ hwit
  · have hmn1 : m = α := by linarith
    rw [heq, hmn1] at hydef
    rw [← hydef, hy₀def]
    exact hy₀
  · have hαpos : (0:ℝ) < α := by linarith
    have hαm : m < α := by linarith
    have hwit : y ∈ openSegment ℝ y₀ b := by
      refine ⟨m / α, 1 - m / α, div_pos hm hαpos, ?_, ?_, ?_⟩
      · rw [sub_pos]; exact (div_lt_one hαpos).mpr hαm
      · ring
      · rw [← hy₀def, ← hydef, smul_add, smul_smul, smul_smul, add_assoc]
        have hmrg : (m / α * β) • b + (1 - m / α) • b
            = (m / α * β + (1 - m / α)) • b := by
          rw [← add_smul]
        rw [hmrg]
        have e1 : m / α * β + (1 - m / α) = n := by
          rw [show β = 1 - α from by linarith, show n = 1 - m from by linarith]
          field_simp
          ring
        have e2 : m / α * α = m := div_mul_cancel₀ _ hαpos.ne'
        rw [e1, e2]
    exact openSegment_subset_rinterior hcv (right_mem_segment ℝ a b) hy₀
      ((openSegment_symm ℝ y₀ b) ▸ hwit)

/-- 闭段成员三分：端点或开段。 -/
private theorem segment_cases {a b y : V3} (hy : y ∈ segment ℝ a b) :
    y = a ∨ y ∈ openSegment ℝ a b ∨ y = b := by
  obtain ⟨m, n, hm, hn, hmn, hydef⟩ := hy
  rcases hn.eq_or_lt with h0 | hn'
  · left
    have hm1 : m = 1 := by linarith
    rw [← hydef, h0.symm, zero_smul, add_zero, hm1, one_smul]
  · rcases hm.eq_or_lt with h1 | hm'
    · right
      right
      have hn1 : n = 1 := by linarith
      rw [← hydef, ← h1, zero_smul, zero_add, hn1, one_smul]
    · exact Or.inr (Or.inl ⟨m, n, hm', hn', hmn, hydef⟩)

/-- 二点集相等的包含判据。 -/
private theorem pair_eq_of_subset {a b c d : V3} (h1 : a ≠ b) (h2 : c ≠ d)
    (hsub : (({c, d} : Set V3) ⊆ ({a, b} : Set V3))) : ({a, b} : Set V3) = {c, d} := by
  have hc : c ∈ ({a, b} : Set V3) := hsub (Set.mem_insert c {d})
  have hd : d ∈ ({a, b} : Set V3) := hsub (Set.mem_insert_of_mem c (Set.mem_singleton d))
  rcases Set.mem_insert_iff.mp hc with hce | hce
  · rcases Set.mem_insert_iff.mp hd with hde | hde
    · exact absurd (hde.trans hce.symm) h2.symm
    · rw [← hce, ← hde]
  · rcases Set.mem_insert_iff.mp hd with hde | hde
    · rw [← hce, ← hde]
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    · exact absurd (hce.trans hde.symm) h2

/-- 两条边-面（端点互异的段面）要么端点集重合，要么两段之交互于端点集之交
（HOL POLYHEDRON_FAN 内部引理，polyhedron.hl:346-365）。 -/
private theorem segment_face_inter_eq {p : Set V3} {a b c d : V3} (hab : a ≠ b) (hcd : c ≠ d)
    (h1 : FaceOf (segment ℝ a b) p) (h2 : FaceOf (segment ℝ c d) p) :
    ({a, b} : Set V3) = ({c, d} : Set V3) ∨
      segment ℝ a b ∩ segment ℝ c d = ({a, b} : Set V3) ∩ ({c, d} : Set V3) := by
  have hr1 : openSegment ℝ a b ⊆ intrinsicInterior ℝ (segment ℝ a b) :=
    fun y hy => openSegment_subset_rinterior_segment hy
  have hr2 : openSegment ℝ c d ⊆ intrinsicInterior ℝ (segment ℝ c d) :=
    fun y hy => openSegment_subset_rinterior_segment hy
  -- 右向包含在「双相对内部皆避开」情形下成立；先给出四点组合的⊇方向
  have hsup : ∀ y : V3, y ∈ ({a, b} : Set V3) ∩ ({c, d} : Set V3) →
      y ∈ segment ℝ a b ∩ segment ℝ c d := by
    rintro y ⟨hy1, hy2⟩
    rcases Set.mem_insert_iff.mp hy1 with hya | hyb
    · rcases Set.mem_insert_iff.mp hy2 with hyc | hyd
      · exact ⟨by rw [hya]; exact left_mem_segment ℝ a b,
          by rw [hyc]; exact left_mem_segment ℝ c d⟩
      · exact ⟨by rw [hya]; exact left_mem_segment ℝ a b,
          by rw [hyd]; exact right_mem_segment ℝ c d⟩
    · rcases Set.mem_insert_iff.mp hy2 with hyc | hyd
      · exact ⟨by rw [hyb]; exact right_mem_segment ℝ a b,
          by rw [hyc]; exact left_mem_segment ℝ c d⟩
      · exact ⟨by rw [hyb]; exact right_mem_segment ℝ a b,
          by rw [hyd]; exact right_mem_segment ℝ c d⟩
  rcases Classical.em (Disjoint (segment ℝ c d) (intrinsicInterior ℝ (segment ℝ a b))) with
    hd1 | hd1
  · rcases Classical.em (Disjoint (segment ℝ a b) (intrinsicInterior ℝ (segment ℝ c d))) with
      hd2 | hd2
    · -- 双相对内部皆不交：两段之交互于端点集之交
      refine Or.inr (Set.ext fun y => ?_)
      constructor
      · rintro ⟨hy1, hy2⟩
        rcases segment_cases hy1 with hya | hyo | hyb
        · rw [hya] at hy1 hy2
          rw [hya]
          rcases segment_cases hy2 with hyc | hco | hyd
          · exact ⟨Or.inl rfl, by rw [hyc]; exact Or.inl rfl⟩
          · exact (Set.disjoint_left.mp hd2 hy1 (hr2 hco)).elim
          · exact ⟨Or.inl rfl, by rw [hyd]; exact Or.inr rfl⟩
        · exact (Set.disjoint_left.mp hd1 hy2 (hr1 hyo)).elim
        · rw [hyb] at hy1 hy2
          rw [hyb]
          rcases segment_cases hy2 with hyc | hco | hyd
          · exact ⟨Or.inr rfl, by rw [hyc]; exact Or.inl rfl⟩
          · exact (Set.disjoint_left.mp hd2 hy1 (hr2 hco)).elim
          · exact ⟨Or.inr rfl, by rw [hyd]; exact Or.inr rfl⟩
      · exact hsup y
    · -- seg2 ⊆ seg1 且 rint seg1 避开 seg2：端点重合
      have hsub21 : segment ℝ c d ⊆ segment ℝ a b := subset_of_faceOf h1 h2.1 hd2
      have hv2 : c ∈ ({a, b} : Set V3) := by
        rcases segment_cases (hsub21 (left_mem_segment ℝ c d)) with h | hco | h
        · rw [h]; exact Set.mem_insert a {b}
        · exact (Set.disjoint_left.mp hd1 (left_mem_segment ℝ c d) (hr1 hco)).elim
        · rw [h]; exact Set.mem_insert_of_mem a (Set.mem_singleton b)
      have hv3 : d ∈ ({a, b} : Set V3) := by
        rcases segment_cases (hsub21 (right_mem_segment ℝ c d)) with h | hco | h
        · rw [h]; exact Set.mem_insert a {b}
        · exact (Set.disjoint_left.mp hd1 (right_mem_segment ℝ c d) (hr1 hco)).elim
        · rw [h]; exact Set.mem_insert_of_mem a (Set.mem_singleton b)
      refine Or.inl (pair_eq_of_subset hab hcd ?_)
      intro x hx
      rcases Set.mem_insert_iff.mp hx with hx' | hx'
      · rw [hx']; exact hv2
      · rw [hx']; exact hv3
  · -- rint seg1 遇 seg2 ⇒ seg1 ⊆ seg2
    have hsub12 : segment ℝ a b ⊆ segment ℝ c d := subset_of_faceOf h2 h1.1 hd1
    rcases Classical.em (Disjoint (segment ℝ a b) (intrinsicInterior ℝ (segment ℝ c d))) with
      hd2 | hd2
    · -- seg2 ⊆ seg1 失败方向被避开：端点重合
      have hv2 : a ∈ ({c, d} : Set V3) := by
        rcases segment_cases (hsub12 (left_mem_segment ℝ a b)) with h | hco | h
        · rw [h]; exact Set.mem_insert c {d}
        · exact (Set.disjoint_left.mp hd2 (left_mem_segment ℝ a b) (hr2 hco)).elim
        · rw [h]; exact Set.mem_insert_of_mem c (Set.mem_singleton d)
      have hv3 : b ∈ ({c, d} : Set V3) := by
        rcases segment_cases (hsub12 (right_mem_segment ℝ a b)) with h | hco | h
        · rw [h]; exact Set.mem_insert c {d}
        · exact (Set.disjoint_left.mp hd2 (right_mem_segment ℝ a b) (hr2 hco)).elim
        · rw [h]; exact Set.mem_insert_of_mem c (Set.mem_singleton d)
      refine Or.inl (pair_eq_of_subset hcd hab ?_).symm
      intro x hx
      rcases Set.mem_insert_iff.mp hx with hx' | hx'
      · rw [hx']; exact hv2
      · rw [hx']; exact hv3
    · -- 双向包含：两段相等，端点集（极值点集）相等
      have hsub21 : segment ℝ c d ⊆ segment ℝ a b := subset_of_faceOf h1 h2.1 hd2
      have hseg : segment ℝ a b = segment ℝ c d := subset_antisymm hsub12 hsub21
      have hext : Set.extremePoints ℝ (segment ℝ a b)
          = Set.extremePoints ℝ (segment ℝ c d) := by rw [hseg]
      refine Or.inl (Set.ext fun x => ?_)
      constructor
      · rintro (hxa | hxb)
        · exact (EXTREME_POINT_OF_SEGMENT c d x).mp
            (hext ▸ (EXTREME_POINT_OF_SEGMENT a b x).mpr (Or.inl hxa)) |>.elim Or.inl Or.inr
        · exact (EXTREME_POINT_OF_SEGMENT c d x).mp
            (hext ▸ (EXTREME_POINT_OF_SEGMENT a b x).mpr (Or.inr hxb)) |>.elim Or.inl Or.inr
      · rintro (hxc | hxd)
        · exact (EXTREME_POINT_OF_SEGMENT a b x).mp
            (hext.symm ▸ (EXTREME_POINT_OF_SEGMENT c d x).mpr (Or.inl hxc)) |>.elim Or.inl Or.inr
        · exact (EXTREME_POINT_OF_SEGMENT a b x).mp
            (hext.symm ▸ (EXTREME_POINT_OF_SEGMENT c d x).mpr (Or.inr hxd)) |>.elim Or.inl Or.inr

/-- 平移预像 `(u ↦ z + u) ⁻¹' p` 以 0 为内点（当 `z` 为 `p` 的内点）。 -/
private theorem zero_mem_interior_addLeft_preimage {p : Set V3} {z : V3} (hz : z ∈ interior p) :
    (0:V3) ∈ interior ((fun u : V3 => z + u) ⁻¹' p) := by
  obtain ⟨t, htp, hto, hzt⟩ := mem_interior.mp hz
  refine mem_interior.mpr ⟨(fun u : V3 => z + u) ⁻¹' t, ?_, ?_, ?_⟩
  · intro u hu
    simp only [Set.mem_preimage] at hu ⊢
    exact htp hu
  · exact hto.preimage (by fun_prop)
  · rw [Set.mem_preimage, add_zero]
    exact hzt

/-! ### 平移后的多面体（fan6/fan7 共用配置） -/

/-- `insert` 对 `∩` 的分配（无前提恒等式）。 -/
private theorem insert_inter_insert {α : Type*} (a : α) (s t : Set α) :
    insert a s ∩ insert a t = insert a (s ∩ t) := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  tauto

/-- 顶点/边集合数据包：有限性、`z` 不属于、凸包是面、凸包非全集。 -/
private theorem edge_data {p : Set V3} {z : V3} (hz : z ∈ interior p) {v w : V3} (hvw : v ≠ w)
    (hface : FaceOf (segment ℝ v w) p) :
    ({v, w} : Set V3).Finite ∧ z ∉ ({v, w} : Set V3) ∧
      FaceOf (convexHull ℝ ({v, w} : Set V3)) p ∧ convexHull ℝ ({v, w} : Set V3) ≠ p := by
  refine ⟨(Set.finite_singleton w).insert v, ?_, ?_, ?_⟩
  · intro hmem
    rcases Set.mem_insert_iff.mp hmem with h | h
    · exact interior_not_extremePoint hz
        (by rw [h]; exact (SEGMENT_FACE_OF hface).1)
    · exact interior_not_extremePoint hz
        (by rw [h]; exact (SEGMENT_FACE_OF hface).2)
  · rw [convexHull_pair]; exact hface
  · intro heq
    have h1 : affDim (segment ℝ v w) = 1 := (affDim_segment _ _).2 hvw
    rw [← convexHull_pair] at h1
    rw [heq] at h1
    rw [affDim_eq_three_of_mem_interior ⟨z, hz⟩] at h1
    norm_num at h1

/-- 顶点集合数据包（单点情形）。 -/
private theorem single_data {p : Set V3} {z : V3} (hz : z ∈ interior p) {v : V3}
    (hv : v ∈ Set.extremePoints ℝ p) :
    ({v} : Set V3).Finite ∧ z ∉ ({v} : Set V3) ∧
      FaceOf (convexHull ℝ ({v} : Set V3)) p ∧ convexHull ℝ ({v} : Set V3) ≠ p := by
  refine ⟨Set.finite_singleton v, ?_, ?_, ?_⟩
  · intro hmem
    rw [Set.mem_singleton_iff] at hmem
    exact interior_not_extremePoint hz (hmem ▸ hv)
  · rw [convexHull_singleton]; exact faceOf_sing.2 hv
  · intro heq
    have hzp : z ∈ p := interior_subset hz
    rw [← heq, convexHull_singleton] at hzp
    rw [Set.mem_singleton_iff] at hzp
    exact interior_not_extremePoint hz (hzp.symm ▸ hv)

/-- 平移预像在双射下的等集消去。 -/
private theorem eq_of_preimage_eq_addLeft {z : V3} {s t : Set V3}
    (heq : ((fun u : V3 => z + u) ⁻¹' s) = ((fun u : V3 => z + u) ⁻¹' t)) : s = t := by
  have hsurj : Function.Surjective (fun u : V3 => z + u) := fun y => ⟨y - z, by module⟩
  have h1 := congrArg (fun r : Set V3 => (fun u : V3 => z + u) '' r) heq
  rwa [Set.image_preimage_eq s hsurj, Set.image_preimage_eq t hsurj] at h1

/-- `fan7` 的核心：两条「凸包 = 面」的集合在 `z`-锥下的分配律。 -/
private theorem fan7_pair {p : Set V3} {z : V3} (hp : polyhedron p) (hz : z ∈ interior p)
    {e1 e2 : Set V3} (hfin1 : e1.Finite) (hfin2 : e2.Finite)
    (hze1 : z ∉ e1) (hze2 : z ∉ e2)
    {F1 F2 : Set V3} (hF1 : FaceOf F1 p) (hF2 : FaceOf F2 p)
    (hull1 : convexHull ℝ e1 = F1) (hull2 : convexHull ℝ e2 = F2)
    (hprop1 : F1 ≠ p) (hprop2 : F2 ≠ p)
    (hsubI : F1 ∩ F2 ⊆ convexHull ℝ (e1 ∩ e2)) :
    affGe {z} e1 ∩ affGe {z} e2 = affGe {z} (e1 ∩ e2) := by
  have hfinI : (e1 ∩ e2).Finite := hfin1.subset (Set.inter_subset_left)
  have hzeI : z ∉ e1 ∩ e2 := fun h => hze1 h.1
  rw [AFF_GE_SING_CONVEX_HULL_ALT hfin1 hze1, AFF_GE_SING_CONVEX_HULL_ALT hfin2 hze2,
    AFF_GE_SING_CONVEX_HULL_ALT hfinI hzeI, insert_inter_insert]
  refine congrArg (insert z) (Set.ext fun w => ?_)
  constructor
  · rintro ⟨⟨s, hs0, x, hx1, hxw⟩, ⟨t, ht0, y, hy2, hyw⟩⟩
    set p' : Set V3 := (fun u : V3 => z + u) ⁻¹' p with hp'def
    have hsp' : polyhedron p' := polyhedron_addLeft_preimage hp
    have h0int : (0:V3) ∈ interior p' := zero_mem_interior_addLeft_preimage hz
    have hF1' : FaceOf ((fun u : V3 => z + u) ⁻¹' F1) p' := faceOf_addLeft_preimage hF1
    have hF2' : FaceOf ((fun u : V3 => z + u) ⁻¹' F2) p' := faceOf_addLeft_preimage hF2
    have hprop1' : ((fun u : V3 => z + u) ⁻¹' F1) ≠ p' := by
      intro heq
      exact hprop1 (eq_of_preimage_eq_addLeft (by rw [heq, hp'def]))
    have hprop2' : ((fun u : V3 => z + u) ⁻¹' F2) ≠ p' := by
      intro heq
      exact hprop2 (eq_of_preimage_eq_addLeft (by rw [heq, hp'def]))
    have hx1F : x ∈ F1 := by rw [← hull1]; exact hx1
    have hy2F : y ∈ F2 := by rw [← hull2]; exact hy2
    have hxe : x - z ∈ ((fun u : V3 => z + u) ⁻¹' F1) := by
      simp only [Set.mem_preimage]
      rw [show z + (x - z) = x from by module]
      exact hx1F
    have hye : y - z ∈ ((fun u : V3 => z + u) ⁻¹' F2) := by
      simp only [Set.mem_preimage]
      rw [show z + (y - z) = y from by module]
      exact hy2F
    have heq0 : s • (x - z) = t • (y - z) := by
      linear_combination (norm := module) (hxw.symm.trans hyw)
    have hst := POLYHEDRON_COLLINEAR_FACES (P := p') (f := (fun u : V3 => z + u) ⁻¹' F1)
      (f' := (fun u : V3 => z + u) ⁻¹' F2) (p := x - z) (q := y - z) (s := s) (t := t)
      hsp' h0int hF1' hprop1' hF2' hprop2' hxe hye hs0 ht0 heq0
    rw [hst] at heq0
    have hxy2 : x = y :=
      eq_of_sub_eq_right (smul_right_injective V3 ht0.ne' heq0)
    have hxI : x ∈ convexHull ℝ (e1 ∩ e2) := by
      refine hsubI ⟨hx1F, ?_⟩
      rw [← hxy2] at hy2F
      exact hy2F
    exact ⟨s, hs0, x, hxI, hxw⟩
  · rintro ⟨s, hs0, x, hxI, hxdef⟩
    rw [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_setOf_eq]
    exact ⟨⟨s, hs0, x, convexHull_mono (Set.inter_subset_left) hxI, hxdef⟩,
      ⟨s, hs0, x, convexHull_mono (Set.inter_subset_right) hxI, hxdef⟩⟩

/-- `fan7` 组合：边 × 边。 -/
private theorem fan7_edge_edge {p : Set V3} {z : V3} (hp : polyhedron p) (hz : z ∈ interior p)
    {v1 w1 v2 w2 : V3} (hv1w1 : v1 ≠ w1) (hv2w2 : v2 ≠ w2)
    (hface1 : FaceOf (segment ℝ v1 w1) p) (hface2 : FaceOf (segment ℝ v2 w2) p) :
    affGe {z} ({v1, w1} : Set V3) ∩ affGe {z} ({v2, w2} : Set V3)
      = affGe {z} (({v1, w1} : Set V3) ∩ ({v2, w2} : Set V3)) := by
  have d1 := edge_data hz hv1w1 hface1
  have d2 := edge_data hz hv2w2 hface2
  obtain ⟨hfin1, hze1, hF1, hprop1⟩ := d1
  obtain ⟨hfin2, hze2, hF2, hprop2⟩ := d2
  refine fan7_pair hp hz hfin1 hfin2 hze1 hze2 hF1 hF2 rfl rfl hprop1 hprop2 ?_
  rw [convexHull_pair, convexHull_pair]
  rcases segment_face_inter_eq hv1w1 hv2w2 hface1 hface2 with heq | heq
  · intro x hx
    have hxx : convexHull ℝ (({v1, w1} : Set V3) ∩ ({v2, w2} : Set V3))
= segment ℝ v2 w2 := by
      rw [heq, Set.inter_self, convexHull_pair]
    rw [hxx]; exact hx.2
  · intro x hx
    rw [heq] at hx
    exact subset_convexHull ℝ (({v1, w1} : Set V3) ∩ ({v2, w2} : Set V3)) hx

/-- `fan7` 组合：边 × 单点。 -/
private theorem fan7_edge_single {p : Set V3} {z : V3} (hp : polyhedron p) (hz : z ∈ interior p)
    {v1 w1 v2 : V3} (hv1w1 : v1 ≠ w1) (hface1 : FaceOf (segment ℝ v1 w1) p)
    (hv2 : v2 ∈ Set.extremePoints ℝ p) :
    affGe {z} ({v1, w1} : Set V3) ∩ affGe {z} ({v2} : Set V3)
      = affGe {z} (({v1, w1} : Set V3) ∩ ({v2} : Set V3)) := by
  have d1 := edge_data hz hv1w1 hface1
  have d2 := single_data hz hv2
  obtain ⟨hfin1, hze1, hF1, hprop1⟩ := d1
  obtain ⟨hfin2, hze2, hF2, hprop2⟩ := d2
  refine fan7_pair hp hz hfin1 hfin2 hze1 hze2 hF1 hF2 rfl rfl hprop1 hprop2 ?_
  intro x hx
  rw [convexHull_singleton] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [Set.mem_singleton_iff] at hx2
  rw [hx2] at hx1 ⊢
  rw [convexHull_pair] at hx1
  have hv2ext : v2 ∈ Set.extremePoints ℝ (segment ℝ v1 w1) := by
    rw [mem_extremePoints_iff_forall_segment] at hv2 ⊢
    exact ⟨hx1, fun a ha b hb hxopen => hv2.2 a (hface1.1 ha) b (hface1.1 hb) hxopen⟩
  have hv2pair : v2 ∈ ({v1, w1} : Set V3) := by
    rcases (EXTREME_POINT_OF_SEGMENT v1 w1 v2).mp hv2ext with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact subset_convexHull ℝ _ ⟨hv2pair, Set.mem_singleton_iff.mpr rfl⟩

/-- `fan7` 组合：单点 × 边。 -/
private theorem fan7_single_edge {p : Set V3} {z : V3} (hp : polyhedron p) (hz : z ∈ interior p)
    {v1 v2 w2 : V3} (hv2w2 : v2 ≠ w2) (hface2 : FaceOf (segment ℝ v2 w2) p)
    (hv1 : v1 ∈ Set.extremePoints ℝ p) :
    affGe {z} ({v1} : Set V3) ∩ affGe {z} ({v2, w2} : Set V3)
      = affGe {z} (({v1} : Set V3) ∩ ({v2, w2} : Set V3)) := by
  have d1 := single_data hz hv1
  have d2 := edge_data hz hv2w2 hface2
  obtain ⟨hfin1, hze1, hF1, hprop1⟩ := d1
  obtain ⟨hfin2, hze2, hF2, hprop2⟩ := d2
  refine fan7_pair hp hz hfin1 hfin2 hze1 hze2 hF1 hF2 rfl rfl hprop1 hprop2 ?_
  intro x hx
  rw [convexHull_singleton] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [Set.mem_singleton_iff] at hx1
  rw [hx1] at hx2 ⊢
  rw [convexHull_pair] at hx2
  have hv1ext : v1 ∈ Set.extremePoints ℝ (segment ℝ v2 w2) := by
    rw [mem_extremePoints_iff_forall_segment] at hv1 ⊢
    exact ⟨hx2, fun a ha b hb hxopen => hv1.2 a (hface2.1 ha) b (hface2.1 hb) hxopen⟩
  have hv1pair : v1 ∈ ({v2, w2} : Set V3) := by
    rcases (EXTREME_POINT_OF_SEGMENT v2 w2 v1).mp hv1ext with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact subset_convexHull ℝ _ ⟨Set.mem_singleton_iff.mpr rfl, hv1pair⟩

/-- `fan7` 组合：单点 × 单点。 -/
private theorem fan7_single_single {p : Set V3} {z : V3} (hp : polyhedron p)
    (hz : z ∈ interior p) {v1 v2 : V3} (hv1 : v1 ∈ Set.extremePoints ℝ p)
    (hv2 : v2 ∈ Set.extremePoints ℝ p) :
    affGe {z} ({v1} : Set V3) ∩ affGe {z} ({v2} : Set V3)
      = affGe {z} (({v1} : Set V3) ∩ ({v2} : Set V3)) := by
  have d1 := single_data hz hv1
  have d2 := single_data hz hv2
  obtain ⟨hfin1, hze1, hF1, hprop1⟩ := d1
  obtain ⟨hfin2, hze2, hF2, hprop2⟩ := d2
  refine fan7_pair hp hz hfin1 hfin2 hze1 hze2 hF1 hF2 rfl rfl hprop1 hprop2 ?_
  intro x hx
  rw [convexHull_singleton, convexHull_singleton] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [Set.mem_singleton_iff] at hx1 hx2
  have hv12 : v1 = v2 := hx1.symm.trans hx2
  rw [hv12, Set.inter_self, convexHull_singleton]
  exact hx2

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

实施状态（本批，已完成，零 sorry）：
- 合取项 (1) 由 `edgeFirstEndpoint_extreme` 覆盖；(2) 由
  `finite_pair_card_two` 覆盖；(4) 由 `interior_not_extremePoint` 覆盖；
  (3) 的非空部分由 `extremePoints_nonempty_of_polyhedron`（Krein–Milman）
  覆盖，有限部分由 `FINITE_POLYHEDRON_EXTREME_POINTS`
  （Kepler/Text/Polytope.lean，题设内联形式即 `polyhedron` 定义）覆盖。
- fan6：按 HOL 证明将配置平移（`u ↦ z + u` 预像，0 成为内点），由
  `faceOf_addLeft_preimage` + `segment_addLeft_preimage` 迁移边面，
  共线性经 `exists_smul_of_collinear_insert` 参数化；t < 0 时
  0 ∈ [v-z, w-z] 与真面-内点不交（`faceOf_disjoint_interior`）矛盾，
  t > 0 时 `POLYHEDRON_COLLINEAR_FACES` 迫使 t = 1（即 v = w）。真面性
  由 `affDim_eq_three_of_mem_interior`（内点 ⇒ 满维 3）对照
  `affDim_segment = 1` 排除「p 退化为段」。
- fan7：`AFF_GE_SING_CONVEX_HULL_ALT`（z-基点版）把两侧锥写成
  `insert z Ray(·)`；公共射线点经平移后的 `POLYHEDRON_COLLINEAR_FACES`
  统一径向参数（s = t ⇒ x = y），再由内引理 `segment_face_inter_eq`
  （两段面之交互于端点集之交，基于 `openSegment_subset_rinterior`、
  `subset_of_faceOf` 与 `EXTREME_POINT_OF_SEGMENT`）把公共点压入
  `convexHull (e1 ∩ e2)`。四种组合（边×边、边×点、点×边、点×点）在
  `fan7_pair` 下统一。

候选已有引理：
- `FAN`、`fan1`、`fan2`、`fan6`、`fan7`、`Graph`（Kepler/Text/Fan.lean:37-56）
- `Set.extremePoints`、`mem_extremePoints`（Mathlib Analysis/Convex/Extreme.lean:68,133）
- `segment`、`openSegment`、`convex_segment`（Mathlib Analysis/Convex/Segment.lean）
- `IsBounded`（Mathlib Topology/Bornology/Basic.lean:99；HOL `bounded`）、
  `interior`、`interior_subset`（Mathlib）
- Polytope 桥件：`FINITE_POLYHEDRON_EXTREME_POINTS`、
  `POLYHEDRON_COLLINEAR_FACES(_STRONG)`、`SUBSET_OF_FACE_OF`、
  `FACE_OF_(DISJOINT_)(RELATIVE_)INTERIOR`、`AFF_GE_SING_CONVEX_HULL_ALT`、
  `EXTREME_POINT_OF_SEGMENT`、`SEGMENT_FACE_OF` -/
theorem POLYHEDRON_FAN {p : Set V3} {z : V3} (hb : Bornology.IsBounded p)
    (hp : ∃ f : Set (Set V3), f.Finite ∧ p = ⋂₀ f ∧
      ∀ h ∈ f, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {y : V3 | a ⬝ᵥ y ≤ b})
    (hz : z ∈ interior p) :
    FAN z (Set.extremePoints ℝ p)
      {e : Set V3 | ∃ v w : V3, e = {v, w} ∧ v ≠ w ∧
        segment ℝ v w ⊆ p ∧ Convex ℝ (segment ℝ v w) ∧
        ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ segment ℝ v w →
          y ∈ openSegment ℝ c d → c ∈ segment ℝ v w ∧ d ∈ segment ℝ v w} := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- 合取项 1：`⋃₀ E ⊆ extremePoints p`（边端点是极值点）
    intro x hx
    obtain ⟨e, he, hxe⟩ := Set.mem_sUnion.mp hx
    obtain ⟨v, w, rfl, hvw, hsub, -, hface⟩ := he
    have hface' : ∀ c d y : V3, c ∈ p → d ∈ p → y ∈ segment ℝ w v →
          y ∈ openSegment ℝ c d → c ∈ segment ℝ w v ∧ d ∈ segment ℝ w v := by
      intro c d y hc hd hy hopen
      rw [segment_symm] at hy ⊢
      exact hface c d y hc hd hy hopen
    have hsub' : segment ℝ w v ⊆ p := by rw [segment_symm]; exact hsub
    have hkeyv := edgeFirstEndpoint_extreme hvw hsub hface
    have hkeyw := edgeFirstEndpoint_extreme (Ne.symm hvw) hsub' hface'
    rcases Set.mem_insert_iff.mp hxe with hxe' | hx'
    · rw [hxe']
      exact hkeyv
    · rw [Set.mem_singleton_iff.mp hx']
      exact hkeyw
  · -- 合取项 2：`Graph E`（`{v,w}` 基数 2）
    intro e he
    obtain ⟨v, w, rfl, hvw, -, -, -⟩ := he
    exact finite_pair_card_two hvw
  · -- 合取项 3 前半：`extremePoints p` 有限（`FINITE_POLYHEDRON_EXTREME_POINTS`：
    -- `p` 为 Polytope 意义下的多面体——题设内联形式即 `polyhedron` 定义）
    have hsp : polyhedron p := hp
    have hfin := FINITE_POLYHEDRON_EXTREME_POINTS hsp
    rwa [Set.setOf_mem_eq] at hfin
  · -- 合取项 3 后半：`extremePoints p` 非空（Krein–Milman）
    exact Set.nonempty_iff_ne_empty.mp
      (extremePoints_nonempty_of_polyhedron hp hb (interior_subset hz))
  · -- 合取项 4：`fan2`（内点非极值点）
    exact interior_not_extremePoint hz
  · -- 合取项 5：`fan6`（边 {v,w} 与 z 不共线；HOL 用 GEOM_ORIGIN_TAC 把 z 平移到 0）
    intro e he
    obtain ⟨v, w, rfl, hvw, hsub, hconv, hface⟩ := he
    have hfaceP : FaceOf (segment ℝ v w) p := ⟨hsub, hconv, hface⟩
    obtain ⟨hve, hwe⟩ := SEGMENT_FACE_OF hfaceP
    have hvz : v ≠ z := fun h => interior_not_extremePoint hz (h ▸ hve)
    have hwz : w ≠ z := fun h => interior_not_extremePoint hz (h ▸ hwe)
    -- 平移配置：p' := (u ↦ z + u) ⁻¹' p，则 0 ∈ interior p'，且平移后的边
    -- [v - z, w - z] 是 p' 的真面
    set p' : Set V3 := (fun u : V3 => z + u) ⁻¹' p with hp'def
    have hsp' : polyhedron p' := polyhedron_addLeft_preimage hp
    have h0int : (0:V3) ∈ interior p' := zero_mem_interior_addLeft_preimage hz
    have hfaceT : FaceOf (segment ℝ (v - z) (w - z)) p' := by
      rw [← segment_addLeft_preimage]
      exact faceOf_addLeft_preimage hfaceP
    have hvz' : v - z ≠ w - z := fun h => hvw (eq_of_sub_eq_right h)
    have hpropT : segment ℝ (v - z) (w - z) ≠ p' := by
      intro heq
      have h1 : affDim (segment ℝ (v - z) (w - z)) = 1 := (affDim_segment _ _).2 hvz'
      rw [heq, affDim_eq_three_of_mem_interior ⟨0, h0int⟩] at h1
      norm_num at h1
    intro hcol
    obtain ⟨t, ht0, htw⟩ := exists_smul_of_collinear_insert hcol hvz hwz
    rcases lt_or_gt_of_ne ht0 with ht | ht
    · -- t < 0：0 ∈ [v - z, w - z] 与 p' 的内点相交，与真面不交内点矛盾
      have h0mem : (0:V3) ∈ segment ℝ (v - z) (w - z) := by
        rw [htw]
        refine ⟨-t / (1 - t), 1 / (1 - t), ?_, ?_, ?_, ?_⟩
        · exact div_nonneg (by linarith) (by linarith)
        · exact div_nonneg (by linarith) (by linarith)
        · rw [← add_div, show -t + 1 = 1 - t from by ring, div_self (by linarith)]
        · rw [smul_smul, ← add_smul]
          have hcoeff : (-t / (1 - t)) + 1 / (1 - t) * t = 0 := by
            rw [div_mul_eq_mul_div, ← add_div, show -t + 1 * t = 0 from by ring]
            exact zero_div (1 - t)
          rw [hcoeff, zero_smul]
      exact (Set.disjoint_left.mp (faceOf_disjoint_interior hfaceT hpropT) h0mem h0int).elim
    · -- t > 0：POLYHEDRON_COLLINEAR_FACES（基点 0）给 t = 1，即 v = w
      have h1 := POLYHEDRON_COLLINEAR_FACES (P := p')
        (f := segment ℝ (v - z) (w - z)) (f' := segment ℝ (v - z) (w - z))
        (p := v - z) (q := w - z) (s := t) (t := 1)
        hsp' h0int hfaceT hpropT hfaceT hpropT
        (left_mem_segment ℝ (v - z) (w - z)) (right_mem_segment ℝ (v - z) (w - z))
        ht zero_lt_one (by rw [one_smul]; exact htw.symm)
      rw [h1, one_smul] at htw
      exact hvw (eq_of_sub_eq_right htw).symm
  · -- 合取项 6：`fan7`（affGe {z} 在边/顶点上的分配律）
    intro e1 he1 e2 he2
    rcases he1 with ⟨v1, w1, rfl, hv1w1, hsub1, hconv1, hface1⟩ | ⟨v1, hv1e, rfl⟩
    · rcases he2 with ⟨v2, w2, rfl, hv2w2, hsub2, hconv2, hface2⟩ | ⟨v2, hv2e, rfl⟩
      · exact fan7_edge_edge hp hz hv1w1 hv2w2 ⟨hsub1, hconv1, hface1⟩
          ⟨hsub2, hconv2, hface2⟩
      · exact fan7_edge_single hp hz hv1w1 ⟨hsub1, hconv1, hface1⟩ hv2e
    · rcases he2 with ⟨v2, w2, rfl, hv2w2, hsub2, hconv2, hface2⟩ | ⟨v2, hv2e, rfl⟩
      · exact fan7_single_edge hp hz hv2w2 ⟨hsub2, hconv2, hface2⟩ hv1e
      · exact fan7_single_single hp hz hv1e hv2e

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
