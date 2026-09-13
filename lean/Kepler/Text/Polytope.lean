/-
Polytope face-theory foundation (S1 stage).

HOL source: Flyspeck HOL Light Multivariate `polytope1.ml` (face_of kit),
`polyhedron.hl` (`fchanged`), `flyspeck_multivariate.ml:6887` (`edges`,
closed segment in the body — kept distinct from `openSegment`-based defs).

Definitions ported here verbatim (bodies identical to the private copies in
PolyAuto4/5/6; merge note: later lanes should delete their copies and import
this file instead).

Encoding: HOL `real^3` ↔ `V3` (Kepler.Geom); `relative_interior` ↔
`intrinsicInterior ℝ` (Mathlib Analysis/Convex/Intrinsic.lean); HOL
`aff_dim` (∅ ↦ -1) ↔ `affDim`; HOL `x IN segment(a,b)` ↔ `x ∈ segment ℝ a b`
(in the flyspeck azure tree, polytope1.ml:25 `segment(a,b)` denotes
`open_segment(a,b)` = `closed_segment DIFF {a,b}` — Brøndsted-style face
definition; `edges` below uses the CLOSED `closed_segment[a,b]`).
-/

import Kepler.Text.PlanarityAuto16
import Kepler.Text.ConformingDefs
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Definitions -/

/-- HOL `aff_dim` (∅ ↦ -1, else dimension of the direction of the affine hull). -/
noncomputable def affDim (s : Set V3) : ℤ :=
  if s = ∅ then -1 else (Module.finrank ℝ (vectorSpan ℝ s) : ℤ)

/-- HOL `t face_of s` (polytope1.ml:22, flyspeck Definition 4.7 QLITJET):
```
t SUBSET s /\ convex t /\
!a b x. a IN s /\ b IN s /\ x IN t /\ x IN segment(a,b) ==> a IN t /\ b IN t
```
-/
def FaceOf (t s : Set V3) : Prop :=
  t ⊆ s ∧ Convex ℝ t ∧
    ∀ a b x : V3, a ∈ s → b ∈ s → x ∈ t → x ∈ openSegment ℝ a b → a ∈ t ∧ b ∈ t

/-- HOL `f facet_of s` (polytope1.ml:1506). -/
def FacetOf (f s : Set V3) : Prop :=
  FaceOf f s ∧ f ≠ ∅ ∧ affDim f = affDim s - 1

/-- HOL `e edge_of s` (polytope1.ml:2847). -/
def edgeOf (e s : Set V3) : Prop :=
  FaceOf e s ∧ affDim e = 1

/-- HOL `edges s = {{v,w} | segment[v,w] edge_of s}` (flyspeck_multivariate.ml:6887;
the body uses the CLOSED `segment`). -/
def edges (s : Set V3) : Set (Set V3) :=
  {e : Set V3 | ∃ v w : V3, e = {v, w} ∧ edgeOf (segment ℝ v w) s}

/-- HOL `polyhedron s` (polytope1.ml:2546, flyspeck Definition 4.8 QSRHLXB). -/
def polyhedron (s : Set V3) : Prop :=
  ∃ F : Set (Set V3), F.Finite ∧ s = ⋂₀ F ∧
    ∀ h ∈ F, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b}

/-- HOL `fchanged f` (polyhedron.hl:512, verbatim):
```
fchanged f = {v | ?v1 t. v = t % v1 /\ v1 IN relative_interior f /\ t > &0}
```
-/
def fchanged (f : Set V3) : Set V3 :=
  {v : V3 | ∃ v1 : V3, ∃ t : ℝ, v = t • v1 ∧ v1 ∈ intrinsicInterior ℝ f ∧ 0 < t}

/-! ## #1 FaceOf kit (short items) -/

/-- HOL `FACE_OF_REFL` (polytope1.ml:46). -/
theorem FaceOf.refl {s : Set V3} (hs : Convex ℝ s) : FaceOf s s :=
  ⟨Subset.rfl, hs, fun _ _ _ ha hb _ _ => ⟨ha, hb⟩⟩

/-- HOL `EMPTY_FACE_OF` (polytope1.ml:54). -/
theorem empty_faceOf (s : Set V3) : FaceOf ∅ s :=
  ⟨empty_subset s, convex_empty, fun _ _ x _ _ hx _ => absurd hx (Set.notMem_empty x)⟩

/-- HOL `FACE_OF_EMPTY` (polytope1.ml:58). -/
theorem faceOf_empty {s : Set V3} : FaceOf s ∅ ↔ s = ∅ := by
  constructor
  · rintro ⟨hsub, -, -⟩
    exact Set.subset_empty_iff.1 hsub
  · rintro rfl
    exact empty_faceOf ∅

/-- HOL `FACE_OF_IMP_SUBSET` (polytope1.ml:235). -/
theorem FaceOf.imp_subset {s t : Set V3} (h : FaceOf t s) : t ⊆ s := h.1

/-- HOL `FACE_OF_IMP_CONVEX` (polytope1.ml:239). -/
theorem FaceOf.imp_convex {s t : Set V3} (h : FaceOf t s) : Convex ℝ t := h.2.1

/-- HOL `FACE_OF_TRANS` (polytope1.ml:63). -/
theorem FaceOf.trans {s t u : Set V3} (hst : FaceOf s t) (htu : FaceOf t u) : FaceOf s u := by
  refine ⟨hst.1.trans htu.1, hst.2.1, ?_⟩
  intro a b x ha hb hx hseg
  obtain ⟨ha', hb'⟩ := htu.2.2 a b x ha hb (hst.1 hx) hseg
  exact hst.2.2 a b x ha' hb' hx hseg

/-- HOL `FACE_OF_FACE` (polytope1.ml:68). -/
theorem faceOf_face {f s t : Set V3} (h : FaceOf t s) :
    FaceOf f t ↔ FaceOf f s ∧ f ⊆ t := by
  constructor
  · rintro ⟨hsub, hcv, hcond⟩
    refine ⟨⟨hsub.trans h.1, hcv, ?_⟩, hsub⟩
    intro a b x ha hb hx hseg
    obtain ⟨ha', hb'⟩ := h.2.2 a b x ha hb (hsub hx) hseg
    exact hcond a b x ha' hb' hx hseg
  · rintro ⟨⟨hsub, hcv, hcond⟩, hsub2⟩
    exact ⟨hsub2, hcv, fun a b x ha hb hx hseg => hcond a b x (h.1 ha) (h.1 hb) hx hseg⟩

/-- HOL `FACE_OF_SUBSET` (polytope1.ml:74). -/
theorem faceOf_subset {f s t : Set V3} (h : FaceOf f s) (h1 : f ⊆ t) (h2 : t ⊆ s) :
    FaceOf f t :=
  ⟨h1, h.2.1, fun a b x ha hb hx hseg => h.2.2 a b x (h2 ha) (h2 hb) hx hseg⟩

/-- HOL `FACE_OF_INTER` (polytope1.ml:88). -/
theorem faceOf_inter {s t1 t2 : Set V3} (h1 : FaceOf t1 s) (h2 : FaceOf t2 s) :
    FaceOf (t1 ∩ t2) s := by
  refine ⟨Set.inter_subset_right.trans h2.1, h1.2.1.inter h2.2.1, ?_⟩
  intro a b x ha hb hx hseg
  obtain ⟨ha1, hb1⟩ := h1.2.2 a b x ha hb hx.1 hseg
  obtain ⟨ha2, hb2⟩ := h2.2.2 a b x ha hb hx.2 hseg
  exact ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩

/-! ## #2 Faces and extreme points -/

/-- HOL `FACE_OF_SING` (polytope1.ml:1266). Mathlib's `Set.extremePoints`
matches HOL's `extreme_point_of` (`mem_extremePoints_iff_left`). -/
theorem faceOf_sing {x : V3} {s : Set V3} :
    FaceOf {x} s ↔ x ∈ Set.extremePoints ℝ s := by
  rw [mem_extremePoints_iff_left]
  constructor
  · rintro ⟨hsub, -, hcond⟩
    exact ⟨hsub (Set.mem_singleton x), fun y hy z hz hseg =>
      (hcond y z x hy hz (Set.mem_singleton x) hseg).1⟩
  · rintro ⟨hxmem, hcond⟩
    refine ⟨Set.singleton_subset_iff.2 hxmem, convex_singleton (𝕜 := ℝ) x, ?_⟩
    intro a b y ha hb hy hseg
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨hcond a ha b hb hseg, hcond b hb a ha (by rwa [openSegment_symm])⟩

/-! ## #3 affDim basics -/

theorem affDim_empty : affDim (∅ : Set V3) = -1 :=
  if_pos rfl

theorem affDim_singleton (x : V3) : affDim {x} = 0 := by
  rw [affDim, if_neg (by simp)]
  simp [vectorSpan_singleton]

theorem affDim_mono {s t : Set V3} (hsub : s ⊆ t) (hs : s.Nonempty) :
    affDim s ≤ affDim t := by
  have hs' : s ≠ ∅ := nonempty_iff_ne_empty.1 hs
  have ht' : t ≠ ∅ := nonempty_iff_ne_empty.1 (hs.mono hsub)
  simp only [affDim, if_neg hs', if_neg ht']
  exact Nat.cast_le.2 (Submodule.finrank_mono (vectorSpan_mono ℝ hsub))

private theorem vectorSpan_segment (v w : V3) :
    vectorSpan ℝ (segment ℝ v w) = ℝ ∙ (w - v) := by
  refine le_antisymm ?_ ?_
  · rw [vectorSpan_def, Submodule.span_le]
    rintro z ⟨p, hp, q, hq, rfl⟩
    simp only [segment, Set.mem_setOf_eq] at hp hq
    obtain ⟨α, β, hα, hβ, hαβ, hpαβ⟩ := hp
    obtain ⟨α', β', hα', hβ', hαβ', hqαβ⟩ := hq
    change (p -ᵥ q) ∈ ((ℝ ∙ (w - v) : Submodule ℝ V3) : Set V3)
    rw [← hpαβ, ← hqαβ, vsub_eq_sub, SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨α' - α, ?_⟩
    rw [show β = 1 - α by linarith, show β' = 1 - α' by linarith]
    module
  · rw [vectorSpan_def]
    refine Submodule.span_mono (Set.singleton_subset_iff.2 ?_)
    exact vsub_mem_vsub (right_mem_segment ℝ v w) (left_mem_segment ℝ v w)

theorem affDim_segment (v w : V3) : affDim (segment ℝ v w) = 1 ↔ v ≠ w := by
  constructor
  · intro h hveq
    subst hveq
    rw [segment_same] at h
    rw [affDim_singleton] at h
    exact zero_ne_one h
  · intro h
    have hne : w - v ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    have hne2 : (segment ℝ v w).Nonempty := ⟨v, left_mem_segment ℝ v w⟩
    simp only [affDim, if_neg (nonempty_iff_ne_empty.1 hne2)]
    rw [vectorSpan_segment, finrank_span_singleton hne]
    norm_cast

private def dotRight (a : V3) : V3 →ₗ[ℝ] ℝ where
  toFun x := a ⬝ᵥ x
  map_add' x y := by
    show a.ofLp ⬝ᵥ (x.ofLp + y.ofLp) = a.ofLp ⬝ᵥ x.ofLp + a.ofLp ⬝ᵥ y.ofLp
    rw [dotProduct_add]
  map_smul' r x := by
    show a.ofLp ⬝ᵥ (r • x.ofLp) = (RingHom.id ℝ) r • (a.ofLp ⬝ᵥ x.ofLp)
    rw [dotProduct_smul]
    simp

theorem affDim_hyperplane {a : V3} (ha : a ≠ 0) (b : ℝ) :
    affDim {x : V3 | a ⬝ᵥ x = b} = 2 := by
  set H := {x : V3 | a ⬝ᵥ x = b} with hH
  have haof : a.ofLp ≠ 0 := by simpa using ha
  have hc : a.ofLp ⬝ᵥ a.ofLp ≠ 0 := fun h => haof (dotProduct_self_eq_zero.1 h)
  have hsolve : ∀ r : ℝ, ∃ x : V3, a ⬝ᵥ x = r := by
    intro r
    refine ⟨(r / (a.ofLp ⬝ᵥ a.ofLp)) • a, ?_⟩
    show a.ofLp ⬝ᵥ ((r / (a.ofLp ⬝ᵥ a.ofLp)) • a.ofLp) = r
    rw [dotProduct_smul, smul_eq_mul]
    field_simp
  obtain ⟨p0, hp0⟩ := hsolve b
  have hsurj : ∀ r : ℝ, ∃ x : V3, dotRight a x = r := hsolve
  have key : vectorSpan ℝ H = LinearMap.ker (dotRight a) := by
    refine le_antisymm ?_ ?_
    · rw [vectorSpan_def, Submodule.span_le]
      rintro z ⟨p, hp, q, hq, rfl⟩
      simp only [hH, Set.mem_setOf_eq] at hp hq
      change (p -ᵥ q) ∈ ((LinearMap.ker (dotRight a) : Submodule ℝ V3) : Set V3)
      have hp' : dotRight a p = b := hp
      have hq' : dotRight a q = b := hq
      rw [vsub_eq_sub, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.map_sub,
        hp', hq', sub_self]
    · intro z hz
      have hzk : dotRight a z = 0 := LinearMap.mem_ker.1 hz
      have hzk2 : a.ofLp ⬝ᵥ z.ofLp = 0 := hzk
      have hpmz : p0 - z ∈ H := by
        simp only [hH, Set.mem_setOf_eq]
        have hsplit : a.ofLp ⬝ᵥ (p0 - z).ofLp = a.ofLp ⬝ᵥ p0.ofLp - a.ofLp ⬝ᵥ z.ofLp := by
          rw [show (p0 - z).ofLp = p0.ofLp - z.ofLp from rfl, dotProduct_sub]
        rw [hsplit, hp0, hzk2, sub_zero]
      show z ∈ vectorSpan ℝ H
      rw [vectorSpan_def]
      exact Submodule.subset_span (Set.mem_vsub.2 ⟨p0, hp0, p0 - z, hpmz,
        by rw [vsub_eq_sub, sub_sub_self]⟩)
  have h1 : Module.finrank ℝ (LinearMap.ker (dotRight a)) = 2 := by
    have hnk := LinearMap.finrank_range_add_finrank_ker (dotRight a)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
      finrank_euclideanSpace_fin] at hnk
    omega
  have hHne : H.Nonempty := ⟨p0, by rw [hH]; exact Set.mem_setOf.2 hp0⟩
  rw [affDim, if_neg (nonempty_iff_ne_empty.1 hHne), key, h1]
  norm_num

/-! ## #4 Relative (intrinsic) interior utilities -/

/-- Membership in the intrinsic interior, characterized by a ball along the
affine hull (HOL `IN_RELATIVE_INTERIOR_CBALL` with `cball` weakened to `ball`;
form adjusted to what Mathlib's `intrinsicInterior` API supports). -/
theorem mem_rint_iff {s : Set V3} {x : V3} :
    x ∈ intrinsicInterior ℝ s ↔
      x ∈ s ∧ ∃ ε > 0, (Metric.ball x ε ∩ (affineSpan ℝ s : Set V3)) ⊆ s := by
  constructor
  · intro hmem
    rw [mem_intrinsicInterior] at hmem
    obtain ⟨y, hy, rfl⟩ := hmem
    have hxmem : ↑y ∈ s := Set.mem_preimage.1 (interior_subset hy)
    refine ⟨hxmem, ?_⟩
    obtain ⟨t, htsub, htopen, hyt⟩ := mem_interior.1 hy
    have hopen := Metric.isOpen_iff.1 htopen
    obtain ⟨ε, hε, hball⟩ := hopen y hyt
    refine ⟨ε, hε, fun w hw => ?_⟩
    have hwball : (⟨w, hw.2⟩ : ↥(affineSpan ℝ s)) ∈ Metric.ball y ε :=
      Metric.mem_ball.2 (show dist (w : V3) (y : V3) < ε from hw.1)
    exact Set.mem_preimage.1 (htsub (hball hwball))
  · rintro ⟨hxmem, ε, hε, hsub⟩
    have hxaff : x ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hxmem
    have hsub' : Metric.ball (⟨x, hxaff⟩ : ↥(affineSpan ℝ s)) ε ⊆
        (Subtype.val ⁻¹' s) := by
      intro w hw
      have hwball : w.1 ∈ Metric.ball x ε := hw
      exact Set.mem_preimage.2 (hsub (Set.mem_inter hwball w.2))
    rw [mem_intrinsicInterior]
    exact ⟨⟨x, hxaff⟩, mem_interior.2 ⟨Metric.ball (⟨x, hxaff⟩ : ↥(affineSpan ℝ s)) ε,
      hsub', Metric.isOpen_ball, Metric.mem_ball_self hε⟩, rfl⟩

/-- Line in the affine span through `p'` in direction `q - p`. -/
private theorem affineSpan_lineq {s : Set V3} {p p' q : V3}
    (hp : p ∈ (affineSpan ℝ s : Set V3)) (hp' : p' ∈ (affineSpan ℝ s : Set V3))
    (hq : q ∈ (affineSpan ℝ s : Set V3)) (t : ℝ) :
    p' + t • (q - p) ∈ (affineSpan ℝ s : Set V3) := by
  have hdir : t • (q -ᵥ p) ∈ (affineSpan ℝ s).direction :=
    Submodule.smul_mem _ t (AffineSubspace.vsub_mem_direction hq hp)
  have hvadd : (t • (q -ᵥ p)) +ᵥ p' = p' + t • (q - p) := by
    rw [vadd_eq_add, vsub_eq_sub]
    module
  rw [← hvadd]
  exact AffineSubspace.vadd_mem_of_mem_direction hdir hp'

/-- Public port of the (previously `sorry`ed private) `convex_intrinsicInterior`
of PolyAuto3.lean:924: the intrinsic interior of a convex set is convex. -/
theorem convex_intrinsicInterior {s : Set V3} (hs : Convex ℝ s) :
    Convex ℝ (intrinsicInterior ℝ s) := by
  intro u hu v hv a b hab hbb hsum
  rcases eq_or_ne b 0 with hb0 | hb0
  · have h1 : a = 1 := by
      have h := hsum
      rw [hb0, add_zero] at h
      exact h
    have h2 : a • u + b • v = u := by rw [h1, hb0, one_smul, zero_smul, add_zero]
    rw [h2]
    exact hu
  rcases eq_or_ne a 0 with ha0 | ha0
  · have h1 : b = 1 := by
      have h := hsum
      rw [ha0, zero_add] at h
      exact h
    have h2 : a • u + b • v = v := by rw [ha0, h1, zero_smul, one_smul, zero_add]
    rw [h2]
    exact hv
  have ha : 0 < a := lt_of_le_of_ne hab (Ne.symm ha0)
  have hb : 0 < b := lt_of_le_of_ne hbb (Ne.symm hb0)
  set z := a • u + b • v with hzdef
  obtain ⟨hu_mem, εu, hεu0, hεu⟩ := mem_rint_iff.1 hu
  obtain ⟨hv_mem, εv, hεv0, hεv⟩ := mem_rint_iff.1 hv
  have hu_aff : u ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hu_mem
  have hv_aff : v ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hv_mem
  have hzmem : z ∈ s := hs hu_mem hv_mem hab hbb hsum
  have hzaff : z ∈ (affineSpan ℝ s : Set V3) := by
    have h0 : u + b • (v - u) ∈ (affineSpan ℝ s : Set V3) :=
      affineSpan_lineq hu_aff hu_aff hv_aff b
    have hba : a = 1 - b := by linarith
    have hzeq : z = u + b • (v - u) := by
      rw [hzdef, hba]
      module
    rw [hzeq]
    exact h0
  refine mem_rint_iff.2 ⟨hzmem, min (a * εu) εv, lt_min (mul_pos ha hεu0) hεv0, fun w hw => ?_⟩
  have hwball : dist w z < min (a * εu) εv := hw.1
  have hnzb : ‖w - z‖ < min (a * εu) εv := hwball
  have h1a : 0 < 1 / a := one_div_pos.2 ha
  have hw'mem : u + (1 / a) • (w - z) ∈ s := by
    refine hεu (Set.mem_inter ?_ ?_)
    · refine Metric.mem_ball.2 ?_
      have hdiff : u + (1 / a) • (w - z) - u = (1 / a) • (w - z) := by
        rw [add_sub_cancel_left]
      have hd : dist (u + (1 / a) • (w - z)) u < εu := by
        rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos h1a]
        have h1 : (1 / a) * ‖w - z‖ < (1 / a) * min (a * εu) εv :=
          mul_lt_mul_of_pos_left hnzb h1a
        have h2 : (1 / a) * min (a * εu) εv ≤ (1 / a) * (a * εu) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt h1a)
        have h3 : (1 / a) * (a * εu) = εu := by field_simp
        rw [h3] at h2
        exact lt_of_lt_of_le h1 h2
      rw [dist_eq_norm] at hd
      exact hd
    · exact affineSpan_lineq hzaff hu_aff hw.2 (1 / a)
  have hw'eq : a • (u + (1 / a) • (w - z)) + b • v = w := by
    rw [smul_add, smul_smul]
    have hmul : (a * (1 / a)) • (w - z) = (w - z) := by
      rw [one_div, mul_inv_cancel₀ ha.ne', one_smul]
    rw [hmul, hzdef]
    have hba : a = 1 - b := by linarith
    rw [hba]
    module
  have hwmem : w ∈ s := by
    have h := hs hw'mem hv_mem hab hbb hsum
    rwa [hw'eq] at h
  exact hwmem

/-! ## #6 ★ SUBSET_OF_FACE_OF (polytope1.ml:267) -/

/-- HOL `SUBSET_OF_FACE_OF`: a set meeting the relative interior of a face's
superset in a nonempty way is contained in the face (ball-along-affine-hull
trick). -/
theorem subset_of_faceOf {t s u : Set V3} (hface : FaceOf t s) (husub : u ⊆ s)
    (hdisj : ¬Disjoint t (intrinsicInterior ℝ u)) : u ⊆ t := by
  obtain ⟨b, hb⟩ := Set.not_disjoint_iff.1 hdisj
  obtain ⟨hbu, ε, hε0, hball⟩ := mem_rint_iff.1 hb.2
  have hbt : b ∈ t := hb.1
  have hbu_aff : b ∈ (affineSpan ℝ u : Set V3) := subset_affineSpan ℝ u hbu
  intro c hc
  by_cases hcb : c = b
  · rw [hcb]
    exact hbt
  · have hnb : ‖b - c‖ ≠ 0 := by
      intro h
      exact hcb (sub_eq_zero.1 (norm_eq_zero.mp h)).symm
    set lam := ε / (2 * ‖b - c‖) with hlam
    have hlam0 : 0 < lam := by
      rw [hlam]
      exact div_pos hε0 (by positivity)
    -- `d` lies beyond `b`, so `b` is in the open segment `(c, d)`
    have hdm : b + lam • (b - c) ∈ u := by
      refine hball (Set.mem_inter ?_ ?_)
      · refine Metric.mem_ball.2 ?_
        have hdd : dist (b + lam • (b - c)) b = lam * ‖b - c‖ := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos hlam0]
        rw [hdd, hlam]
        have h2 : (ε / (2 * ‖b - c‖)) * ‖b - c‖ = ε / 2 := by field_simp
        rw [h2]
        linarith
      · exact affineSpan_lineq (subset_affineSpan ℝ u hc) hbu_aff hbu_aff lam
    have hd : b + lam • (b - c) ∈ s := husub hdm
    -- fire the face condition on the open segment (c, d) through b
    have hbseg : b ∈ openSegment ℝ c (b + lam • (b - c)) := by
      have hpos : 0 < 1 + lam := by linarith
      have hnn : (1 + lam : ℝ) ≠ 0 := by linarith
      have hkey : (1 + lam) • b = lam • c + (b + lam • (b - c)) := by module
      have hkey2 : b + lam • (b - c) = (1 + lam) • b - lam • c := by
        rw [hkey]
        module
      refine ⟨lam / (1 + lam), 1 / (1 + lam), div_pos hlam0 hpos,
        div_pos zero_lt_one hpos, by field_simp; ring, ?_⟩
      rw [hkey2, smul_sub, one_div, div_eq_inv_mul, smul_smul, smul_smul,
        mul_comm (1 + lam)⁻¹ lam, inv_mul_cancel₀ hnn, one_smul, add_sub_cancel]
    exact (hface.2.2 c _ b (husub hc) hd hbt hbseg).1

/-! ## #7 FACE_OF_EQ (polytope1.ml:321) -/

/-- HOL `FACE_OF_EQ`: two faces of `s` whose relative interiors meet agree. -/
theorem faceOf_eq {s t u : Set V3} (ht : FaceOf t s) (hu : FaceOf u s)
    (h : ¬Disjoint (intrinsicInterior ℝ t) (intrinsicInterior ℝ u)) : t = u := by
  refine subset_antisymm ?_ ?_
  · refine subset_of_faceOf hu ht.1 fun hd => h ?_
    exact (Disjoint.mono_left intrinsicInterior_subset hd).symm
  · refine subset_of_faceOf ht hu.1 fun hd => h ?_
    exact Disjoint.mono_left intrinsicInterior_subset hd

/-! ## #5 FACE_OF_DISJOINT_RELATIVE_INTERIOR / _INTERIOR (polytope1.ml:333,342) -/

/-- HOL `FACE_OF_DISJOINT_RELATIVE_INTERIOR`. -/
theorem faceOf_disjoint_rinterior {f s : Set V3} (hf : FaceOf f s) (hne : f ≠ s) :
    Disjoint f (intrinsicInterior ℝ s) := by
  by_contra h
  exact hne (subset_antisymm hf.1 (subset_of_faceOf hf (subset_refl s) h))

/-- HOL `FACE_OF_DISJOINT_INTERIOR`. -/
theorem faceOf_disjoint_interior {f s : Set V3} (hf : FaceOf f s) (hne : f ≠ s) :
    Disjoint f (interior s) :=
  Disjoint.mono_right interior_subset_intrinsicInterior (faceOf_disjoint_rinterior hf hne)

/-! ## #1 (deferred) FACE_OF_IMP_CLOSED / IMP_COMPACT via t = aff t ∩ s -/

private theorem isClosed_affineSpan_coe {t : Set V3} (hne : t ≠ ∅) :
    IsClosed (affineSpan ℝ t : Set V3) := by
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 hne
  have hpaff : p ∈ (affineSpan ℝ t : Set V3) := subset_affineSpan ℝ t hp
  have hsetEq : (affineSpan ℝ t : Set V3) =
      (fun w : V3 => w - p) ⁻¹' ((affineSpan ℝ t).direction : Set V3) := by
    ext w
    rw [Set.mem_preimage]
    refine ⟨fun hw => ?_, fun hd => ?_⟩
    · refine (AffineSubspace.vadd_mem_iff_mem_direction (v := w - p) (p := p) hpaff).1 ?_
      rw [vadd_eq_add, sub_add_cancel]
      exact hw
    · rw [SetLike.mem_coe] at hd
      rw [← AffineSubspace.vadd_mem_iff_mem_direction (v := w - p) (p := p) hpaff] at hd
      rw [vadd_eq_add, sub_add_cancel] at hd
      exact hd
  rw [hsetEq]
  exact IsClosed.preimage (continuous_sub_right p)
    (Submodule.closed_of_finiteDimensional _)

/-- HOL `FACE_OF_STILLCONVEX` second half: a face equals the intersection of
its affine hull with the ambient convex set. -/
theorem faceOf_eq_affineInter {t s : Set V3} (_hs : Convex ℝ s) (hface : FaceOf t s) :
    (affineSpan ℝ t : Set V3) ∩ s ⊆ t := by
  by_cases hte : t = ∅
  · rintro (y ⟨hyaff, -⟩)
    rw [hte, AffineSubspace.span_empty, AffineSubspace.bot_coe] at hyaff
    exact absurd hyaff (by simp)
  · obtain ⟨x0, hx0⟩ := nonempty_iff_ne_empty.2 hte
    obtain ⟨x0i, hx0i⟩ := Set.Nonempty.intrinsicInterior hface.2.1 ⟨x0, hx0⟩
    obtain ⟨hx0mem, ε, hε0, hball⟩ := mem_rint_iff.1 hx0i
    have hx0aff : x0i ∈ (affineSpan ℝ t : Set V3) := subset_affineSpan ℝ t hx0mem
    rintro y ⟨hyaff, hys⟩
    by_cases hey : y = x0i
    · rw [hey]
      exact hx0mem
    ·
      have hnpos : 0 < ‖y - x0i‖ := norm_pos_iff.2 (sub_ne_zero.2 hey)
      have h3p : 0 < 3 * ‖y - x0i‖ := by linarith
      set α := min (ε / (3 * ‖y - x0i‖)) (1 / 2) with hαdef
      have hα0 : 0 < α := lt_min (div_pos hε0 h3p) one_half_pos
      have hαhalf : α ≤ 1 / 2 := min_le_right _ _
      have hαe : α * ‖y - x0i‖ ≤ ε / 3 := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 3)]
        have h1 : α ≤ ε / (3 * ‖y - x0i‖) := min_le_left _ _
        rw [le_div_iff₀ h3p] at h1
        nlinarith
      -- x0' := x0i + α • (y - x0i) lies in t, hence in s
      have hx0' : x0i + α • (y - x0i) ∈ t := by
        refine hball (Set.mem_inter ?_ (affineSpan_lineq hx0aff hx0aff hyaff α))
        refine Metric.mem_ball.2 ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hα0]
        calc α * ‖y - x0i‖ ≤ ε / 3 := hαe
          _ < ε := by linarith
      have hx0's : x0i + α • (y - x0i) ∈ s := hface.1 hx0'
      have hx0'a : x0i + α • (y - x0i) ∈ (affineSpan ℝ t : Set V3) :=
        affineSpan_lineq hx0aff hx0aff hyaff α
      -- the midpoint d_mid = x0' + α • (y - x0') lies in t and in the open segment (x0', y)
      have hdmid : x0i + α • (y - x0i) + α • (y - (x0i + α • (y - x0i))) ∈ t := by
        refine hball (Set.mem_inter ?_ (affineSpan_lineq hx0'a hx0'a hyaff α))
        refine Metric.mem_ball.2 ?_
        have hdd : (x0i + α • (y - x0i) + α • (y - (x0i + α • (y - x0i)))) - x0i
            = ((2 - α) * α) • (y - x0i) := by
          have h1 : (x0i + α • (y - x0i) + α • (y - (x0i + α • (y - x0i)))) - x0i
              = α • (y - x0i) + α • ((y - x0i) - α • (y - x0i)) := by
            module
          rw [h1, smul_sub, ← smul_smul]
          module
        rw [dist_eq_norm, hdd, norm_smul, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 - α),
          abs_of_nonneg (by linarith : (0:ℝ) ≤ α)]
        have hnn : (0:ℝ) ≤ 2 - α := by linarith
        have h5 : (2 - α) * (α * ‖y - x0i‖) ≤ (2 - α) * (ε / 3) :=
          mul_le_mul_of_nonneg_left hαe hnn
        have h6 : (2 - α) * (ε / 3) ≤ 2 * (ε / 3) :=
          mul_le_mul_of_nonneg_right (show (2:ℝ) - α ≤ 2 by linarith)
            (by linarith)
        linarith
      have hdmidseg : x0i + α • (y - x0i) + α • (y - (x0i + α • (y - x0i)))
          ∈ openSegment ℝ (x0i + α • (y - x0i)) y := by
        refine ⟨1 - α, α, by linarith, by linarith, by ring, ?_⟩
        module
      exact (hface.2.2 _ _ _ hx0's hys hdmid hdmidseg).2


/-! ## #5 polyhedron basics (HOL polytope1.ml `polyhedron`, short item set) -/

/-- Dot product additivity in the second argument (V3 bridge, via `dotRight`). -/
private theorem dot_add (a x y : V3) : a ⬝ᵥ (x + y) = a ⬝ᵥ x + a ⬝ᵥ y :=
  LinearMap.map_add (dotRight a) x y

/-- Dot product difference in the second argument (V3 bridge, via `dotRight`). -/
private theorem dot_sub (a x y : V3) : a ⬝ᵥ (x - y) = a ⬝ᵥ x - a ⬝ᵥ y :=
  LinearMap.map_sub (dotRight a) x y

/-- Dot product homogeneity in the second argument (V3 bridge, via `dotRight`). -/
private theorem dot_smul (a : V3) (r : ℝ) (x : V3) : a ⬝ᵥ (r • x) = r * (a ⬝ᵥ x) := by
  rw [show a ⬝ᵥ (r • x) = (RingHom.id ℝ) r • (a ⬝ᵥ x) from
    LinearMap.map_smul (dotRight a) r x, RingHom.id_apply, smul_eq_mul]

/-- Negation of the left argument (V3 bridge). -/
private theorem dot_neg_left (a x : V3) : (-a) ⬝ᵥ x = -(a ⬝ᵥ x) := by
  show (-a).ofLp ⬝ᵥ x.ofLp = -(a.ofLp ⬝ᵥ x.ofLp)
  rw [WithLp.ofLp_neg, neg_dotProduct]

/-- The halfspace `{x : V3 | a ⬝ᵥ x ≤ b}` is convex. -/
private theorem convex_halfspace_le (a : V3) (b : ℝ) : Convex ℝ {x : V3 | a ⬝ᵥ x ≤ b} := by
  intro x hx y hy u v hu hv hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h : a ⬝ᵥ (u • x + v • y) = u * (a ⬝ᵥ x) + v * (a ⬝ᵥ y) := by
    rw [dot_add, dot_smul, dot_smul]
  rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, h]
  have hu1 : u + v = 1 := hab
  have h3 : u * b + v * b = b := by
    have h4 : (u + v) * b = b := by rw [hu1, one_mul]
    rwa [add_mul] at h4
  exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hx hu)
    (mul_le_mul_of_nonneg_left hy hv)) (by rw [h3])

/-- The halfspace `{x : V3 | a ⬝ᵥ x ≤ b}` is closed. -/
private theorem isClosed_halfspace_le (a : V3) (b : ℝ) : IsClosed {x : V3 | a ⬝ᵥ x ≤ b} := by
  have hc : Continuous fun y : V3 => a ⬝ᵥ y :=
    continuous_const.dotProduct (PiLp.continuous_ofLp 2 _)
  exact isClosed_le hc continuous_const

/-- HOL `POLYHEDRON_UNIV`. -/
theorem POLYHEDRON_UNIV : polyhedron (univ : Set V3) := by
  refine ⟨∅, Set.finite_empty, ?_, ?_⟩
  · simp
  · intro h hh
    exact absurd hh (by simp)

/-- HOL `POLYHEDRON_EMPTY`: `∅` is the intersection of two opposite halfspaces. -/
theorem POLYHEDRON_EMPTY : polyhedron (∅ : Set V3) := by
  obtain ⟨a, ha⟩ := exists_ne (0 : V3)
  refine ⟨{{x : V3 | a ⬝ᵥ x ≤ 0}, {x : V3 | 1 ≤ a ⬝ᵥ x}}, by simp, ?_, ?_⟩
  · rw [Set.sInter_insert, Set.sInter_singleton]
    ext x
    simp only [Set.mem_empty_iff_false, false_iff, Set.mem_inter_iff, not_and]
    intro hx1 hx2
    simp only [Set.mem_setOf_eq] at hx1 hx2
    linarith
  · intro k hk
    rcases Set.mem_insert_iff.1 hk with rfl | hk
    · exact ⟨a, 0, ha, rfl⟩
    · rcases Set.mem_singleton_iff.1 hk with rfl
      refine ⟨-a, -1, neg_ne_zero.2 ha, ?_⟩
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        show (-a) ⬝ᵥ x ≤ -1
        rw [dot_neg_left]
        linarith
      · intro h
        show 1 ≤ a ⬝ᵥ x
        rw [dot_neg_left] at h
        linarith

/-- HOL `POLYHEDRON_HALFSPACE_LE`. -/
theorem POLYHEDRON_HALFSPACE_LE {a : V3} (ha : a ≠ 0) (b : ℝ) :
    polyhedron {x : V3 | a ⬝ᵥ x ≤ b} := by
  refine ⟨{{x : V3 | a ⬝ᵥ x ≤ b}}, Set.finite_singleton _, ?_, ?_⟩
  · simp
  · intro k hk
    rcases Set.mem_singleton_iff.1 hk with rfl
    exact ⟨a, b, ha, rfl⟩

/-- HOL `POLYHEDRON_INTER`. -/
theorem POLYHEDRON_INTER {s t : Set V3} (hs : polyhedron s) (ht : polyhedron t) :
    polyhedron (s ∩ t) := by
  obtain ⟨F, hF, rfl, hFprop⟩ := hs
  obtain ⟨G, hG, rfl, hGprop⟩ := ht
  refine ⟨F ∪ G, hF.union hG, ?_, ?_⟩
  · rw [Set.sInter_union]
  · intro k hk
    rcases Set.mem_union _ _ _ |>.1 hk with hk | hk
    · exact hFprop _ hk
    · exact hGprop _ hk

/-- HOL `POLYHEDRON_HYPERPLANE`. -/
theorem POLYHEDRON_HYPERPLANE {a : V3} (ha : a ≠ 0) (b : ℝ) :
    polyhedron {x : V3 | a ⬝ᵥ x = b} := by
  have hset : {x : V3 | a ⬝ᵥ x = b} =
      {x : V3 | a ⬝ᵥ x ≤ b} ∩ {x : V3 | b ≤ a ⬝ᵥ x} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, le_antisymm_iff]
  rw [hset]
  have hge : polyhedron {x : V3 | b ≤ a ⬝ᵥ x} := by
    have : {x : V3 | b ≤ a ⬝ᵥ x} = {x : V3 | (-a) ⬝ᵥ x ≤ -b} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        show (-a) ⬝ᵥ x ≤ -b
        rw [dot_neg_left]
        linarith
      · intro h
        show b ≤ a ⬝ᵥ x
        rw [dot_neg_left] at h
        linarith
    rw [this]
    exact POLYHEDRON_HALFSPACE_LE (neg_ne_zero.2 ha) (-b)
  exact POLYHEDRON_INTER (POLYHEDRON_HALFSPACE_LE ha b) hge

/-- HOL `POLYHEDRON_INTERS`: a finite intersection of polyhedra is a polyhedron. -/
theorem POLYHEDRON_INTERS {F : Set (Set V3)} (hF : F.Finite)
    (hFprop : ∀ k ∈ F, polyhedron k) : polyhedron (⋂₀ F) := by
  classical
  refine Set.Finite.induction_on
    (motive := fun t _ => (∀ j ∈ t, polyhedron j) → polyhedron (⋂₀ t)) F hF ?_ ?_
    hFprop
  · intro _
    simpa using POLYHEDRON_UNIV
  · intro k s' hk _ ih hprop
    rw [Set.sInter_insert]
    exact POLYHEDRON_INTER (hprop k (Set.mem_insert k s'))
      (ih fun j hj => hprop j (Set.mem_insert_of_mem k hj))

/-- HOL `POLYHEDRON_IMP_CLOSED`. -/
theorem POLYHEDRON_IMP_CLOSED {s : Set V3} (hs : polyhedron s) : IsClosed s := by
  obtain ⟨F, hF, rfl, hFprop⟩ := hs
  exact isClosed_sInter fun k hk => by
    obtain ⟨a, b, -, rfl⟩ := hFprop k hk
    exact isClosed_halfspace_le a b

/-- HOL `POLYHEDRON_IMP_CONVEX`. -/
theorem POLYHEDRON_IMP_CONVEX {s : Set V3} (hs : polyhedron s) : Convex ℝ s := by
  obtain ⟨F, hF, rfl, hFprop⟩ := hs
  exact convex_sInter fun k hk => by
    obtain ⟨a, b, -, rfl⟩ := hFprop k hk
    exact convex_halfspace_le a b

/-! ## #6 affine sets are polyhedra (kernel of HOL `AFFINE_IMP_POLYHEDRON`) -/

/-- For `V3` the real inner product agrees with the dot product. -/
private theorem inner_eq_dot (v u : V3) : (inner ℝ v u) = v ⬝ᵥ u := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp

/-- Every affine subspace of `V3` is a polyhedron: it is a finite intersection
of halfspaces.  (HOL `AFFINE_IMP_POLYHEDRON`, polytope.ml:4462.) -/
private theorem affineSubspace_polyhedron (A : AffineSubspace ℝ V3) :
    polyhedron (A : Set V3) := by
  classical
  rcases eq_or_ne A ⊥ with hbot | hbot
  · rw [hbot, AffineSubspace.bot_coe]
    exact POLYHEDRON_EMPTY
  · obtain ⟨c, hc⟩ := (AffineSubspace.nonempty_iff_ne_bot A).2 hbot
    set K := A.direction with hK
    have hmem : ∀ x : V3, x ∈ A ↔ x - c ∈ K := by
      intro x
      constructor
      · intro hx
        have h1 : (x -ᵥ c) ∈ K := AffineSubspace.vsub_mem_direction hx hc
        rwa [vsub_eq_sub] at h1
      · intro hxc
        have h1 : ((x - c) +ᵥ c) ∈ A :=
          AffineSubspace.vadd_mem_of_mem_direction hxc hc
        rwa [vadd_eq_add, sub_add_cancel] at h1
    -- a finite spanning family of `Kᗮ` without the zero vector
    have hfd : (Submodule.orthogonal K).FG :=
      (Submodule.fg_iff_finiteDimensional _).2 (by infer_instance)
    obtain ⟨t0, ht0⟩ := hfd
    set t : Finset V3 := t0.filter (fun v : V3 => v ≠ 0) with htdef
    have hsub0 : (↑t : Set V3) ⊆ ↑t0 := by
      intro v hv
      obtain ⟨hv1, _⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hv)
      exact Finset.mem_coe.2 hv1
    have hspan : Submodule.span ℝ (↑t : Set V3) = Submodule.orthogonal K := by
      rw [← ht0]
      refine le_antisymm (Submodule.span_mono hsub0) ?_
      rw [Submodule.span_le]
      intro v hv
      by_cases hv0 : v = 0
      · subst hv0
        exact Submodule.zero_mem _
      · refine Submodule.subset_span ?_
        exact Finset.mem_filter.2 ⟨Finset.mem_coe.2 hv, hv0⟩
    have hK2 : Submodule.orthogonal (Submodule.orthogonal K) = K := by
      rw [Submodule.orthogonal_orthogonal_eq_closure]
      exact (Submodule.closed_of_finiteDimensional K).submodule_topologicalClosure_eq
    have hbridge : ∀ x : V3, x - c ∈ K ↔ ∀ v ∈ (↑t : Set V3), (inner ℝ v (x - c)) = 0 := by
      intro x
      constructor
      · intro hxm v hv
        have hvK : v ∈ Submodule.orthogonal K := by
          rw [← hspan]
          exact Submodule.subset_span hv
        rw [Submodule.mem_orthogonal'] at hvK
        exact hvK (x - c) hxm
      · intro h
        have hsp : Submodule.span ℝ (↑t : Set V3) ≤ LinearMap.ker
            ({ toFun := fun u : V3 => inner ℝ u (x - c),
               map_add' := by intro p q; rw [inner_add_left],
               map_smul' := by intro r p; simp [inner_smul_left] } :
               V3 →ₗ[ℝ] ℝ) := by
          rw [Submodule.span_le]
          intro v hv
          simp only [SetLike.mem_coe, LinearMap.mem_ker]
          show (inner ℝ v (x - c) : ℝ) = 0
          exact h v hv
        have hmem2 : (x - c) ∈ Submodule.orthogonal (Submodule.orthogonal K) := by
          rw [Submodule.mem_orthogonal]
          intro u hu
          exact hsp (by rw [hspan]; exact hu)
        rw [hK2] at hmem2
        exact hmem2
    refine ⟨(fun v : V3 => {x : V3 | v ⬝ᵥ x ≤ v ⬝ᵥ c}) '' ↑t ∪
      (fun v : V3 => {x : V3 | v ⬝ᵥ c ≤ v ⬝ᵥ x}) '' ↑t,
      (t.finite_toSet.image _).union (t.finite_toSet.image _), ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        have hxm : x - c ∈ K := (hmem x).1 hx
        rw [Set.mem_sInter]
        intro k hk
        rcases Set.mem_union _ _ _ |>.1 hk with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
        · have h2 : v ⬝ᵥ (x - c) = 0 := by
            rw [← inner_eq_dot]
            exact (hbridge x).1 hxm v hv
          have h3 := dot_sub v x c
          rw [h2] at h3
          simp only [Set.mem_setOf_eq]
          linarith
        · have h2 : v ⬝ᵥ (x - c) = 0 := by
            rw [← inner_eq_dot]
            exact (hbridge x).1 hxm v hv
          have h3 := dot_sub v x c
          rw [h2] at h3
          simp only [Set.mem_setOf_eq]
          linarith
      · intro hx
        rw [Set.mem_sInter] at hx
        have hall : ∀ v ∈ (↑t : Set V3), v ⬝ᵥ x = v ⬝ᵥ c := by
          intro v hv
          have h1 := hx _ (Set.mem_union_left _ (Set.mem_image_of_mem _ hv))
          have h2 := hx _ (Set.mem_union_right _ (Set.mem_image_of_mem _ hv))
          simp only [Set.mem_setOf_eq] at h1 h2
          linarith
        refine (hmem x).2 ((hbridge x).2 fun v hv => ?_)
        rw [inner_eq_dot]
        have h3 := dot_sub v x c
        rw [hall v hv, sub_self] at h3
        exact h3
    · intro k hk
      rcases Set.mem_union _ _ _ |>.1 hk with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · exact ⟨v, v ⬝ᵥ c, (Finset.mem_filter.1 hv).2, rfl⟩
      · refine ⟨-v, -(v ⬝ᵥ c), neg_ne_zero.2 (Finset.mem_filter.1 hv).2, ?_⟩
        ext x
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h
          show (-v) ⬝ᵥ x ≤ -(v ⬝ᵥ c)
          rw [dot_neg_left]
          linarith
        · intro h
          show v ⬝ᵥ c ≤ v ⬝ᵥ x
          rw [dot_neg_left] at h
          linarith

/-- HOL `POLYHEDRON_AFFINE_HULL` (via `AFFINE_IMP_POLYHEDRON`). -/
theorem POLYHEDRON_AFFINE_HULL (s : Set V3) : polyhedron (affineSpan ℝ s : Set V3) :=
  affineSubspace_polyhedron _

/-! ## #7 POLYHEDRON_INTER_AFFINE (HOL polytope.ml:4502) -/

/-- HOL `POLYHEDRON_INTER_AFFINE`: canonical affine-hull + halfspace
representation of a polyhedron. -/
theorem POLYHEDRON_INTER_AFFINE {s : Set V3} :
    polyhedron s ↔ ∃ F : Set (Set V3), F.Finite ∧
      s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F ∧
      ∀ h ∈ F, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b} := by
  constructor
  · rintro ⟨F, hF, rfl, hFprop⟩
    refine ⟨F, hF, Set.eq_of_subset_of_subset (fun x hx => ?_) Set.inter_subset_right, hFprop⟩
    exact ⟨subset_affineSpan ℝ _ hx, hx⟩
  · rintro ⟨F, hF, hs, hFprop⟩
    rw [hs]
    exact POLYHEDRON_INTER (POLYHEDRON_AFFINE_HULL s) (POLYHEDRON_INTERS hF
      (fun k hk => by
        obtain ⟨a, b, ha, rfl⟩ := hFprop k hk
        exact POLYHEDRON_HALFSPACE_LE ha b))

/-! ## #8 POLYHEDRON_INTER_AFFINE_MINIMAL (HOL polytope.ml:4628,
POLYHEDRON_INTER_AFFINE_PARALLEL_MINIMAL collapsed to a direct
cardinality-minimal argument) -/

/-- HOL `POLYHEDRON_INTER_AFFINE_MINIMAL`: a polyhedron admits a finite
halfspace representation that is *irredundant*: every proper subfamily
strictly enlarges the set. -/
theorem POLYHEDRON_INTER_AFFINE_MINIMAL {s : Set V3} :
    polyhedron s ↔ ∃ F : Set (Set V3), F.Finite ∧
      s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F ∧
      (∀ h ∈ F, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b}) ∧
      ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F' := by
  classical
  refine ⟨fun h => ?_, fun h => POLYHEDRON_INTER_AFFINE.2 (by
    obtain ⟨F, hF, hs, hFprop, -⟩ := h
    exact ⟨F, hF, hs, hFprop⟩)⟩
  obtain ⟨F0, hF0, hs0, hF0prop⟩ := POLYHEDRON_INTER_AFFINE.1 h
  set Swit : Set (Set (Set V3)) := {G : Set (Set V3) | G.Finite ∧
    s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ G ∧
    (∀ h ∈ G, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b})} with hSwit
  have hWne : Swit.Nonempty := ⟨F0, by
    rw [hSwit, Set.mem_setOf_eq]
    exact ⟨hF0, hs0, hF0prop⟩⟩
  set F := Function.argminOn (f := Set.ncard) Swit hWne with hFdef
  have hFmem : F ∈ Swit := Function.argminOn_mem (f := Set.ncard) Swit hWne
  obtain ⟨hF, hs, hFprop⟩ : (F.Finite ∧ s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F ∧
      ∀ h ∈ F, ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b}) := hFmem
  refine ⟨F, hF, hs, hFprop, ?_⟩
  intro F' hsub
  have hsubFF : F' ⊆ F := hsub.1
  have hF'fin : F'.Finite := hF.subset hsubFF
  have hF'prop : ∀ h ∈ F', ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b} :=
    fun h hk => hFprop h (hsubFF hk)
  have hssub : s ⊆ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F' := by
    refine Set.subset_inter (subset_affineSpan ℝ s) ?_
    calc s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F := hs
      _ ⊆ ⋂₀ F := Set.inter_subset_right
      _ ⊆ ⋂₀ F' := Set.sInter_subset_sInter hsubFF
  refine Set.ssubset_iff_subset_ne.2 ⟨hssub, fun heq => ?_⟩
  have hF'mem : F' ∈ Swit := by
    rw [hSwit, Set.mem_setOf_eq]
    exact ⟨hF'fin, heq, hF'prop⟩
  have hlt : F'.ncard < F.ncard := Set.ncard_lt_ncard hsub hF
  exact Function.not_lt_argminOn (f := Set.ncard) Swit hF'mem hlt

/-! ## #9 RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT (HOL polytope.ml:4640) -/

/-- HOL `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT`: for an irredundant
halfspace representation `s = affine hull s ∩ ⋂₀ F`, the intrinsic interior
is cut out by the *strict* inequalities. -/
theorem RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ)
    (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F') :
    intrinsicInterior ℝ s = {x : V3 | x ∈ s ∧ ∀ h ∈ F, a h ⬝ᵥ x < b h} := by
  classical
  haveI : Finite F := hF
  ext x
  constructor
  · -- the intrinsic interior is inside every defining halfspace, strictly
    intro hx
    obtain ⟨hxmem, ε, hε0, hball⟩ := mem_rint_iff.1 hx
    refine ⟨hxmem, fun h hk => ?_⟩
    obtain ⟨ha, hh⟩ := hFprop h hk
    have hxInter : x ∈ ⋂₀ F := by rw [hs] at hxmem; exact hxmem.2
    have hxh : x ∈ h := Set.mem_sInter.1 hxInter h hk
    rw [hh, Set.mem_setOf_eq] at hxh
    have hxA : a h ⬝ᵥ x ≤ b h := hxh
    by_contra hcon
    push_neg at hcon
    have heq : a h ⬝ᵥ x = b h := le_antisymm hxA hcon
    -- remove the h-th halfspace: minimality produces z in the affine hull
    -- violating h but satisfying all the others
    have hsdiff : F \ {h} ⊂ F := by
      refine Set.ssubset_iff_subset_ne.2 ⟨Set.sdiff_subset, fun hEq => ?_⟩
      have hmem' : h ∈ F \ {h} := by rw [hEq]; exact hk
      exact absurd hmem'.2 (by simp)
    obtain ⟨-, z, hzT, hzs⟩ := Set.ssubset_iff_exists.1 (hmin _ hsdiff)
    have hzaff : z ∈ (affineSpan ℝ s : Set V3) := hzT.1
    have hall : ∀ i ∈ F \ {h}, z ∈ i := fun i hi =>
      Set.mem_sInter.1 hzT.2 i hi
    have hzF : z ∉ ⋂₀ F := by
      rw [hs] at hzs
      exact fun hz' => hzs ⟨hzaff, hz'⟩
    obtain ⟨i, hiF, hzi⟩ : ∃ i ∈ F, z ∉ i := by
      by_contra hcon'
      push_neg at hcon'
      exact hzF (Set.mem_sInter.2 hcon')
    have hih : i = h := by
      by_contra hne
      exact hzi (hall i ⟨hiF, by simp [hne]⟩)
    have hAz : b h < a h ⬝ᵥ z := by
      have hkz : z ∉ h := by rw [← hih]; exact hzi
      rw [hh] at hkz
      simpa only [Set.mem_setOf_eq, not_le] using hkz
    -- the point w := x + t • (z - x) lies in s but violates the h-th halfspace
    set t : ℝ := min (1 / 2) (ε / (2 * (‖z - x‖ + 1))) with htdef
    have ht0 : 0 < t := lt_min (by norm_num : (0:ℝ) < 1 / 2)
      (div_pos hε0 (by positivity))
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num : (1 / 2 : ℝ) < 1)
    have hwball : ‖x + t • (z - x) - x‖ < ε := by
      have hstep : x + t • (z - x) - x = t • (z - x) := by
        rw [smul_sub]; module
      rw [hstep, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have h1 : t ≤ ε / (2 * (‖z - x‖ + 1)) := min_le_right _ _
      have hK0 : 0 ≤ ε / (2 * (‖z - x‖ + 1)) := div_nonneg hε0.le (by positivity)
      have h2 : ‖z - x‖ ≤ ‖z - x‖ + 1 := by linarith [norm_nonneg (z - x)]
      calc t * ‖z - x‖ ≤ (ε / (2 * (‖z - x‖ + 1))) * ‖z - x‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg (z - x))
        _ ≤ (ε / (2 * (‖z - x‖ + 1))) * (‖z - x‖ + 1) :=
          mul_le_mul_of_nonneg_left h2 hK0
        _ = ε / 2 := by field_simp
      linarith
    have hxaff : x ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hxmem
    have hw : x + t • (z - x) ∈ s :=
      hball ⟨hwball, affineSpan_lineq hxaff hxaff hzaff t⟩
    have hws : x + t • (z - x) ∈ ⋂₀ F := by rw [hs] at hw; exact hw.2
    have hwh : x + t • (z - x) ∈ h := Set.mem_sInter.1 hws h hk
    rw [hh, Set.mem_setOf_eq] at hwh
    have hwA : a h ⬝ᵥ (x + t • (z - x)) ≤ b h := hwh
    have hAw : a h ⬝ᵥ (x + t • (z - x))
        = a h ⬝ᵥ x + t * (a h ⬝ᵥ z - a h ⬝ᵥ x) := by
      have e1 : a h ⬝ᵥ (x + t • (z - x)) = a h ⬝ᵥ x + a h ⬝ᵥ (t • (z - x)) :=
        dot_add _ _ _
      have e2 : a h ⬝ᵥ (t • (z - x)) = t * (a h ⬝ᵥ (z - x)) := dot_smul _ _ _
      have e3 : a h ⬝ᵥ (z - x) = a h ⬝ᵥ z - a h ⬝ᵥ x := dot_sub _ _ _
      rw [e1, e2, e3]
    rw [heq] at hAw
    rw [hAw] at hwA
    have hpos' : 0 < t * (a h ⬝ᵥ z - b h) := mul_pos ht0 (by linarith)
    linarith
  · -- all strict inequalities give a point of the intrinsic interior
    rintro ⟨hxmem, hstrict⟩
    set O : Set V3 := ⋂ h : {y // y ∈ F}, {y : V3 | a h ⬝ᵥ y < b h} with hO
    have hOopen : IsOpen O := by
      rw [hO]
      exact isOpen_iInter_of_finite fun h => isOpen_lt
        (continuous_const.dotProduct (PiLp.continuous_ofLp 2 _)) continuous_const
    have hxO : x ∈ O := by
      rw [hO, Set.mem_iInter]
      exact fun h => hstrict h.1 h.2
    obtain ⟨δ, hδ0, hballδ⟩ := Metric.isOpen_iff.1 hOopen x hxO
    refine mem_rint_iff.2 ⟨hxmem, δ, hδ0, fun y hy => ?_⟩
    rw [hs]
    refine ⟨hy.2, fun i hi => ?_⟩
    obtain ⟨-, hhi⟩ := hFprop i hi
    have hyO : y ∈ O := hballδ (Metric.mem_ball.2 hy.1)
    rw [hO] at hyO
    have hyi : a i ⬝ᵥ y < b i := Set.mem_iInter.1 hyO ⟨i, hi⟩
    rw [hhi]
    exact Set.mem_setOf.2 (le_of_lt hyi)

/-! ## #10 FACET_OF_POLYHEDRON_EXPLICIT — supporting-face half
(HOL polytope.ml:4718, `FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE` ingredient) -/

/-- A supporting hyperplane cuts a face: for convex `s` with `a ⬝ᵥ x ≤ c` on
`s`, the slice `s ∩ {a ⬝ᵥ x = c}` is a face of `s`. -/
private theorem faceOf_supporting_eq {s : Set V3} (hs : Convex ℝ s) (a : V3) (c : ℝ)
    (hsub : ∀ x ∈ s, a ⬝ᵥ x ≤ c) :
    FaceOf (s ∩ {x : V3 | a ⬝ᵥ x = c}) s := by
  refine ⟨Set.inter_subset_left, ?_, ?_⟩
  · intro p hp q hq u v hu1 hv1 hab
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq ⊢
    obtain ⟨hps, hpP⟩ := hp
    obtain ⟨hqs, hqP⟩ := hq
    refine ⟨hs hps hqs hu1 hv1 hab, ?_⟩
    have e1 : a ⬝ᵥ (u • p + v • q) = u * (a ⬝ᵥ p) + v * (a ⬝ᵥ q) := by
      rw [dot_add, dot_smul, dot_smul]
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, e1, hpP, hqP]
    have hcc : (u + v) * c = c := by rw [hab, one_mul]
    linarith [mul_add u v c, mul_comm v c, hcc]
  · rintro p q x hps hqs hx hseg
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨hxs, hxe⟩ := hx
    obtain ⟨u, v, hu0, hv0, huv, hxuv⟩ := hseg
    have e1 : a ⬝ᵥ (u • p + v • q) = u * (a ⬝ᵥ p) + v * (a ⬝ᵥ q) := by
      rw [dot_add, dot_smul, dot_smul]
    have hpx : a ⬝ᵥ x = u * (a ⬝ᵥ p) + v * (a ⬝ᵥ q) := by
      rw [← hxuv, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, e1]
    rw [hxe] at hpx
    have key : u * (c - a ⬝ᵥ p) + v * (c - a ⬝ᵥ q) = 0 := by
      have h2 : u * (c - a ⬝ᵥ p) + v * (c - a ⬝ᵥ q)
          = (u + v) * c - (u * (a ⬝ᵥ p) + v * (a ⬝ᵥ q)) := by ring
      rw [h2, huv, one_mul, ← hpx]
      ring
    have hpp : a ⬝ᵥ p = c := by
      by_contra hne
      have hgt : a ⬝ᵥ p < c := lt_of_le_of_ne (hsub p hps) hne
      have hppos : 0 < u * (c - a ⬝ᵥ p) := mul_pos hu0 (sub_pos.2 hgt)
      have hqpos : 0 ≤ v * (c - a ⬝ᵥ q) :=
        mul_nonneg hv0.le (sub_nonneg.2 (hsub q hqs))
      linarith
    have hqq : a ⬝ᵥ q = c := by
      by_contra hne
      have hgt : a ⬝ᵥ q < c := lt_of_le_of_ne (hsub q hqs) hne
      have hppos : 0 < v * (c - a ⬝ᵥ q) := mul_pos hv0 (sub_pos.2 hgt)
      have hqpos : 0 ≤ u * (c - a ⬝ᵥ p) :=
        mul_nonneg hu0.le (sub_nonneg.2 (hsub p hps))
      linarith
    exact ⟨⟨hps, hpp⟩, ⟨hqs, hqq⟩⟩

/-- Slice-face half of HOL `FACET_OF_POLYHEDRON_EXPLICIT` (⇐ direction,
facehood part): for each defining halfspace `h` of an irredundant
representation, `s ∩ {a h ⬝ᵥ x = b h}` is a face of `s`. -/
theorem FACE_OF_POLYHEDRON_SLICE {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ) (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F')
    (h : Set V3) (hk : h ∈ F) :
    FaceOf (s ∩ {x : V3 | a h ⬝ᵥ x = b h}) s := by
  obtain ⟨-, hh⟩ := hFprop h hk
  have hsup : ∀ x ∈ s, a h ⬝ᵥ x ≤ b h := by
    intro x hx
    have hxInter : x ∈ ⋂₀ F := by rw [hs] at hx; exact hx.2
    have hxh : x ∈ h := Set.mem_sInter.1 hxInter h hk
    rw [hh, Set.mem_setOf_eq] at hxh
    exact hxh
  exact faceOf_supporting_eq
    (POLYHEDRON_IMP_CONVEX (POLYHEDRON_INTER_AFFINE.2 ⟨F, hF, hs,
      fun k hk => ⟨a k, b k, (hFprop k hk).1, (hFprop k hk).2⟩⟩))
    (a h) (b h) hsup

/-! ## #12 FACE_OF_AFF_DIM_LT (HOL polytope.ml:393) -/

private theorem affDim_ge_neg1 (s : Set V3) : -1 ≤ affDim s := by
  by_cases hs : s = ∅
  · rw [hs, affDim_empty]
  · simp only [affDim, if_neg hs]
    have h : (0 : ℤ) ≤ (Module.finrank ℝ (vectorSpan ℝ s) : ℤ) := by
      exact_mod_cast Nat.zero_le _
    linarith

/-- HOL `FACE_OF_AFF_DIM_LT` (polytope.ml:393): a proper face of a convex
set has strictly smaller affine dimension. -/
theorem FACE_OF_AFF_DIM_LT {f s : Set V3} (hsc : Convex ℝ s) (hface : FaceOf f s)
    (hne : f ≠ s) : affDim f < affDim s := by
  by_cases hf : f = ∅
  · have hsne : s ≠ ∅ := by
      intro h
      exact hne (h ▸ hf)
    have h1 : (0 : ℤ) ≤ affDim s := by
      simp only [affDim, if_neg hsne]
      have this : (0 : ℤ) ≤ (Module.finrank ℝ (vectorSpan ℝ s) : ℤ) := by
        exact_mod_cast Nat.zero_le _
      exact this
    rw [hf, affDim_empty]
    linarith
  · have hfne : f.Nonempty := nonempty_iff_ne_empty.2 hf
    have hsne : s.Nonempty := hfne.mono hface.1
    obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hsc hsne
    have hxf : x ∉ f := fun hmem =>
      (Set.disjoint_left.1 (faceOf_disjoint_rinterior hface hne)) hmem hx
    by_contra hcon
    push_neg at hcon
    have hmono := affDim_mono hface.1 hfne
    have hfeq : affDim f = affDim s := le_antisymm hmono hcon
    have hfe : f ≠ ∅ := hf
    have hfs : s ≠ ∅ := nonempty_iff_ne_empty.1 hsne
    simp only [affDim, if_neg hfe, if_neg hfs] at hfeq
    have hvle : vectorSpan ℝ f ≤ vectorSpan ℝ s := vectorSpan_mono ℝ hface.1
    have hnat : Module.finrank ℝ (vectorSpan ℝ s) ≤ Module.finrank ℝ (vectorSpan ℝ f) :=
      le_of_eq (by exact_mod_cast hfeq.symm)
    have hveq : vectorSpan ℝ f = vectorSpan ℝ s :=
      Submodule.eq_of_le_of_finrank_le hvle hnat
    obtain ⟨p, hp⟩ := hfne
    have heq : (affineSpan ℝ f : AffineSubspace ℝ V3) = affineSpan ℝ s := by
      refine AffineSubspace.eq_of_direction_eq_of_nonempty_of_le ?_
        ⟨p, subset_affineSpan ℝ _ hp⟩ (affineSpan_mono ℝ hface.1)
      rw [direction_affineSpan, direction_affineSpan, hveq]
    have hspan : (affineSpan ℝ f : Set V3) = (affineSpan ℝ s : Set V3) := by rw [heq]
    obtain ⟨hxmem, ε, hε, hball⟩ := mem_rint_iff.1 hx
    have hxaff : x ∈ (affineSpan ℝ f : Set V3) := by
      rw [hspan]; exact subset_affineSpan ℝ s hxmem
    have hxs : x ∈ s := hball ⟨Metric.mem_ball_self hε, by rw [← hspan]; exact hxaff⟩
    exact hxf (faceOf_eq_affineInter hsc hface ⟨hxaff, hxs⟩)

/-! ## #12a Slice kit for the minimal halfspace representation -/

private theorem convex_of_minrep {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ) (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h}) :
    Convex ℝ s :=
  POLYHEDRON_IMP_CONVEX (POLYHEDRON_INTER_AFFINE.2 ⟨F, hF, hs,
    fun k hk => ⟨a k, b k, (hFprop k hk).1, (hFprop k hk).2⟩⟩)

/-- For each constraint `h` of an irredundant representation there are points
of `s` strictly on both sides of the hyperplane `{a h ⬝ᵥ x = b h}`. -/
private theorem slice_sides {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ) (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F')
    (hsne : s ≠ ∅) (h : Set V3) (hh : h ∈ F) :
    ∃ x z : V3, x ∈ s ∧ (∀ i ∈ F, a i ⬝ᵥ x < b i) ∧
      z ∈ (affineSpan ℝ s : Set V3) ∩ ⋂₀ (F \ {h}) ∧
      a h ⬝ᵥ x < b h ∧ b h < a h ⬝ᵥ z := by
  have hconv := convex_of_minrep a b hF hs hFprop
  have hrie : intrinsicInterior ℝ s = {x : V3 | x ∈ s ∧ ∀ i ∈ F, a i ⬝ᵥ x < b i} :=
    RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hconv (nonempty_iff_ne_empty.2 hsne)
  have hx' : x ∈ s ∧ ∀ i ∈ F, a i ⬝ᵥ x < b i := by rw [hrie] at hx; exact hx
  have hsdiff : F \ {h} ⊂ F := by
    refine Set.ssubset_iff_subset_ne.2 ⟨Set.sdiff_subset, fun hEq => ?_⟩
    have hmem' : h ∈ F \ {h} := by rw [hEq]; exact hh
    exact absurd hmem'.2 (by simp)
  obtain ⟨-, z, hzT, hzs⟩ := Set.ssubset_iff_exists.1 (hmin _ hsdiff)
  have hzaff : z ∈ (affineSpan ℝ s : Set V3) := hzT.1
  have hzF : z ∉ ⋂₀ F := by
    rw [hs] at hzs
    exact fun hz' => hzs ⟨hzaff, hz'⟩
  obtain ⟨i, hiF, hzi⟩ : ∃ i ∈ F, z ∉ i := by
    by_contra hcon'
    push_neg at hcon'
    exact hzF (Set.mem_sInter.2 hcon')
  have hih : i = h := by
    by_contra hne
    exact hzi (Set.mem_sInter.1 hzT.2 i ⟨hiF, by simp [hne]⟩)
  have hzA : b h < a h ⬝ᵥ z := by
    have hkz : z ∉ h := by rw [← hih]; exact hzi
    rw [(hFprop h hh).2] at hkz
    simpa only [Set.mem_setOf_eq, not_le] using hkz
  exact ⟨x, z, hx'.1, hx'.2, ⟨hzaff, hzT.2⟩, hx'.2 h hh, hzA⟩

/-- The crossing point: `h` is tight and all other constraints are strict. -/
private theorem slice_cross {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ) (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F')
    (hsne : s ≠ ∅) (h : Set V3) (hh : h ∈ F) :
    ∃ x : V3, x ∈ s ∧ a h ⬝ᵥ x = b h ∧
      (∀ i ∈ F, i ≠ h → a i ⬝ᵥ x < b i) ∧ x ∈ (affineSpan ℝ s : Set V3) := by
  obtain ⟨p, z, hps, hpstrict, hzs, hpl, hzg⟩ :=
    slice_sides a b hF hs hFprop hmin hsne h hh
  have hpaff : p ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hps
  have hzaff : z ∈ (affineSpan ℝ s : Set V3) := hzs.1
  obtain ⟨t, htp, ht1, htden⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      t * (a h ⬝ᵥ z - a h ⬝ᵥ p) = b h - a h ⬝ᵥ p :=
    ⟨(b h - a h ⬝ᵥ p) / (a h ⬝ᵥ z - a h ⬝ᵥ p), div_pos (by linarith) (by linarith),
      (div_lt_one (by linarith)).2 (by linarith), div_mul_cancel₀ _ (by linarith)⟩
  have hqdot : ∀ w : V3, w ⬝ᵥ (p + t • (z - p)) = w ⬝ᵥ p + t * (w ⬝ᵥ z - w ⬝ᵥ p) := by
    intro w
    have e1 : w ⬝ᵥ (p + t • (z - p)) = w ⬝ᵥ p + w ⬝ᵥ (t • (z - p)) := dot_add _ _ _
    have e2 : w ⬝ᵥ (t • (z - p)) = t * (w ⬝ᵥ (z - p)) := dot_smul _ _ _
    have e3 : w ⬝ᵥ (z - p) = w ⬝ᵥ z - w ⬝ᵥ p := dot_sub _ _ _
    rw [e1, e2, e3]
  refine ⟨p + t • (z - p), ?_, ?_, ?_, ?_⟩
  · rw [hs]
    refine ⟨affineSpan_lineq hpaff hpaff hzaff t, fun i hi => ?_⟩
    rw [(hFprop i hi).2, Set.mem_setOf_eq, WithLp.ofLp_add,
      WithLp.ofLp_smul, WithLp.ofLp_sub, hqdot (a i)]
    by_cases hih : i = h
    · rw [← hih] at htden
      linarith
    · have hiz : a i ⬝ᵥ z ≤ b i := by
        have hzi : z ∈ i := Set.mem_sInter.1 hzs.2 i ((Set.mem_diff i).2 ⟨hi, hih⟩)
        rw [(hFprop i hi).2] at hzi
        exact hzi
      have hstep : t * (a i ⬝ᵥ z - a i ⬝ᵥ p) ≤ t * (b i - a i ⬝ᵥ p) :=
        mul_le_mul_of_nonneg_left (by linarith) htp.le
      have hkey : t * (b i - a i ⬝ᵥ p) < b i - a i ⬝ᵥ p := by
        refine lt_of_lt_of_le
          (mul_lt_mul_of_pos_right ht1 (by linarith [hpstrict i hi])) ?_
        rw [one_mul]
      linarith
  · rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub, hqdot (a h)]
    linarith
  · intro i hi hih
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub, hqdot (a i)]
    have hiz : a i ⬝ᵥ z ≤ b i := by
      have hzi : z ∈ i := Set.mem_sInter.1 hzs.2 i ((Set.mem_diff i).2 ⟨hi, hih⟩)
      rw [(hFprop i hi).2] at hzi
      exact hzi
    have hstep : t * (a i ⬝ᵥ z - a i ⬝ᵥ p) ≤ t * (b i - a i ⬝ᵥ p) :=
      mul_le_mul_of_nonneg_left (by linarith) htp.le
    have hkey : t * (b i - a i ⬝ᵥ p) < b i - a i ⬝ᵥ p := by
      refine lt_of_lt_of_le
        (mul_lt_mul_of_pos_right ht1 (by linarith [hpstrict i hi])) ?_
      rw [one_mul]
    linarith
  · exact affineSpan_lineq hpaff hpaff hzaff t

/-- The span of a nonempty hyperplane slice of `s` is the direction of `s`
killed by the slice's normal vector. -/
private theorem vectorSpan_slice {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ) (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F')
    (hsne : s ≠ ∅) (h : Set V3) (hh : h ∈ F) :
    vectorSpan ℝ (s ∩ {x : V3 | a h ⬝ᵥ x = b h})
      = vectorSpan ℝ s ⊓ LinearMap.ker (dotRight (a h)) := by
  classical
  obtain ⟨x0, hx0s, hx0eq, hx0st, hx0aff⟩ := slice_cross a b hF hs hFprop hmin hsne h hh
  haveI : Finite F := hF
  have hlin : ∀ u x y : V3, ∀ r : ℝ,
      u.ofLp ⬝ᵥ (x + r • y).ofLp = u.ofLp ⬝ᵥ x.ofLp + r * (u.ofLp ⬝ᵥ y.ofLp) := by
    intro u x y r
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
  refine le_antisymm (le_inf (vectorSpan_mono ℝ Set.inter_subset_left) ?_) ?_
  · rw [vectorSpan_def, Submodule.span_le]
    rintro w ⟨p, hp, q, hq, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq
    change (p -ᵥ q) ∈ ((LinearMap.ker (dotRight (a h)) : Submodule ℝ V3) : Set V3)
    rw [vsub_eq_sub, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.map_sub]
    have hp' : dotRight (a h) p = b h := hp.2
    have hq' : dotRight (a h) q = b h := hq.2
    rw [hp', hq', sub_self]
  · intro w hw
    obtain ⟨hwW, hwK⟩ := Submodule.mem_inf.1 hw
    have hwK' : dotRight (a h) w = 0 := LinearMap.mem_ker.1 hwK
    have hwK'' : a h ⬝ᵥ w = 0 := hwK'
    have hwdir : w ∈ (affineSpan ℝ s).direction := by
      rw [direction_affineSpan]
      exact hwW
    set O : Set V3 := ⋂ i : {y // y ∈ F}, {y : V3 | a i.1 ⬝ᵥ y < b i.1 ∨ i.1 = h} with hO
    have hOopen : IsOpen O := by
      rw [hO]
      refine isOpen_iInter_of_finite fun i => ?_
      by_cases hih : i.1 = h
      · have hset : {y : V3 | a i.1 ⬝ᵥ y < b i.1 ∨ i.1 = h} = (univ : Set V3) := by
          ext y
          simp [hih]
        rw [hset]
        exact isOpen_univ
      · have hset : {y : V3 | a i.1 ⬝ᵥ y < b i.1 ∨ i.1 = h}
            = {y : V3 | a i.1 ⬝ᵥ y < b i.1} := by
          ext y
          simp [hih]
        rw [hset]
        exact isOpen_lt (continuous_const.dotProduct (PiLp.continuous_ofLp 2 _))
          continuous_const
    have hx0O : x0 ∈ O := by
      rw [hO, Set.mem_iInter]
      intro i
      by_cases hih : i.1 = h
      · right
        exact hih
      · left
        exact hx0st i.1 i.2 hih
    obtain ⟨ε, hε0, hballO⟩ := Metric.isOpen_iff.1 hOopen x0 hx0O
    have htex : ∃ t : ℝ, 0 < t ∧ ‖x0 + t • w - x0‖ < ε := by
      refine ⟨ε / (2 * (‖w‖ + 1)), div_pos hε0 (by positivity), ?_⟩
      have hstep : x0 + (ε / (2 * (‖w‖ + 1))) • w - x0
          = (ε / (2 * (‖w‖ + 1))) • w := by rw [add_sub_cancel_left]
      rw [hstep, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hε0 (by positivity))]
      calc (ε / (2 * (‖w‖ + 1))) * ‖w‖
          ≤ (ε / (2 * (‖w‖ + 1))) * (‖w‖ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w])
              (div_nonneg hε0.le (by positivity))
        _ = ε / 2 := by field_simp
      linarith
    obtain ⟨t, ht0, htball⟩ := htex
    have hqA : x0 + t • w ∈ (affineSpan ℝ s : Set V3) := by
      have hv : (t • w) +ᵥ x0 = x0 + t • w := by rw [vadd_eq_add]; module
      rw [← hv]
      exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hwdir) hx0aff
    have hqH : (a h).ofLp ⬝ᵥ (x0 + t • w).ofLp = b h := by
      rw [hlin, hx0eq, hwK'', mul_zero, add_zero]
    have h1 : x0 + t • w ∈ ⋂₀ F := by
      refine Set.mem_sInter.2 fun i hi => ?_
      rw [(hFprop i hi).2, Set.mem_setOf_eq]
      by_cases hih : i = h
      · have hie : (a i).ofLp ⬝ᵥ (x0 + t • w).ofLp = b i := by rw [hih]; exact hqH
        rw [hie]
      · have hqO : x0 + t • w ∈ O := hballO (Metric.mem_ball.2 htball)
        rw [hO] at hqO
        rcases Set.mem_iInter.1 hqO ⟨i, hi⟩ with h1' | h2
        · exact le_of_lt h1'
        · exact absurd h2 hih
    have hqs : x0 + t • w ∈ s := by
      rw [hs]
      exact ⟨hqA, h1⟩
    have hmemH : x0 + t • w ∈ {y : V3 | a h ⬝ᵥ y = b h} := by
      rw [Set.mem_setOf_eq]
      exact hqH
    have hmemH0 : x0 ∈ {y : V3 | a h ⬝ᵥ y = b h} := by
      rw [Set.mem_setOf_eq]
      exact hx0eq
    have hgen : (x0 + t • w - x0 : V3) ∈ vectorSpan ℝ (s ∩ {y : V3 | a h ⬝ᵥ y = b h}) :=
      Submodule.subset_span (Set.mem_vsub.2 ⟨x0 + t • w, ⟨hqs, hmemH⟩,
        x0, ⟨hx0s, hmemH0⟩, by rw [vsub_eq_sub]⟩)
    have hscale : w = (1 / t) • (x0 + t • w - x0) := by
      have hstep : x0 + t • w - x0 = t • w := by rw [add_sub_cancel_left]
      rw [hstep, smul_smul, one_div, inv_mul_cancel₀ ht0.ne', one_smul]
    rw [hscale]
    exact Submodule.smul_mem _ _ hgen

/-- Codimension-one property: the hyperplane slice has affine dimension
`affDim s - 1`. -/
private theorem affDim_slice {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ) (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F')
    (hsne : s ≠ ∅) (h : Set V3) (hh : h ∈ F) :
    affDim (s ∩ {x : V3 | a h ⬝ᵥ x = b h}) = affDim s - 1 := by
  classical
  obtain ⟨x0, hx0s, hx0eq, -, -⟩ := slice_cross a b hF hs hFprop hmin hsne h hh
  have hune : (s ∩ {x : V3 | a h ⬝ᵥ x = b h}).Nonempty :=
    ⟨x0, ⟨hx0s, by rw [Set.mem_setOf_eq]; exact hx0eq⟩⟩
  obtain ⟨p, z, hps, -, hzs, hpl, hzg⟩ := slice_sides a b hF hs hFprop hmin hsne h hh
  have hpaff : p ∈ (affineSpan ℝ s : Set V3) := subset_affineSpan ℝ s hps
  have hzaff : z ∈ (affineSpan ℝ s : Set V3) := hzs.1
  have hwW : z - p ∈ vectorSpan ℝ s := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hzaff hpaff
  have hwne : dotRight (a h) (z - p) ≠ 0 := by
    show a h ⬝ᵥ (z - p) ≠ 0
    rw [dot_sub]
    linarith
  have hzp : (z - p : V3) ≠ 0 := fun hc => hwne (by rw [hc]; simp)
  have hveq : vectorSpan ℝ (s ∩ {x : V3 | a h ⬝ᵥ x = b h})
      = vectorSpan ℝ s ⊓ LinearMap.ker (dotRight (a h)) :=
    vectorSpan_slice a b hF hs hFprop hmin hsne h hh
  -- codimension one of the kernel inside the direction
  have hsup : ((vectorSpan ℝ s ⊓ LinearMap.ker (dotRight (a h))) ⊔
      (ℝ ∙ (z - p) : Submodule ℝ V3)) = vectorSpan ℝ s := by
    refine le_antisymm (sup_le inf_le_left ?_) ?_
    · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 hwW)
    · intro v hv
      have hd0 : dotRight (a h) (z - p) ≠ 0 := hwne
      refine Submodule.mem_sup.2 ⟨v - (dotRight (a h) v / dotRight (a h) (z - p)) • (z - p),
        ?_, (dotRight (a h) v / dotRight (a h) (z - p)) • (z - p), ?_, ?_⟩
      · refine ⟨Submodule.sub_mem (p := vectorSpan ℝ s) hv
            (Submodule.smul_mem _ _ hwW), ?_⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.map_sub, LinearMap.map_smul,
          smul_eq_mul]
        field_simp
        ring
      · exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
      · rw [sub_add_cancel]
  have hinf : ((vectorSpan ℝ s ⊓ LinearMap.ker (dotRight (a h))) ⊓
      (ℝ ∙ (z - p) : Submodule ℝ V3)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hvS⟩ := Submodule.mem_inf.1 hv
    obtain ⟨-, hvK⟩ := Submodule.mem_inf.1 hvW
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hvS
    have hker : dotRight (a h) v = 0 := hvK
    rw [← hc, LinearMap.map_smul, smul_eq_mul] at hker
    have hcv : c = 0 := by
      rcases mul_eq_zero.1 hker with h0 | h0
      · exact h0
      · exact absurd h0 hwne
    rw [← hc, hcv, zero_smul]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq
    (vectorSpan ℝ s ⊓ LinearMap.ker (dotRight (a h))) (ℝ ∙ (z - p))
  rw [hsup, hinf, finrank_bot, finrank_span_singleton hzp] at h1
  simp only [affDim, if_neg (nonempty_iff_ne_empty.1 hune), if_neg hsne]
  rw [hveq]
  have e1 : (↑(Module.finrank ℝ (vectorSpan ℝ s)) : ℤ)
      = ↑(Module.finrank ℝ
          (vectorSpan ℝ s ⊓ LinearMap.ker (dotRight (a h)) : Submodule ℝ V3)) + 1 := by
    omega
  omega

/-! ## #13 FACET_OF_POLYHEDRON_EXPLICIT (HOL polytope.ml:4718) -/

/-- HOL `FACET_OF_POLYHEDRON_EXPLICIT`: for a polyhedron given by an
irredundant halfspace representation, the facets are exactly the hyperplane
slices cut out by single constraints of the representation. -/
theorem FACET_OF_POLYHEDRON_EXPLICIT {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ) (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F')
    (c : Set V3) :
    FacetOf c s ↔ ∃ h, h ∈ F ∧ c = s ∩ {x : V3 | a h ⬝ᵥ x = b h} := by
  classical
  have hrie : intrinsicInterior ℝ s = {y : V3 | y ∈ s ∧ ∀ i ∈ F, a i ⬝ᵥ y < b i} :=
    RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin
  constructor
  · rintro ⟨hface, hcne, hcdim⟩
    by_cases hse : s = ∅
    · rw [hse] at hface
      exact absurd (faceOf_empty.1 hface) hcne
    · have hconv : Convex ℝ s := convex_of_minrep a b hF hs hFprop
      have hcs : c ≠ s := by
        intro heq
        rw [heq] at hcdim
        have hpos : (0 : ℤ) ≤ affDim s := by
          simp only [affDim, if_neg hse]
          have hh : (0 : ℤ) ≤ (Module.finrank ℝ (vectorSpan ℝ s) : ℤ) := by
            exact_mod_cast Nat.zero_le _
          exact hh
        linarith
      -- a point of the relative interior of the facet
      obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hface.2.1
        (nonempty_iff_ne_empty.2 hcne)
      have hxc : x ∈ c := (mem_rint_iff.1 hx).1
      have hxinS : x ∈ s := hface.1 hxc
      have hxnot : x ∉ intrinsicInterior ℝ s :=
        Set.disjoint_left.1 (faceOf_disjoint_rinterior hface hcs) hxc
      -- the constraint `j` of the minimal representation that is tight at `x`
      obtain ⟨j, hjF, hj⟩ : ∃ i ∈ F, ¬(a i ⬝ᵥ x < b i) := by
        by_contra hcon
        push_neg at hcon
        exact hxnot (by rw [hrie]; exact ⟨hxinS, hcon⟩)
      have hxmem2 : x ∈ ⋂₀ F := by
        rw [hs] at hxinS
        exact hxinS.2
      have hxj : a j ⬝ᵥ x ≤ b j := by
        have h0 : x ∈ j := Set.mem_sInter.1 hxmem2 j hjF
        rw [(hFprop j hjF).2] at h0
        exact h0
      have hjeq : a j ⬝ᵥ x = b j := le_antisymm hxj (not_lt.1 hj)
      have hxu : x ∈ s ∩ {y : V3 | a j ⬝ᵥ y = b j} :=
        ⟨hxinS, by rw [Set.mem_setOf_eq]; exact hjeq⟩
      -- the facet is contained in the slice (both faces, rint's meet at x)
      have hcu : c ⊆ s ∩ {y : V3 | a j ⬝ᵥ y = b j} :=
        subset_of_faceOf (FACE_OF_POLYHEDRON_SLICE a b hF hs hFprop hmin j hjF)
          hface.1 (Set.not_disjoint_iff.2 ⟨x, hxu, hx⟩)
      -- dimension descent
      have hun : (s ∩ {y : V3 | a j ⬝ᵥ y = b j}).Nonempty := ⟨x, hxu⟩
      have hc' : c.Nonempty := nonempty_iff_ne_empty.2 hcne
      have hcdim' := affDim_slice a b hF hs hFprop hmin hse j hjF
      have hfeq2 : Module.finrank ℝ (vectorSpan ℝ c)
          = Module.finrank ℝ (vectorSpan ℝ (s ∩ {y : V3 | a j ⬝ᵥ y = b j})) := by
        have h1 : affDim c = affDim (s ∩ {y : V3 | a j ⬝ᵥ y = b j}) := by
          rw [hcdim, hcdim']
        simp only [affDim, if_neg (nonempty_iff_ne_empty.1 hc'),
          if_neg (nonempty_iff_ne_empty.1 hun)] at h1
        exact_mod_cast h1
      have hveq : vectorSpan ℝ c = vectorSpan ℝ (s ∩ {y : V3 | a j ⬝ᵥ y = b j}) :=
        Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ hcu)
          (le_of_eq hfeq2.symm)
      have heq2 : (affineSpan ℝ c : AffineSubspace ℝ V3)
          = affineSpan ℝ (s ∩ {y : V3 | a j ⬝ᵥ y = b j}) := by
        refine AffineSubspace.eq_of_direction_eq_of_nonempty_of_le ?_
          ⟨x, subset_affineSpan ℝ _ hxc⟩ (affineSpan_mono ℝ hcu)
        rw [direction_affineSpan, direction_affineSpan, hveq]
      -- the slice is contained in the facet, since their spans agree
      refine ⟨j, hjF, subset_antisymm hcu ?_⟩
      intro y hy
      refine faceOf_eq_affineInter hconv hface ⟨?_, hy.1⟩
      rw [heq2]
      exact subset_affineSpan ℝ _ hy
  · rintro ⟨j, hjF, rfl⟩
    by_cases hse : s = ∅
    · -- a nonempty `s = ∅` representation is irredundant only when `F = ∅`
      have hFe : F = ∅ := by
        by_contra hFne
        have hne0 : (∅ : Set (Set V3)) ⊂ F :=
          Set.ssubset_iff_subset_ne.2 ⟨Set.empty_subset _, Ne.symm hFne⟩
        obtain ⟨-, w, hwT, -⟩ := Set.ssubset_iff_exists.1 (hmin _ hne0)
        rw [hse, AffineSubspace.span_empty, AffineSubspace.bot_coe] at hwT
        exact absurd hwT.1 (by simp)
      exact absurd hjF (by rw [hFe]; simp)
    · obtain ⟨x0, hx0s, hx0eq, -, -⟩ := slice_cross a b hF hs hFprop hmin hse j hjF
      refine ⟨FACE_OF_POLYHEDRON_SLICE a b hF hs hFprop hmin j hjF, ?_, ?_⟩
      · exact nonempty_iff_ne_empty.1
          ⟨x0, ⟨hx0s, by rw [Set.mem_setOf_eq]; exact hx0eq⟩⟩
      · exact affDim_slice a b hF hs hFprop hmin hse j hjF

/-! ## #14 FACE_OF_POLYHEDRON_SUBSET_EXPLICIT kit -/

/-- The intrinsic interior of a nonempty affine set is the set itself. -/
private theorem rint_affine {s : Set V3} (hne : s.Nonempty)
    (haff : (affineSpan ℝ s : Set V3) = s) : intrinsicInterior ℝ s = s := by
  refine Set.ext fun x => ?_
  constructor
  · intro hmem
    exact (mem_rint_iff.1 hmem).1
  · intro hx
    exact mem_rint_iff.2 ⟨hx, 1, by norm_num, by rw [haff]; exact Set.inter_subset_right⟩

/-- The affine span of a set inside a hyperplane stays inside the hyperplane. -/
private theorem affineSpan_subset_hyperplane {t : Set V3} {a : V3} {b : ℝ}
    (hsub : t ⊆ {x : V3 | a ⬝ᵥ x = b}) (p : V3) (hp : a ⬝ᵥ p = b) :
    (affineSpan ℝ t : Set V3) ⊆ {x : V3 | a ⬝ᵥ x = b} := by
  have hT : affineSpan ℝ t ≤ AffineSubspace.mk' p (LinearMap.ker (dotRight a)) := by
    refine affineSpan_le.2 ?_
    intro q hq
    have hq' : a ⬝ᵥ q = b := hsub hq
    refine (AffineSubspace.mem_mk').2 ?_
    rw [vsub_eq_sub, LinearMap.mem_ker, LinearMap.map_sub]
    have hq2 : dotRight a q = b := hq'
    have hp2 : dotRight a p = b := hp
    rw [hq2, hp2, sub_self]
  intro q hq
  have h1 : q -ᵥ p ∈ LinearMap.ker (dotRight a) := (AffineSubspace.mem_mk').1 (hT hq)
  have h2 : a ⬝ᵥ q - a ⬝ᵥ p = 0 := by
    rw [← dot_sub]
    exact h1
  rw [Set.mem_setOf_eq]
  linarith

/-- The intersection of a finite nonempty family of faces of `s` is a face. -/
private theorem faceOf_sInter {s : Set V3} (hsc : Convex ℝ s) :
    ∀ G : Set (Set V3), G.Finite → (∀ u ∈ G, FaceOf u s) → G.Nonempty →
      FaceOf (⋂₀ G) s := by
  intro G hG
  refine Set.Finite.induction_on
    (motive := fun G _ => (∀ u ∈ G, FaceOf u s) → G.Nonempty →
      FaceOf (⋂₀ G) s) G hG ?_ ?_
  · intro _ hne
    exact absurd hne (by simp)
  · intro u G' huG' hFin ih hmem hne
    rw [Set.sInter_insert]
    by_cases hG'e : G' = ∅
    · subst hG'e
      rw [Set.sInter_empty, Set.inter_univ]
      exact hmem u (Set.mem_insert u ∅)
    · refine faceOf_inter (hmem u (Set.mem_insert u G'))
        (ih (fun v hv => hmem v (Set.mem_insert_of_mem _ hv)) ?_)
      exact Set.nonempty_iff_ne_empty.2 hG'e

/-- HOL `FACE_OF_POLYHEDRON_SUBSET_EXPLICIT` (polytope.ml:4986): every
nonempty proper face of `s` is contained in a hyperplane slice determined by
a single constraint of the irredundant representation. -/
theorem FACE_OF_POLYHEDRON_SUBSET_EXPLICIT {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ) (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F')
    {c : Set V3} (hcf : FaceOf c s) (hcne : c ≠ ∅) (hcs : c ≠ s) :
    ∃ h, h ∈ F ∧ c ⊆ s ∩ {x : V3 | a h ⬝ᵥ x = b h} := by
  classical
  haveI : Finite F := hF
  have hrie : intrinsicInterior ℝ s = {y : V3 | y ∈ s ∧ ∀ i ∈ F, a i ⬝ᵥ y < b i} :=
    RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin
  by_cases hFe : F = ∅
  · -- an affine set has no nonempty proper faces
    exfalso
    obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hcne
    have hs' : s = (affineSpan ℝ s : Set V3) := by
      refine eq_of_subset_of_subset (subset_affineSpan ℝ s) ?_
      intro x hx
      rw [hs, hFe, Set.sInter_empty, Set.inter_univ]
      exact hx
    have hrint : intrinsicInterior ℝ s = s := rint_affine ⟨y, hcf.1 hy⟩ hs'.symm
    have hdisj := faceOf_disjoint_rinterior hcf hcs
    rw [hrint] at hdisj
    exact Set.disjoint_left.1 hdisj hy (hcf.1 hy)
  · obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hcf.2.1
      (nonempty_iff_ne_empty.2 hcne)
    have hxc : x ∈ c := (mem_rint_iff.1 hx).1
    have hxinS : x ∈ s := hcf.1 hxc
    have hxnot : x ∉ intrinsicInterior ℝ s :=
      Set.disjoint_left.1 (faceOf_disjoint_rinterior hcf hcs) hxc
    obtain ⟨j, hjF, hj⟩ : ∃ i ∈ F, ¬(a i ⬝ᵥ x < b i) := by
      by_contra hcon
      push_neg at hcon
      exact hxnot (by rw [hrie]; exact ⟨hxinS, hcon⟩)
    have hxmem2 : x ∈ ⋂₀ F := by
      rw [hs] at hxinS
      exact hxinS.2
    have hxj : a j ⬝ᵥ x ≤ b j := by
      have h0 : x ∈ j := Set.mem_sInter.1 hxmem2 j hjF
      rw [(hFprop j hjF).2] at h0
      exact h0
    have hjeq : a j ⬝ᵥ x = b j := le_antisymm hxj (not_lt.1 hj)
    have hxu : x ∈ s ∩ {y : V3 | a j ⬝ᵥ y = b j} :=
      ⟨hxinS, by rw [Set.mem_setOf_eq]; exact hjeq⟩
    exact ⟨j, hjF, subset_of_faceOf (FACE_OF_POLYHEDRON_SLICE a b hF hs hFprop hmin j hjF)
      hcf.1 (Set.not_disjoint_iff.2 ⟨x, hxu, hx⟩)⟩

/-- HOL `FACE_OF_POLYHEDRON_EXPLICIT` (polytope.ml:5065): every nonempty
proper face of `s` is the intersection of the hyperplane slices (from the
irredundant representation) that contain it. -/
theorem FACE_OF_POLYHEDRON_EXPLICIT {s : Set V3} {F : Set (Set V3)}
    (a : Set V3 → V3) (b : Set V3 → ℝ) (hF : F.Finite)
    (hs : s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F')
    {c : Set V3} (hcf : FaceOf c s) (hcne : c ≠ ∅) (hcs : c ≠ s) :
    c = ⋂₀ {u | ∃ h ∈ F, u = s ∩ {y : V3 | a h ⬝ᵥ y = b h} ∧
      c ⊆ s ∩ {y : V3 | a h ⬝ᵥ y = b h}} := by
  classical
  haveI : Finite F := hF
  have hconv : Convex ℝ s := convex_of_minrep a b hF hs hFprop
  have hrie : intrinsicInterior ℝ s = {y : V3 | y ∈ s ∧ ∀ i ∈ F, a i ⬝ᵥ y < b i} :=
    RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin
  -- a point of the relative interior of the face and a tight constraint at it
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hcf.2.1
    (nonempty_iff_ne_empty.2 hcne)
  have hxc : x ∈ c := (mem_rint_iff.1 hx).1
  have hxinS : x ∈ s := hcf.1 hxc
  have hxnot : x ∉ intrinsicInterior ℝ s :=
    Set.disjoint_left.1 (faceOf_disjoint_rinterior hcf hcs) hxc
  have hxmem2 : x ∈ ⋂₀ F := by
    rw [hs] at hxinS
    exact hxinS.2
  obtain ⟨j, hjF, hj⟩ : ∃ i ∈ F, ¬(a i ⬝ᵥ x < b i) := by
    by_contra hcon
    push_neg at hcon
    exact hxnot (by rw [hrie]; exact ⟨hxinS, hcon⟩)
  have hxj : a j ⬝ᵥ x ≤ b j := by
    have h0 : x ∈ j := Set.mem_sInter.1 hxmem2 j hjF
    rw [(hFprop j hjF).2] at h0
    exact h0
  have hjeq : a j ⬝ᵥ x = b j := le_antisymm hxj (not_lt.1 hj)
  -- the family of slices containing `c`, resp. containing the rint point `x`
  set I : Set (Set V3) := {u | ∃ h ∈ F, u = s ∩ {y : V3 | a h ⬝ᵥ y = b h} ∧
    c ⊆ s ∩ {y : V3 | a h ⬝ᵥ y = b h}} with hI
  set I' : Set (Set V3) := {u | ∃ h ∈ F, u = s ∩ {y : V3 | a h ⬝ᵥ y = b h} ∧
    x ∈ s ∩ {y : V3 | a h ⬝ᵥ y = b h}} with hI'
  have hxslice : x ∈ s ∩ {y : V3 | a j ⬝ᵥ y = b j} :=
    ⟨hxinS, hjeq⟩
  have hIne : I'.Nonempty :=
    ⟨s ∩ {y : V3 | a j ⬝ᵥ y = b j}, j, hjF, rfl, hxslice⟩
  -- the two index sets define the same family of slices
  have hII' : I = I' := by
    refine Set.ext fun u => ?_
    constructor
    · intro hu
      rw [hI] at hu
      obtain ⟨h, hHF, rfl, hcsub⟩ := hu
      rw [hI']
      exact ⟨h, hHF, rfl, hcsub hxc⟩
    · intro hu
      rw [hI'] at hu
      obtain ⟨h, hHF, rfl, hxT⟩ := hu
      rw [hI]
      refine ⟨h, hHF, rfl, subset_of_faceOf
        (FACE_OF_POLYHEDRON_SLICE a b hF hs hFprop hmin h hHF) hcf.1 ?_⟩
      exact Set.not_disjoint_iff.2 ⟨x, hxT, hx⟩
  -- `⋂₀ I'` is a face of `s` whose relative interior meets the one of `c`
  have hIfin : I'.Finite :=
    (Set.Finite.image (fun h => s ∩ {y : V3 | a h ⬝ᵥ y = b h}) hF).subset fun u hu => by
      rw [hI'] at hu
      obtain ⟨h, hHF, rfl, -⟩ := hu
      exact ⟨h, hHF, rfl⟩
  have hfaceI : FaceOf (⋂₀ I') s :=
    faceOf_sInter hconv I' hIfin (fun u hu => by
      rw [hI'] at hu
      obtain ⟨h, hHF, rfl, -⟩ := hu
      exact FACE_OF_POLYHEDRON_SLICE a b hF hs hFprop hmin h hHF) hIne
  have hxmI' : x ∈ ⋂₀ I' := by
    refine Set.mem_sInter.2 fun u hu => ?_
    rw [hI'] at hu
    obtain ⟨h, hHF, rfl, hxT⟩ := hu
    exact hxT
  set O : Set V3 := ⋂ i : {y // y ∈ F},
    {p : V3 | a i.1 ⬝ᵥ p < b i.1 ∨ a i.1 ⬝ᵥ x = b i.1} with hO
  have hOopen : IsOpen O := by
    rw [hO]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hih : a i.1 ⬝ᵥ x = b i.1
    · have hset : {p : V3 | a i.1 ⬝ᵥ p < b i.1 ∨ a i.1 ⬝ᵥ x = b i.1}
          = (univ : Set V3) := by
        ext p
        simp [hih]
      rw [hset]
      exact isOpen_univ
    · have hset : {p : V3 | a i.1 ⬝ᵥ p < b i.1 ∨ a i.1 ⬝ᵥ x = b i.1}
          = {p : V3 | a i.1 ⬝ᵥ p < b i.1} := by
        ext p
        simp [hih]
      rw [hset]
      exact isOpen_lt (continuous_const.dotProduct (PiLp.continuous_ofLp 2 _))
        continuous_const
  have hxO : x ∈ O := by
    rw [hO, Set.mem_iInter]
    intro i
    by_cases hih : a i.1 ⬝ᵥ x = b i.1
    · right
      exact hih
    · left
      have h0 : x ∈ i.1 := Set.mem_sInter.1 hxmem2 i.1 i.2
      rw [(hFprop i.1 i.2).2] at h0
      exact lt_of_le_of_ne h0 hih
  obtain ⟨ε', hε0', hballO⟩ := Metric.isOpen_iff.1 hOopen x hxO
  have hxmI'rint : x ∈ intrinsicInterior ℝ (⋂₀ I') := by
    refine mem_rint_iff.2 ⟨hxmI', ε', hε0', ?_⟩
    intro y hy
    have hyaff : y ∈ (affineSpan ℝ (⋂₀ I') : Set V3) := hy.2
    have hyH : ∀ i ∈ F, a i ⬝ᵥ x = b i → a i ⬝ᵥ y = b i := by
      intro i hiF hiEq
      have hmem : s ∩ {y : V3 | a i ⬝ᵥ y = b i} ∈ I' :=
        ⟨i, hiF, rfl, ⟨hxinS, hiEq⟩⟩
      have h1 : y ∈ (affineSpan ℝ (s ∩ {y : V3 | a i ⬝ᵥ y = b i}) : Set V3) :=
        (affineSpan_mono ℝ (Set.sInter_subset_of_mem hmem)) hyaff
      exact affineSpan_subset_hyperplane Set.inter_subset_right x hiEq h1
    obtain ⟨v, hvI'⟩ := hIne
    have hvs : v ⊆ s := by
      have hv := hvI'
      rw [hI'] at hv
      obtain ⟨h, hHF, rfl, -⟩ := hv
      exact Set.inter_subset_left
    have hyA : y ∈ (affineSpan ℝ s : Set V3) :=
      (affineSpan_mono ℝ (Set.Subset.trans (Set.sInter_subset_of_mem hvI') hvs)) hyaff
    have hyF : y ∈ ⋂₀ F := by
      refine Set.mem_sInter.2 fun i hiF => ?_
      rcases Set.mem_iInter.1 (hballO hy.1) ⟨i, hiF⟩ with h1 | h2
      · rw [(hFprop i hiF).2, Set.mem_setOf_eq]
        exact le_of_lt h1
      · rw [(hFprop i hiF).2, Set.mem_setOf_eq]
        exact (hyH i hiF h2).le
    intro u hu
    rw [hI'] at hu
    obtain ⟨h, hHF, rfl, hxT⟩ := hu
    refine ⟨?_, hyH h hHF hxT.2⟩
    rw [hs]
    exact ⟨hyA, hyF⟩
  -- conclusion: the two faces agree
  refine subset_antisymm ?_ ?_
  · intro y hy
    intro u hu
    rw [hI] at hu
    obtain ⟨h, hHF, rfl, hcsub⟩ := hu
    exact hcsub hy
  · rw [hII']
    exact (faceOf_eq hcf hfaceI
      (Set.not_disjoint_iff.2 ⟨x, hx, hxmI'rint⟩)).symm.subset

/-- Skolemized minimal halfspace representation of a polyhedron. -/
private theorem minrep_skolem {s : Set V3} (hsp : polyhedron s) :
    ∃ F : Set (Set V3), F.Finite ∧ s = (affineSpan ℝ s : Set V3) ∩ ⋂₀ F ∧
      ∃ a : Set V3 → V3, ∃ b : Set V3 → ℝ,
        (∀ h ∈ F, a h ≠ 0 ∧ h = {x : V3 | a h ⬝ᵥ x ≤ b h}) ∧
        ∀ F', F' ⊂ F → s ⊂ (affineSpan ℝ s : Set V3) ∩ ⋂₀ F' := by
  classical
  obtain ⟨F, hF, hs, hFprop, hmin⟩ := POLYHEDRON_INTER_AFFINE_MINIMAL.1 hsp
  have hFprop' : ∀ h : Set V3, ∃ a : V3, ∃ b : ℝ, h ∈ F →
      a ≠ 0 ∧ h = {x : V3 | a ⬝ᵥ x ≤ b} := by
    intro h
    by_cases hh : h ∈ F
    · obtain ⟨a, b, ha, hb⟩ := hFprop h hh
      exact ⟨a, b, fun _ => ⟨ha, hb⟩⟩
    · refine ⟨0, 0, fun hF0 => absurd hF0 hh⟩
  choose a b ha hb using hFprop'
  exact ⟨F, hF, hs, a, b, fun h hh => ⟨ha h hh, hb h hh⟩, hmin⟩

/-- HOL `FACET_OF_POLYHEDRON` (polytope.ml:5190): every facet of a polyhedron
is cut out by a single supporting halfspace. -/
theorem FACET_OF_POLYHEDRON {s : Set V3} (hsp : polyhedron s) {c : Set V3}
    (hcf : FacetOf c s) :
    ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ s ⊆ {x : V3 | a ⬝ᵥ x ≤ b} ∧
      c = s ∩ {x : V3 | a ⬝ᵥ x = b} := by
  obtain ⟨F, hF, hs, a, b, hFprop, hmin⟩ := minrep_skolem hsp
  obtain ⟨j, hjF, rfl⟩ := (FACET_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin c).1 hcf
  refine ⟨a j, b j, (hFprop j hjF).1, ?_, rfl⟩
  intro x hx
  rw [hs] at hx
  have h0 : x ∈ j := Set.mem_sInter.1 hx.2 j hjF
  rw [(hFprop j hjF).2] at h0
  exact h0

/-- HOL `FACE_OF_POLYHEDRON` (polytope.ml:5217): every nonempty proper face of
a polyhedron is the intersection of the facets containing it. -/
theorem FACE_OF_POLYHEDRON {s : Set V3} (hsp : polyhedron s) {c : Set V3}
    (hcf : FaceOf c s) (hcne : c ≠ ∅) (hcs : c ≠ s) :
    c = ⋂₀ {f : Set V3 | FacetOf f s ∧ c ⊆ f} := by
  obtain ⟨F, hF, hs, a, b, hFprop, hmin⟩ := minrep_skolem hsp
  have hIeq : {f : Set V3 | FacetOf f s ∧ c ⊆ f}
      = {u | ∃ h ∈ F, u = s ∩ {y : V3 | a h ⬝ᵥ y = b h} ∧
          c ⊆ s ∩ {y : V3 | a h ⬝ᵥ y = b h}} := by
    refine Set.ext fun f => ?_
    constructor
    · rintro ⟨hfac, hcsub⟩
      obtain ⟨h, hHF, hfeq⟩ :=
        (FACET_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin f).1 hfac
      refine ⟨h, hHF, hfeq, ?_⟩
      rw [hfeq] at hcsub
      exact hcsub
    · rintro ⟨h, hHF, rfl, hcsub⟩
      exact ⟨(FACET_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin
        (s ∩ {y : V3 | a h ⬝ᵥ y = b h})).2 ⟨h, hHF, rfl⟩, hcsub⟩
  rw [hIeq]
  exact FACE_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin hcf hcne hcs

/-- HOL `RELATIVE_INTERIOR_OF_POLYHEDRON` (polytope.ml:5359): the relative
interior of a polyhedron is the polyhedron minus its facets. -/
theorem RELATIVE_INTERIOR_OF_POLYHEDRON {s : Set V3} (hsp : polyhedron s) :
    intrinsicInterior ℝ s = s \ ⋃₀ {f : Set V3 | FacetOf f s} := by
  classical
  obtain ⟨F, hF, hs, a, b, hFprop, hmin⟩ := minrep_skolem hsp
  have hrie : intrinsicInterior ℝ s = {y : V3 | y ∈ s ∧ ∀ i ∈ F, a i ⬝ᵥ y < b i} :=
    RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin
  refine Set.ext fun x => ?_
  constructor
  · intro hxmem
    rw [hrie] at hxmem
    obtain ⟨hxS', hxstrict⟩ := hxmem
    refine ⟨hxS', ?_⟩
    intro hcon
    rw [Set.mem_sUnion] at hcon
    obtain ⟨f, hf, hxf⟩ := hcon
    obtain ⟨j, hjF, rfl⟩ := (FACET_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin f).1 hf
    have hjeq : a j ⬝ᵥ x = b j := hxf.2
    exact absurd (hxstrict j hjF) (not_lt.2 hjeq.symm.le)
  · intro hxmem
    obtain ⟨hxS, hxnof⟩ := (Set.mem_sdiff x).1 hxmem
    have hxnof' : ∀ f ∈ {f : Set V3 | FacetOf f s}, x ∉ f := by
      intro f hf hxf
      exact hxnof (Set.mem_sUnion.2 ⟨f, hf, hxf⟩)
    rw [hrie]
    refine ⟨hxS, fun i hiF => ?_⟩
    by_contra hcon
    have hxle : a i ⬝ᵥ x ≤ b i := by
      have h0 : x ∈ ⋂₀ F := by
        rw [hs] at hxS
        exact hxS.2
      have h1 : x ∈ i := Set.mem_sInter.1 h0 i hiF
      rw [(hFprop i hiF).2] at h1
      exact h1
    have hieq : a i ⬝ᵥ x = b i := le_antisymm hxle (not_lt.1 hcon)
    have hsne : s ≠ ∅ := nonempty_iff_ne_empty.1 ⟨x, hxS⟩
    obtain ⟨x0, hx0s, hx0eq, -, -⟩ := slice_cross a b hF hs hFprop hmin hsne i hiF
    have hfacet : FacetOf (s ∩ {y : V3 | a i ⬝ᵥ y = b i}) s :=
      (FACET_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin
        (s ∩ {y : V3 | a i ⬝ᵥ y = b i})).2 ⟨i, hiF, rfl⟩
    exact hxnof' _ hfacet ⟨hxS, hieq⟩

end Kepler.Text
