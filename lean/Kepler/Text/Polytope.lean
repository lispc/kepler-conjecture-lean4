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


end Kepler.Text
