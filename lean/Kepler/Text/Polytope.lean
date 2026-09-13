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

/-! ## #18 FACE_OF_POLYHEDRON_SUBSET_FACET (S3) -/

/-- HOL `FACE_OF_POLYHEDRON_SUBSET_FACET` (polytope.ml:70): every nonempty
proper face of a polyhedron is contained in a facet. -/
theorem FACE_OF_POLYHEDRON_SUBSET_FACET {s : Set V3} (hsp : polyhedron s) {c : Set V3}
    (hcf : FaceOf c s) (hcne : c ≠ ∅) (hcs : c ≠ s) :
    ∃ f : Set V3, FacetOf f s ∧ c ⊆ f := by
  by_contra hcon
  push_neg at hcon
  have hF : {f : Set V3 | FacetOf f s ∧ c ⊆ f} = ∅ :=
    Set.ext fun f => ⟨fun h => hcon f h.1 h.2, by simp⟩
  have hce : c = (univ : Set V3) := by
    rw [FACE_OF_POLYHEDRON hsp hcf hcne hcs, hF, Set.sInter_empty]
  have hsU : (univ : Set V3) ⊆ s := by rw [← hce]; exact hcf.1
  exact hcs (hce.trans (subset_antisymm (subset_univ s) hsU).symm)

/-! ## #19 Finiteness of faces, facets and extreme points (S3) -/

/-- HOL `FINITE_POLYHEDRON_FACETS` (polytope.ml:157): a polyhedron has
finitely many facets — every facet is a hyperplane slice of the irredundant
representation. -/
theorem FINITE_POLYHEDRON_FACETS {s : Set V3} (hsp : polyhedron s) :
    {f : Set V3 | FacetOf f s}.Finite := by
  obtain ⟨F, hF, hs, a, b, hFprop, hmin⟩ := minrep_skolem hsp
  refine Set.Finite.subset (hF.image fun h => s ∩ {y : V3 | a h ⬝ᵥ y = b h}) ?_
  intro f hf
  obtain ⟨j, hjF, rfl⟩ := (FACET_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin f).1 hf
  exact Set.mem_image_of_mem _ hjF

/-- HOL `FINITE_POLYHEDRON_FACES` (polytope.ml:121): a polyhedron has finitely
many faces — every nonempty proper face is an intersection of hyperplane
slices indexed by a subset of the constraint set. -/
theorem FINITE_POLYHEDRON_FACES {s : Set V3} (hsp : polyhedron s) :
    {f : Set V3 | FaceOf f s}.Finite := by
  classical
  obtain ⟨F, hF, hs, a, b, hFprop, hmin⟩ := minrep_skolem hsp
  have hP : {T : Set (Set V3) | T ⊆ F}.Finite := Set.Finite.powerset hF
  have hfin : ({⋂₀ {u : Set V3 | ∃ h ∈ T, u = s ∩ {y : V3 | a h ⬝ᵥ y = b h}} |
      T ∈ {T : Set (Set V3) | T ⊆ F}}).Finite :=
    hP.image fun T => ⋂₀ {u : Set V3 | ∃ h ∈ T, u = s ∩ {y : V3 | a h ⬝ᵥ y = b h}}
  refine (hfin.insert (∅ : Set V3)).insert s |>.subset ?_
  intro c hc
  by_cases hc0 : c = ∅
  · exact Or.inr (Set.mem_insert_iff.2 (Or.inl hc0))
  by_cases hcs : c = s
  · exact Set.mem_insert_iff.2 (Or.inl hcs)
  refine Or.inr (Or.inr ⟨{h : Set V3 | h ∈ F ∧ c ⊆ s ∩ {y : V3 | a h ⬝ᵥ y = b h}},
    fun h hh => hh.1, ?_⟩)
  have hface := FACE_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin hc hc0 hcs
  have hTeq : c = ⋂₀ {u : Set V3 | ∃ h ∈ {h : Set V3 | h ∈ F ∧
        c ⊆ s ∩ {y : V3 | a h ⬝ᵥ y = b h}},
        u = s ∩ {y : V3 | a h ⬝ᵥ y = b h}} :=
    hface.trans (congrArg Set.sInter (Set.ext fun u => by
      constructor
      · rintro ⟨h, hFh, rfl, hcsub⟩
        exact ⟨h, ⟨hFh, hcsub⟩, rfl⟩
      · rintro ⟨h, ⟨hFh, hcsub⟩, rfl⟩
        exact ⟨h, hFh, rfl, hcsub⟩))
  exact hTeq.symm

/-- HOL `FINITE_POLYHEDRON_EXTREME_POINTS` (polytope.ml:170): a polyhedron has
finitely many extreme points — they are the singleton faces. -/
theorem FINITE_POLYHEDRON_EXTREME_POINTS {s : Set V3} (hsp : polyhedron s) :
    {v : V3 | v ∈ Set.extremePoints ℝ s}.Finite := by
  have h1 : ∀ v : V3, v ∈ Set.extremePoints ℝ s ↔ FaceOf ({v} : Set V3) s :=
    fun v => faceOf_sing.symm
  have h2 : {v : V3 | v ∈ Set.extremePoints ℝ s}
      = (fun v : V3 => ({v} : Set V3)) ⁻¹' {f : Set V3 | FaceOf f s} := by
    ext v
    simpa only [Set.mem_setOf_eq, Set.mem_preimage] using h1 v
  rw [h2]
  refine Set.Finite.preimage (fun x _ y _ h => by simpa using h)
    (FINITE_POLYHEDRON_FACES hsp)

/-! ## #20 Exposed faces (S3) -/

/-- HOL `exposed_face_of` (polytope1.ml:980). Mathlib's `IsExposed` has a
different shape (dual-pairing functional, empty set not exposed), so the HOL
halfspace formulation is kept verbatim. -/
def exposedFaceOf (t s : Set V3) : Prop :=
  FaceOf t s ∧ ∃ a : V3, ∃ b : ℝ, s ⊆ {x : V3 | a ⬝ᵥ x ≤ b} ∧
    t = s ∩ {x : V3 | a ⬝ᵥ x = b}

private theorem dot_lzero (x : V3) : (0 : V3) ⬝ᵥ x = 0 := by
  show (0 : Fin 3 → ℝ) ⬝ᵥ x.ofLp = 0
  exact zero_dotProduct _

private theorem dot_smul_left (r : ℝ) (a x : V3) : (r • a) ⬝ᵥ x = r * (a ⬝ᵥ x) := by
  show (r • a.ofLp) ⬝ᵥ x.ofLp = r * (a.ofLp ⬝ᵥ x.ofLp)
  exact smul_dotProduct r _ _

private theorem dot_sum_left (K : Finset (Set V3)) (g : Set V3 → V3) (x : V3) :
    WithLp.ofLp (∑ u ∈ K, g u) ⬝ᵥ x.ofLp = ∑ u ∈ K, g u ⬝ᵥ x := by
  rw [dotProduct_comm, WithLp.ofLp_sum, dotProduct_sum]
  exact Finset.sum_congr rfl fun u _ => dotProduct_comm _ _

/-- HOL `EMPTY_EXPOSED_FACE_OF` (polytope1.ml:982). -/
theorem EMPTY_EXPOSED_FACE_OF (s : Set V3) : exposedFaceOf ∅ s := by
  refine ⟨empty_faceOf s, 0, 1, fun x _ => ?_, ?_⟩
  · have h0 : (0 : V3) ⬝ᵥ x = 0 := dot_lzero x
    show (0 : V3) ⬝ᵥ x ≤ 1
    rw [h0]
    norm_num
  · refine Set.ext fun x => ?_
    have h0 : (0 : V3) ⬝ᵥ x = 0 := dot_lzero x
    show False ↔ x ∈ s ∩ {y : V3 | (0 : V3) ⬝ᵥ y = 1}
    simp

/-- HOL `EXPOSED_FACE_OF_REFL` (polytope1.ml:994). -/
theorem EXPOSED_FACE_OF_REFL {s : Set V3} (hs : Convex ℝ s) : exposedFaceOf s s := by
  refine ⟨FaceOf.refl hs, 0, 0, fun x _ => ?_, ?_⟩
  · have h0 : (0 : V3) ⬝ᵥ x = 0 := dot_lzero x
    show (0 : V3) ⬝ᵥ x ≤ 0
    rw [h0]
  · refine Set.ext fun x => ?_
    have h0 : (0 : V3) ⬝ᵥ x = 0 := dot_lzero x
    show x ∈ s ↔ x ∈ s ∩ {y : V3 | (0 : V3) ⬝ᵥ y = 0}
    simp [h0]

/-- The supporting-hyperplane slice of a convex set is a face. -/
private theorem faceOf_hyperplane_slice {s : Set V3} (hs : Convex ℝ s) {a : V3} {b : ℝ}
    (hsub : s ⊆ {x : V3 | a ⬝ᵥ x ≤ b}) : FaceOf (s ∩ {x : V3 | a ⬝ᵥ x = b}) s := by
  have hcvxH : Convex ℝ {x : V3 | a ⬝ᵥ x = b} := by
    intro x hx y hy u v hu hv hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have h : a ⬝ᵥ (u • x + v • y) = u * (a ⬝ᵥ x) + v * (a ⬝ᵥ y) := by
      rw [dot_add, dot_smul, dot_smul]
    rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul, h, hx, hy]
    have h3 : u * b + v * b = b := by
      have h4 : (u + v) * b = b := by rw [hab, one_mul]
      rwa [add_mul] at h4
    exact h3
  refine ⟨Set.inter_subset_left, hs.inter hcvxH, ?_⟩
  intro u v x hu hv hx hseg
  obtain ⟨l, m, hl, hm, hlm, hxe⟩ := hseg
  have hxe' : l • u.ofLp + m • v.ofLp = x.ofLp :=
    congrArg (fun z : V3 => z.ofLp) hxe
  have hu0 : a ⬝ᵥ u ≤ b := hsub hu
  have hv0 : a ⬝ᵥ v ≤ b := hsub hv
  have hkey : a ⬝ᵥ (l • u + m • v) = l * (a ⬝ᵥ u) + m * (a ⬝ᵥ v) := by
    rw [dot_add, dot_smul, dot_smul]
  have hx0 : a.ofLp ⬝ᵥ (l • u.ofLp + m • v.ofLp) = b := by
    rw [hxe']
    exact hx.2
  rw [hkey] at hx0
  have hab : l * (a ⬝ᵥ u) + m * (a ⬝ᵥ v) = l * b + m * b := by
    rw [hx0, ← add_mul, hlm, one_mul]
  have h1 : l * (a ⬝ᵥ u) ≤ l * b := mul_le_mul_of_nonneg_left hu0 hl.le
  have h2 : m * (a ⬝ᵥ v) ≤ m * b := mul_le_mul_of_nonneg_left hv0 hm.le
  have hu' : a ⬝ᵥ u = b := mul_left_cancel₀ hl.ne' (by linarith)
  have hv' : a ⬝ᵥ v = b := mul_left_cancel₀ hm.ne' (by linarith)
  exact ⟨⟨hu, hu'⟩, ⟨hv, hv'⟩⟩

/-- HOL `EXPOSED_FACE_OF` (polytope1.ml:998). -/
theorem EXPOSED_FACE_OF {s t : Set V3} :
    exposedFaceOf t s ↔ FaceOf t s ∧ (t = ∅ ∨ t = s ∨
      ∃ a : V3, ∃ b : ℝ, a ≠ 0 ∧ s ⊆ {x : V3 | a ⬝ᵥ x ≤ b} ∧
        t = s ∩ {x : V3 | a ⬝ᵥ x = b}) := by
  constructor
  · rintro ⟨hface, a, b, hsub, hte⟩
    refine ⟨hface, ?_⟩
    by_cases ha : a = 0
    · rw [ha] at hte
      rcases eq_or_ne b 0 with hb | hb
      · right
        left
        rw [hte, hb]
        refine Set.ext fun x => ?_
        have h0 : (0 : V3) ⬝ᵥ x = 0 := dot_lzero x
        show x ∈ s ∩ {y : V3 | (0 : V3) ⬝ᵥ y = 0} ↔ x ∈ s
        simp [h0]
      · left
        rw [hte]
        refine Set.ext fun x => ?_
        have h0 : (0 : V3) ⬝ᵥ x = 0 := dot_lzero x
        show x ∈ s ∩ {y : V3 | (0 : V3) ⬝ᵥ y = b} ↔ False
        refine iff_of_false ?_ fun hc => hc
        rintro ⟨-, hc⟩
        have h1 : (0 : V3) ⬝ᵥ x = b := hc
        exact hb (h1.symm.trans h0)
    · exact Or.inr (Or.inr ⟨a, b, ha, hsub, hte⟩)
  · rintro ⟨hface, hdisj⟩
    rcases hdisj with rfl | rfl | ⟨a, b, ha, hsub, hte⟩
    · exact EMPTY_EXPOSED_FACE_OF s
    · exact EXPOSED_FACE_OF_REFL hface.2.1
    · exact And.intro hface ⟨a, b, hsub, hte⟩

/-- HOL `EXPOSED_FACE_OF_POLYHEDRON` (polytope.ml:95): in a polyhedron every
face is exposed. -/
theorem EXPOSED_FACE_OF_POLYHEDRON {s : Set V3} (hsp : polyhedron s) {t : Set V3} :
    exposedFaceOf t s ↔ FaceOf t s := by
  refine ⟨fun h => h.1, fun hface => ?_⟩
  by_cases ht0 : t = ∅
  · rw [ht0]
    exact EMPTY_EXPOSED_FACE_OF s
  by_cases hts : t = s
  · subst hts
    exact EXPOSED_FACE_OF_REFL hface.2.1
  classical
  obtain ⟨f₀, hf₀, hf₀t⟩ := FACE_OF_POLYHEDRON_SUBSET_FACET hsp hface ht0 hts
  have hFfin : {f : Set V3 | FacetOf f s ∧ t ⊆ f}.Finite :=
    Set.Finite.subset (FINITE_POLYHEDRON_FACETS hsp) fun f hf => hf.1
  have hFI : t = ⋂₀ {f : Set V3 | FacetOf f s ∧ t ⊆ f} := FACE_OF_POLYHEDRON hsp hface ht0 hts
  have hFBtot : ∀ f : Set V3, ∃ a : V3, ∃ c : ℝ, FacetOf f s →
      (∀ x ∈ s, a ⬝ᵥ x ≤ c) ∧ f = s ∩ {x : V3 | a ⬝ᵥ x = c} := by
    intro f
    by_cases hf : FacetOf f s
    · obtain ⟨a, c, -, h1, h2⟩ := FACET_OF_POLYHEDRON hsp hf
      exact ⟨a, c, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, 0, fun hf' => absurd hf' hf⟩
  choose af cf haf using hFBtot
  set K := hFfin.toFinset with hKdef
  have hKne : K.Nonempty := ⟨f₀, hFfin.mem_toFinset.2 ⟨hf₀, hf₀t⟩⟩
  have hnpos : (0:ℝ) < (K.card : ℝ) :=
    Nat.cast_pos.2 (Finset.card_pos.2 hKne)
  set w : ℝ := (K.card : ℝ)⁻¹ with hwdef
  have hwn : 0 < w := inv_pos.2 hnpos
  have hcard : ∑ u ∈ K, w = 1 := by
    rw [hwdef, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hnpos.ne']
  set g : V3 := ∑ u ∈ K, w • af u with hgdef
  set d : ℝ := ∑ u ∈ K, w * cf u with hddef
  have hmem : ∀ u ∈ K, FacetOf u s ∧ t ⊆ u := fun u hu => hFfin.mem_toFinset.1 hu
  have hclaim1 : ∀ x ∈ s, g ⬝ᵥ x ≤ d := by
    intro x hx
    rw [hgdef, hddef, dot_sum_left]
    refine Finset.sum_le_sum fun u hu => ?_
    rw [dot_smul_left]
    exact mul_le_mul_of_nonneg_left ((haf u (hmem u hu).1).1 x hx) hwn.le
  have hclaim2 : ∀ x ∈ t, g ⬝ᵥ x = d := by
    intro x hx
    rw [hgdef, hddef, dot_sum_left]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [dot_smul_left]
    have hxu : x ∈ s ∩ {y : V3 | af u ⬝ᵥ y = cf u} := by
      have h1 : x ∈ u := (hmem u hu).2 hx
      rwa [(haf u (hmem u hu).1).2] at h1
    have hxeq : af u ⬝ᵥ x = cf u := hxu.2
    rw [hxeq]
  have hclaim3 : ∀ x ∈ s, g ⬝ᵥ x = d → x ∈ ⋂₀ {f : Set V3 | FacetOf f s ∧ t ⊆ f} := by
    intro x hx hgx
    refine Set.mem_sInter.2 fun u hu => ?_
    have hgsum : g ⬝ᵥ x = ∑ v ∈ K, w * (af v ⬝ᵥ x) := by
      rw [hgdef, dot_sum_left]
      exact Finset.sum_congr rfl fun v _ => dot_smul_left w (af v) x
    have hnonneg : ∀ v ∈ K, 0 ≤ w * (cf v - af v ⬝ᵥ x) := fun v hv =>
      mul_nonneg hwn.le (sub_nonneg.2 ((haf v (hmem v hv).1).1 x hx))
    have hsum0 : ∑ v ∈ K, (w * (cf v - af v ⬝ᵥ x)) = 0 := by
      have h1 : ∑ v ∈ K, (w * (cf v - af v ⬝ᵥ x))
          = ∑ v ∈ K, (w * cf v) - ∑ v ∈ K, (w * (af v ⬝ᵥ x)) := by
        rw [← Finset.sum_sub_distrib (f := fun v => w * cf v)
          (g := fun v => w * (af v ⬝ᵥ x))]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [h1, ← hgsum, hgx, hddef]
      ring
    have hcfv : af u ⬝ᵥ x = cf u := by
      have huK : u ∈ K := hFfin.mem_toFinset.2 hu
      have h0 := Finset.sum_eq_zero_iff_of_nonneg hnonneg |>.1 hsum0 u huK
      exact sub_eq_zero.mp ((mul_eq_zero.1 h0).resolve_left hwn.ne') |>.symm
    have hu' := hmem u (hFfin.mem_toFinset.2 hu)
    rw [(haf u hu'.1).2]
    exact ⟨hx, hcfv⟩
  refine ⟨hface, g, d, hclaim1, ?_⟩
  rw [hFI]
  refine Set.ext fun x => ?_
  constructor
  · intro hx
    have hxs : x ∈ s := by
      have h1 := Set.mem_sInter.1 hx f₀ ⟨hf₀, hf₀t⟩
      rw [(haf f₀ hf₀).2] at h1
      exact h1.1
    exact ⟨hxs, hclaim2 x (by rw [hFI]; exact hx)⟩
  · rintro ⟨hxs, hgx⟩
    exact hclaim3 x hxs hgx

/-- HOL `FACE_OF_POLYHEDRON_POLYHEDRON` (polytope.ml:103): a face of a
polyhedron is a polyhedron. -/
theorem FACE_OF_POLYHEDRON_POLYHEDRON {s : Set V3} (hsp : polyhedron s) {c : Set V3}
    (hcf : FaceOf c s) : polyhedron c := by
  by_cases hc0 : c = ∅
  · rw [hc0]
    exact POLYHEDRON_EMPTY
  by_cases hcs : c = s
  · rw [hcs]
    exact hsp
  obtain ⟨F, hF, hs, a, b, hFprop, hmin⟩ := minrep_skolem hsp
  rw [FACE_OF_POLYHEDRON_EXPLICIT a b hF hs hFprop hmin hcf hc0 hcs]
  refine POLYHEDRON_INTERS (Set.Finite.subset (hF.image fun h =>
    s ∩ {y : V3 | a h ⬝ᵥ y = b h}) ?_) ?_
  · rintro u ⟨h, hFh, rfl, -⟩
    exact Set.mem_image_of_mem _ hFh
  · rintro u ⟨h, hFh, rfl, -⟩
    exact POLYHEDRON_INTER hsp (POLYHEDRON_HYPERPLANE (hFprop h hFh).1 (b h))

/-! ## #21 Existence of extreme points (S3) -/

/-- HOL `EXTREME_POINT_EXISTS_CONVEX` (polytope1.ml:1636): a nonempty compact
set has an extreme point (Krein–Milman, Mathlib `IsCompact.extremePoints_nonempty`;
convexity is not needed for existence). -/
theorem EXTREME_POINT_EXISTS_CONVEX {s : Set V3} (hcomp : IsCompact s)
    (_hcvx : Convex ℝ s) (hne : s.Nonempty) :
    ∃ x : V3, x ∈ Set.extremePoints ℝ s :=
  hcomp.extremePoints_nonempty hne

/-! ## #22 Segment family (S3) -/

private theorem leftEndpoint_extreme (a b : V3) :
    a ∈ Set.extremePoints ℝ (segment ℝ a b) := by
  rw [mem_extremePoints_iff_forall_segment]
  refine ⟨left_mem_segment ℝ a b, fun y hy z hz hseg => ?_⟩
  obtain ⟨l₁, m₁, hl₁, hm₁, hlm₁, hye⟩ := hy
  obtain ⟨l₂, m₂, hl₂, hm₂, hlm₂, hze⟩ := hz
  obtain ⟨l, m, hl, hm, hlm, hxe⟩ := hseg
  by_cases hab : a = b
  · left
    rw [hab] at hye ⊢
    rw [← add_smul, hlm₁, one_smul] at hye
    exact hye.symm
  · have hxeq : (l * l₁ + m * l₂) • a + (l * m₁ + m * m₂) • b = a := by
      linear_combination (norm := module) hxe + l • hye + m • hze
    have hAB : l * l₁ + m * l₂ + (l * m₁ + m * m₂) = 1 := by
      have e1 : l * l₁ + m * l₂ + (l * m₁ + m * m₂)
          = l * (l₁ + m₁) + m * (l₂ + m₂) := by ring
      rw [e1, hlm₁, hlm₂, mul_one, mul_one]
      exact hlm
    have hB : (l * m₁ + m * m₂) • (b - a) = 0 := by
      have hA' : l * l₁ + m * l₂ = 1 - (l * m₁ + m * m₂) := by linarith
      rw [hA'] at hxeq
      linear_combination (norm := module) hxeq
    rcases hl.eq_or_lt with h0l | hl0
    · -- l = 0: m = 1, so a = z
      subst h0l
      rw [zero_smul, zero_add] at hxe
      rw [zero_add] at hlm
      rw [hlm, one_smul] at hxe
      right
      exact hxe
    · -- 0 < l: m₁ = 0 and y = a
      have hB0 : l * m₁ + m * m₂ = 0 := by
        rcases smul_eq_zero.1 hB with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h).symm hab
      have hP1 : l * m₁ = 0 := by
        have hnn1 : 0 ≤ l * m₁ := mul_nonneg hl0.le hm₁
        have hnn2 : 0 ≤ m * m₂ := mul_nonneg hm hm₂
        linarith [hB0, hnn1, hnn2]
      have hm₁0 : m₁ = 0 := (mul_eq_zero.1 hP1).resolve_left hl0.ne'
      left
      rw [← hye, hm₁0, zero_smul, add_zero, show l₁ = 1 from by linarith, one_smul]

private theorem leftEndpoint_extreme' (a b : V3) :
    a ∈ segment ℝ a b ∧ ∀ y ∈ segment ℝ a b, ∀ z ∈ segment ℝ a b,
      a ∈ segment ℝ y z → y = a ∨ z = a :=
  mem_extremePoints_iff_forall_segment.1 (leftEndpoint_extreme a b)

/-- HOL `EXTREME_POINT_OF_SEGMENT` (polytope1.ml:1865): the extreme points of
the closed segment `[a, b]` are its endpoints. -/
theorem EXTREME_POINT_OF_SEGMENT (a b x : V3) :
    x ∈ Set.extremePoints ℝ (segment ℝ a b) ↔ x = a ∨ x = b := by
  rw [mem_extremePoints_iff_forall_segment]
  constructor
  · rintro ⟨hmem, hcond⟩
    obtain ⟨l, m, hl, hm, hlm, hxe⟩ := hmem
    rcases eq_or_lt_of_le hl with rfl | hl0
    · right
      rw [← hxe, zero_smul, zero_add, show m = 1 from by linarith, one_smul]
    · rcases eq_or_lt_of_le hm with rfl | hm0
      · left
        rw [← hxe, zero_smul, add_zero, show l = 1 from by linarith, one_smul]
      · rcases hcond a (left_mem_segment ℝ a b) b (right_mem_segment ℝ a b)
          ⟨l, m, le_of_lt hl0, le_of_lt hm0, hlm, hxe⟩ with hx | hx
        · exact Or.inl hx.symm
        · exact Or.inr hx.symm
  · rintro (h | h)
    · rw [h]
      exact leftEndpoint_extreme' a b
    · rw [h, segment_symm]
      exact leftEndpoint_extreme' b a

/-- HOL `SEGMENT_FACE_OF` (polytope1.ml:1966): if the closed segment `[a, b]`
is a face then `a` and `b` are extreme points. -/
theorem SEGMENT_FACE_OF {s : Set V3} {a b : V3} (h : FaceOf (segment ℝ a b) s) :
    a ∈ Set.extremePoints ℝ s ∧ b ∈ Set.extremePoints ℝ s := by
  have h1 : FaceOf {a} (segment ℝ a b) :=
    faceOf_sing.2 ((EXTREME_POINT_OF_SEGMENT a b a).2 (Or.inl rfl))
  have h2 : FaceOf {b} (segment ℝ a b) :=
    faceOf_sing.2 ((EXTREME_POINT_OF_SEGMENT a b b).2 (Or.inr rfl))
  exact ⟨faceOf_sing.1 (FaceOf.trans h1 h), faceOf_sing.1 (FaceOf.trans h2 h)⟩

/-- HOL `SEGMENT_EDGE_OF` (polytope1.ml:1973). -/
theorem SEGMENT_EDGE_OF {s : Set V3} {a b : V3} (h : edgeOf (segment ℝ a b) s) :
    a ≠ b ∧ a ∈ Set.extremePoints ℝ s ∧ b ∈ Set.extremePoints ℝ s := by
  refine ⟨?_, (SEGMENT_FACE_OF h.1).1, (SEGMENT_FACE_OF h.1).2⟩
  rintro rfl
  rw [segment_same] at h
  exact absurd h.2 (by rw [affDim_singleton]; norm_num)

/-- Bridge: the closed segment `[a, b]` carries an edge exactly when `a ≠ b`
and it is a face (HOL `edge_of` + `AFF_DIM_SEGMENT`). -/
theorem edgeOf_segment_iff {s : Set V3} {a b : V3} :
    edgeOf (segment ℝ a b) s ↔ a ≠ b ∧ FaceOf (segment ℝ a b) s := by
  rw [edgeOf]
  constructor
  · rintro ⟨hf, hdim⟩
    refine ⟨?_, hf⟩
    rintro rfl
    rw [segment_same, affDim_singleton] at hdim
    norm_num at hdim
  · rintro ⟨hne, hf⟩
    exact ⟨hf, (affDim_segment a b).2 hne⟩

/-! ## #23 Polytope basics (S3) -/

/-- HOL `polytope` (polytope1.ml): a polytope is the convex hull of a finite
set. -/
def polytope (s : Set V3) : Prop :=
  ∃ F : Set V3, F.Finite ∧ convexHull ℝ F = s

/-- HOL `POLYTOPE_IMP_CONVEX`. -/
theorem POLYTOPE_IMP_CONVEX {s : Set V3} (h : polytope s) : Convex ℝ s := by
  obtain ⟨F, -, rfl⟩ := h
  exact convex_convexHull ℝ F

/-- HOL `POLYTOPE_IMP_BOUNDED`. -/
theorem POLYTOPE_IMP_BOUNDED {s : Set V3} (h : polytope s) : Bornology.IsBounded s := by
  obtain ⟨F, hF, rfl⟩ := h
  exact isBounded_convexHull.2 hF.isBounded

/-- HOL `POLYTOPE_IMP_CLOSED`. -/
theorem POLYTOPE_IMP_CLOSED {s : Set V3} (h : polytope s) : IsClosed s := by
  obtain ⟨F, hF, rfl⟩ := h
  exact hF.isClosed_convexHull ℝ

/-- HOL `POLYTOPE_IMP_COMPACT` (the compactness half of `POLYTOPE_IMP_COMPACT`
in polytope1.ml, from closed + bounded in finite dimension). -/
theorem POLYTOPE_IMP_COMPACT {s : Set V3} (h : polytope s) : IsCompact s := by
  obtain ⟨F, hF, rfl⟩ := h
  exact hF.isCompact_convexHull ℝ

/-! ## #24 Collinear faces of a polyhedron (S3) -/

/-- Scaling step for HOL `POLYHEDRON_COLLINEAR_FACES_STRONG`
(flyspeck_multivariate.ml:6820): the case `s ≤ t`. -/
private theorem collinear_faces_aux {P f f' : Set V3} (hsp : polyhedron P)
    (h0 : (0:V3) ∈ intrinsicInterior ℝ P) (hf : FaceOf f P) (hfn : f ≠ P)
    (hf' : FaceOf f' P) (hfn' : f' ≠ P) {p q : V3} (hpf : p ∈ f) (hqf : q ∈ f')
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hle : s ≤ t) (hst : s • p = t • q) :
    s = t := by
  by_contra hne
  push_neg at hne
  have hlt : s < t := lt_of_le_of_ne hle hne
  have hf'ne : f' ≠ ∅ := nonempty_iff_ne_empty.1 ⟨q, hqf⟩
  obtain ⟨g, hgf, hsub⟩ := FACE_OF_POLYHEDRON_SUBSET_FACET hsp hf' hf'ne hfn'
  obtain ⟨hface, -, hdim⟩ := hgf
  have h0g : (0:V3) ∉ g := by
    intro h0g
    have hPg : P ⊆ g := by
      refine subset_of_faceOf hface (subset_refl P) ?_
      exact Set.not_disjoint_iff.2 ⟨0, h0g, h0⟩
    have hge : g = P := subset_antisymm hface.1 hPg
    rw [hge] at hdim
    linarith
  have hqg : q ∈ g := hsub hqf
  have hpP : p ∈ P := hf.1 hpf
  have hzp : (0:V3) ∈ P := intrinsicInterior_subset h0
  have hqseg : q ∈ openSegment ℝ 0 p := by
    have htp : t ≠ 0 := ne_of_gt ht
    have hqeq : (s / t) • p = q := by
      rw [div_eq_inv_mul, ← smul_smul, ← hst.symm, inv_smul_smul₀ htp]
    exact ⟨1 - s / t, s / t, (by linarith [(div_lt_one ht).2 hlt]), by positivity, by ring, by
      rw [smul_zero, zero_add, hqeq]⟩
  exact h0g (hface.2.2 0 p q hzp hpP hqg hqseg).1

/-- HOL `POLYHEDRON_COLLINEAR_FACES_STRONG` (flyspeck_multivariate.ml:6820):
two proper faces of a polyhedron whose relative interior contains the origin
meet the rays from the origin in the same radial parameter. -/
theorem POLYHEDRON_COLLINEAR_FACES_STRONG {P f f' : Set V3} (hsp : polyhedron P)
    (h0 : (0:V3) ∈ intrinsicInterior ℝ P) (hf : FaceOf f P) (hfn : f ≠ P)
    (hf' : FaceOf f' P) (hfn' : f' ≠ P) {p q : V3} (hpf : p ∈ f) (hqf : q ∈ f')
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s • p = t • q) : s = t := by
  rcases le_total s t with hle | hle
  · exact collinear_faces_aux hsp h0 hf hfn hf' hfn' hpf hqf hs ht hle hst
  · exact (collinear_faces_aux hsp h0 hf' hfn' hf hfn hqf hpf ht hs hle
      hst.symm).symm

/-- HOL `POLYHEDRON_COLLINEAR_FACES` (flyspeck_multivariate.ml:6875), with
the HOL-verbatim topological interior premise. -/
theorem POLYHEDRON_COLLINEAR_FACES {P f f' : Set V3} (hsp : polyhedron P)
    (h0 : (0:V3) ∈ interior P) (hf : FaceOf f P) (hfn : f ≠ P)
    (hf' : FaceOf f' P) (hfn' : f' ≠ P) {p q : V3} (hpf : p ∈ f) (hqf : q ∈ f')
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s • p = t • q) : s = t :=
  POLYHEDRON_COLLINEAR_FACES_STRONG hsp (interior_subset_intrinsicInterior h0)
    hf hfn hf' hfn' hpf hqf hs ht hst

/-! ## #25 Cones `aff_ge {z} s` over a convex hull (S3) -/

private theorem affGe_convex {z : V3} {s : Set V3} (hs : s.Finite) :
    Convex ℝ (affGe {z} s) := by
  classical
  rintro u hu v hv c d hc hd hcd
  obtain ⟨f, hK, hfsum, hfsign, hone⟩ := hu
  obtain ⟨g, hK', hgsum, hgsign, hone'⟩ := hv
  have hKK : hK.toFinset = hK'.toFinset := by rw [proof_irrel hK hK']
  refine ⟨fun w => c * f w + d * g w, hK, ?_, ?_, ?_⟩
  · rw [hfsum, hgsum, ← hKK]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
    exact Finset.sum_add_distrib.symm.trans
      (Finset.sum_congr rfl fun x _ => (add_smul (c * f x) (d * g x) x).symm)
  · intro w hw
    exact add_nonneg (mul_nonneg hc (hfsign w hw)) (mul_nonneg hd (hgsign w hw))
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hone, hone', mul_one]
    exact hcd

private theorem mem_affGe_base {z : V3} {s : Set V3} (hs : s.Finite) :
    z ∈ affGe {z} s := by
  have hK : ({z} ∪ s).Finite := (Set.finite_singleton z).union hs
  have hzK : z ∈ hK.toFinset := by simpa using Set.mem_union_left _ (Set.mem_singleton z)
  refine ⟨fun w => if w = z then 1 else 0, hK, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single_of_mem z hzK (fun b hb hne => by
      have hbm := (Set.Finite.mem_toFinset hK).1 hb
      rcases (Set.mem_union b {z} s).1 hbm with h | h
      · exact absurd h hne
      · simp [hne])]
    simp
  · intro w hw
    by_cases h : w = z <;> simp [h]
  · rw [Finset.sum_eq_single_of_mem z hzK (fun b hb hne => by
      have hbm := (Set.Finite.mem_toFinset hK).1 hb
      rcases (Set.mem_union b {z} s).1 hbm with h | h
      · exact absurd h hne
      · simp [hne])]
    simp

private theorem mem_affGe_of_mem {z : V3} {s : Set V3} {y : V3} (hs : s.Finite)
    (hzs : z ∉ s) (hy : y ∈ s) : y ∈ affGe {z} s := by
  have hzy : z ≠ y := fun hc => hzs (hc ▸ hy)
  have hK : ({z} ∪ s).Finite := (Set.finite_singleton z).union hs
  have hyK : y ∈ hK.toFinset := by simpa using Set.mem_union_right ({z} : Set V3) hy
  refine ⟨fun w => if w = y then 1 else 0, hK, ?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single_of_mem y hyK (fun b hb hne => by
      have hbm := (Set.Finite.mem_toFinset hK).1 hb
      rcases (Set.mem_union b {z} s).1 hbm with h | h
      · show (if b = y then (1:ℝ) else 0) • b = 0
        rw [if_neg (fun hc => by rw [h] at hc; exact hzy hc), zero_smul]
      · show (if b = y then (1:ℝ) else 0) • b = 0
        rw [if_neg hne, zero_smul])]
    simp
  · intro w hw
    by_cases h : w = y <;> simp [h]
  · rw [Finset.sum_eq_single_of_mem y hyK (fun b hb hne => by
      have hbm := (Set.Finite.mem_toFinset hK).1 hb
      rcases (Set.mem_union b {z} s).1 hbm with h | h
      · show (if b = y then (1:ℝ) else 0) = 0
        rw [if_neg (fun hc => by rw [h] at hc; exact hzy hc)]
      · show (if b = y then (1:ℝ) else 0) = 0
        rw [if_neg hne])]
    simp

/-- The cone over a convex hull from an exterior apex `z` (z-translate variant
of HOL `AFF_GE_0_CONVEX_HULL_ALT`, flyspeck_multivariate.ml:1531, needed by
the fan-7 consumers with a non-0 base). -/
theorem AFF_GE_SING_CONVEX_HULL_ALT {z : V3} {s : Set V3} (hfin : s.Finite)
    (hzs : z ∉ s) :
    affGe {z} s =
      insert z {v : V3 | ∃ t : ℝ, 0 < t ∧ ∃ y, y ∈ convexHull ℝ s ∧
        v = z + t • (y - z)} := by
  classical
  refine Set.ext fun v => ?_
  rw [Set.mem_insert_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hK, hvsum, hsign, hone⟩
    have hzK : z ∈ hK.toFinset :=
      hK.mem_toFinset.2 (Set.mem_union_left _ (Set.mem_singleton z))
    have hKe : ∀ w ∈ hK.toFinset.erase z, w ∈ s := by
      intro w hw
      have hbm : w ∈ ({z} ∪ s : Set V3) :=
        hK.mem_toFinset.1 (Finset.mem_erase.1 hw).2
      rcases (Set.mem_union w {z} s).1 hbm with h | h
      · exact absurd h (Finset.mem_erase.1 hw).1
      · exact h
    have hsumE : f z + ∑ w ∈ hK.toFinset.erase z, f w = 1 := by
      rw [← hone, Finset.add_sum_erase _ _ hzK]
    set S : ℝ := ∑ w ∈ hK.toFinset.erase z, f w with hSdef
    have hSn : 0 ≤ S := Finset.sum_nonneg fun w hw => hsign w (hKe w hw)
    by_cases hS0 : S = 0
    · -- S = 0: all s-coefficients vanish, v = z
      left
      have hfv : f z = 1 := by linarith [hsumE, hS0]
      have hnn : ∀ w ∈ hK.toFinset.erase z, 0 ≤ f w := fun w hw => hsign w (hKe w hw)
      have hzero : ∑ w ∈ hK.toFinset.erase z, f w • w = 0 := by
        have hsum0 : ∑ w ∈ hK.toFinset.erase z, f w = 0 := hSdef.symm.trans hS0
        have hfw : ∀ w ∈ hK.toFinset.erase z, f w = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0
        exact Finset.sum_eq_zero fun w hw => by rw [hfw w hw, zero_smul]
      rw [hvsum, ← Finset.add_sum_erase hK.toFinset (fun w => f w • w) hzK,
        hzero, add_zero, hfv, one_smul]
    · -- S > 0: v = z + S • (y - z) with y ∈ convex hull s
      right
      have hSpos : 0 < S := lt_of_le_of_ne hSn (Ne.symm hS0)
      refine ⟨S, hSpos, ∑ w ∈ hK.toFinset.erase z, (f w / S) • w, ?_, ?_⟩
      · rw [convexHull_eq]
        refine ⟨V3, hK.toFinset.erase z, fun i => f i / S, id, ?_, ?_, ?_, ?_⟩
        · exact fun i hi => div_nonneg (hsign i (hKe i hi)) (le_of_lt hSpos)
        · rw [← Finset.sum_div, hSdef, div_self hS0]
        · exact fun i hi => hKe i hi
        · have hsum1 : ∑ i ∈ hK.toFinset.erase z, f i / S = 1 := by
            rw [← Finset.sum_div, hSdef, div_self hS0]
          rw [Finset.centerMass, hsum1, inv_one, one_smul]
          exact Finset.sum_congr rfl fun i _ => by rw [id_eq]
      · rw [hvsum, ← Finset.add_sum_erase hK.toFinset (fun w => f w • w) hzK]
        have hfv : f z = 1 - S := by linarith [hsumE]
        rw [hfv]
        have hyexp : S • ∑ w ∈ hK.toFinset.erase z, (f w / S) • w
            = ∑ w ∈ hK.toFinset.erase z, f w • w := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          have h1 : S * (f w / S) = f w := by field_simp
          rw [smul_smul, h1]
        linear_combination (norm := module) -hyexp
  · rintro (h | ⟨t, ht, y, hym, rfl⟩)
    · rw [h]
      exact mem_affGe_base hfin
    · have hsub : convexHull ℝ s ⊆ affGe {z} s :=
        convexHull_min (fun w hw => mem_affGe_of_mem hfin hzs hw)
          (affGe_convex hfin)
      obtain ⟨f, hK, hfsum, hsign, hone⟩ := hsub hym
      have hzK : z ∈ hK.toFinset :=
        hK.mem_toFinset.2 (Set.mem_union_left _ (Set.mem_singleton z))
      have hvec : z + t • (y - z) = ∑ u ∈ hK.toFinset,
          ((if u = z then (1:ℝ) - t else 0) • u + t • (f u • u)) := by
        have hterm : ∑ x ∈ hK.toFinset, ((if x = z then (1:ℝ) - t else 0) • x
            + t • (f x • x))
            = ∑ x ∈ hK.toFinset, (if x = z then (1:ℝ) - t else 0) • x
                + ∑ x ∈ hK.toFinset, t • (f x • x) := Finset.sum_add_distrib
        have hif : ∑ x ∈ hK.toFinset, (if x = z then (1:ℝ) - t else 0) • x
            = (1 - t) • z := by
          rw [Finset.sum_eq_single_of_mem z hzK (fun b hb hne => by
            rw [if_neg hne]; exact zero_smul ℝ b), if_pos rfl]
        have h2t : ∑ x ∈ hK.toFinset, t • (f x • x)
            = t • ∑ x ∈ hK.toFinset, f x • x := Finset.smul_sum.symm
        rw [hfsum, hterm, hif, h2t]
        module
      rw [hvec]
      refine ⟨fun u => (if u = z then (1:ℝ) - t else 0) + t * f u, hK, ?_, ?_, ?_⟩
      · exact Finset.sum_congr rfl fun w _ => by
          beta_reduce
          rw [add_smul, ← mul_smul]
      · intro w hw
        beta_reduce
        show (if w = z then (1:ℝ) - t else 0) + t * f w ≥ 0
        by_cases huz : w = z
        · rw [huz] at hw
          exact absurd hw hzs
        · rw [if_neg huz]
          exact add_nonneg (by norm_num) (mul_nonneg (le_of_lt ht) (hsign w hw))
      · beta_reduce
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq_of_mem' hK.toFinset z
          (fun x => (1:ℝ) - t) hzK, ← Finset.mul_sum, hone]
        ring

/-- HOL `AFF_GE_0_CONVEX_HULL_ALT` (flyspeck_multivariate.ml:1531). -/
theorem AFF_GE_0_CONVEX_HULL_ALT {s : Set V3} (hfin : s.Finite)
    (h0s : (0:V3) ∉ s) :
    affGe {(0:V3)} s =
      insert (0:V3) {v : V3 | ∃ t : ℝ, 0 < t ∧ ∃ y, y ∈ convexHull ℝ s ∧
        v = t • y} := by
  rw [AFF_GE_SING_CONVEX_HULL_ALT hfin h0s]
  refine congrArg (insert (0:V3)) (Set.ext fun v => ?_)
  simp only [Set.mem_setOf_eq, zero_add, sub_zero]

end Kepler.Text
