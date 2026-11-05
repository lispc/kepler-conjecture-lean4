/-
P22EdgeFacets: the "an edge lies in at most two facets" counting kit, plus the
dart/edge cardinality and incidence-counting chain feeding
`polyhedron_edge_sum` (#9 of PackingAuto22).

Route (route A of the pa22-face-scout verdict, with the sign analysis repaired):
* every facet through `e` is cut out by a supporting halfspace `aᵢ·x ≤ bᵢ`,
  and all normals `aᵢ` kill the edge direction `d`;
* `a1, a2` are independent, `finrank ker (dotRight d) = 2`, so `a3` lies in
  `span{a1, a2}`: `a3 = α a1 + β a2`;
* if `α, β` have the same sign then `f3 ⊆ f1`; if they have opposite signs then
  `a1` (or `a2`) is a *positive* combination of the other two normals, whence
  `f1 ⊆ f3` (resp. `f2 ⊆ f3`).  In both cases two distinct facets coincide.
-/
import Kepler.Text.Polytope

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Dot-product bridge -/

private def dotRight (a : V3) : V3 →ₗ[ℝ] ℝ where
  toFun x := a ⬝ᵥ x
  map_add' x y := by
    show a.ofLp ⬝ᵥ (x.ofLp + y.ofLp) = a.ofLp ⬝ᵥ x.ofLp + a.ofLp ⬝ᵥ y.ofLp
    rw [dotProduct_add]
  map_smul' r x := by
    show a.ofLp ⬝ᵥ (r • x.ofLp) = (RingHom.id ℝ) r • (a.ofLp ⬝ᵥ x.ofLp)
    rw [dotProduct_smul]
    simp

/-- `(α • a + β • a') ⬝ᵥ c = α * (a ⬝ᵥ c) + β * (a' ⬝ᵥ c)`. -/
private theorem dotV_lin (α β : ℝ) (a a' c : V3) :
    (α • a + β • a') ⬝ᵥ c = α * (a ⬝ᵥ c) + β * (a' ⬝ᵥ c) := by
  show (α • a + β • a').ofLp ⬝ᵥ c.ofLp
    = α * (a.ofLp ⬝ᵥ c.ofLp) + β * (a'.ofLp ⬝ᵥ c.ofLp)
  rw [WithLp.ofLp_add, add_dotProduct, WithLp.ofLp_smul, WithLp.ofLp_smul,
    smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]

/-- `((t • a) ⬝ᵥ b) = t * (a ⬝ᵥ b)`. -/
private theorem dotV_smul_l (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) := by
  show ((t • a : V3).ofLp) ⬝ᵥ b.ofLp = t * (a.ofLp ⬝ᵥ b.ofLp)
  rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]

/-- `finrank ker (dotRight d) = 2` for `d ≠ 0` (the row-space dimension of the
hyperplane direction, same template as `Polytope.affDim_hyperplane`). -/
private theorem finrank_ker_dotRight (d : V3) (hd : d ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (dotRight d)) = 2 := by
  have hdof : d.ofLp ≠ 0 := by simpa using hd
  have hdd : d.ofLp ⬝ᵥ d.ofLp ≠ 0 := fun h => hdof (dotProduct_self_eq_zero.1 h)
  have hsurj : ∀ r : ℝ, ∃ x : V3, dotRight d x = r := by
    intro r
    refine ⟨(r / (d ⬝ᵥ d)) • d, ?_⟩
    show d.ofLp ⬝ᵥ ((r / (d.ofLp ⬝ᵥ d.ofLp)) • d.ofLp) = r
    rw [dotProduct_smul, smul_eq_mul]
    field_simp
  have hrange : LinearMap.range (dotRight d) = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact hsurj
  have hnk := LinearMap.finrank_range_add_finrank_ker (dotRight d)
  rw [hrange, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at hnk
  omega

private theorem range_pair_fin2 (a1 a2 : V3) :
    Set.range ![a1, a2] = ({a1, a2} : Set V3) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx
    · exact ⟨0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨1, by simp [hx]⟩

/-! ## Facet basics -/

/-- `FACET_AFF_DIM_2` without the boundedness hypothesis: `0 ∈ interior p`
forces `p` to be full-dimensional, hence every facet is 2-dimensional. -/
theorem p22F_facet_affDim_two (p f : Set V3) (hp : polyhedron p)
    (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p) : affDim f = 2 := by
  have hap : affineSpan ℝ p = ⊤ := by
    have h1 : affineSpan ℝ (interior p) = ⊤ :=
      isOpen_interior.affineSpan_eq_top ⟨(0 : V3), hi⟩
    rw [eq_top_iff, ← h1]
    exact affineSpan_mono ℝ interior_subset
  have hvtop : vectorSpan ℝ p = ⊤ := by
    first
      | rw [← direction_affineSpan ℝ p, hap, AffineSubspace.direction_top]
      | rw [← direction_affineSpan ℝ p, hap, direction_top]
      | rw [← AffineSubspace.direction_affineSpan ℝ p, hap,
          AffineSubspace.direction_top]
  have hpne : p ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨(0 : V3), interior_subset hi⟩
  have hpd : affDim p = 3 := by
    rw [affDim, if_neg hpne, hvtop, finrank_top]
    exact_mod_cast finrank_euclideanSpace_fin
  rw [hf.2.2, hpd]
  norm_num

/-- Same-dimension face containment forces equality (polytope1.ml `FACE_OF_EQ`
via relative interiors). -/
private theorem faceOf_eq_of_subset_affDim {s t u : Set V3} (ht : FaceOf t s)
    (hu : FaceOf u s) (hsub : t ⊆ u) (hdim : affDim t = affDim u) (htne : t ≠ ∅) :
    t = u := by
  have htne' : t.Nonempty := nonempty_iff_ne_empty.2 htne
  have hune : u ≠ ∅ := by
    intro h
    rw [h] at hsub
    exact htne (subset_empty_iff.1 hsub)
  have hfin : Module.finrank ℝ (vectorSpan ℝ t) = Module.finrank ℝ (vectorSpan ℝ u) := by
    have h := hdim
    simp only [affDim, if_neg htne, if_neg hune] at h
    exact_mod_cast h
  have hv : vectorSpan ℝ t = vectorSpan ℝ u :=
    Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ hsub) (le_of_eq hfin.symm)
  have hspan : (affineSpan ℝ t : Set V3) = (affineSpan ℝ u : Set V3) := by
    have h := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
      (s₁ := affineSpan ℝ t) (s₂ := affineSpan ℝ u)
      (by rw [direction_affineSpan, direction_affineSpan, hv])
      ⟨htne'.some, subset_affineSpan ℝ t htne'.some_mem⟩
      (affineSpan_mono ℝ hsub)
    exact congrArg (fun A : AffineSubspace ℝ V3 => (A : Set V3)) h
  obtain ⟨x, hxint⟩ := Set.Nonempty.intrinsicInterior ht.2.1 htne'
  have hx : x ∈ intrinsicInterior ℝ u := by
    rw [mem_rint_iff] at hxint ⊢
    obtain ⟨hxt, ε, hε, hball⟩ := hxint
    refine ⟨hsub hxt, ε, hε, ?_⟩
    intro y hy
    exact hsub (hball ⟨hy.1, by rw [hspan]; exact hy.2⟩)
  exact faceOf_eq ht hu (Set.not_disjoint_iff.2 ⟨x, hxint, hx⟩)

/-- Two facets of a polyhedron with nonempty interior that contain one another
coincide. -/
private theorem facet_eq_of_subset {P f g : Set V3} (hp : polyhedron P)
    (hi : (0 : V3) ∈ interior P) (hf : FacetOf f P) (hg : FacetOf g P) (hsub : f ⊆ g) :
    f = g :=
  faceOf_eq_of_subset_affDim hf.1 hg.1 hsub
    (by rw [p22F_facet_affDim_two P f hp hi hf, p22F_facet_affDim_two P g hp hi hg])
    hf.2.1

/-- **An edge lies in at most two facets** (counting form).  The boundedness
hypothesis is kept only for signature compatibility with
`polyhedron_edge_sum`; the argument does not use it. -/
theorem p22_edge_facets_ncard_le_two (P e : Set V3) (hp : polyhedron P)
    (_hb : Bornology.IsBounded P) (hi : (0 : V3) ∈ interior P) :
    ({f : Set V3 | FacetOf f P ∧ FacetOf e f}).ncard ≤ 2 := by
  classical
  set S : Set (Set V3) := {f : Set V3 | FacetOf f P ∧ FacetOf e f} with hS
  have hSfin : S.Finite := by
    rw [hS]
    exact (FINITE_POLYHEDRON_FACETS hp).subset (fun f hf => hf.1)
  by_contra hcon
  push_neg at hcon
  obtain ⟨f1, hf1, f2, hf2, f3, hf3, h12, h13, h23⟩ := (Set.two_lt_ncard hSfin).1 hcon
  obtain ⟨hf1P, hf1e⟩ := hf1
  obtain ⟨hf2P, hf2e⟩ := hf2
  obtain ⟨hf3P, hf3e⟩ := hf3
  have hd1 : affDim f1 = 2 := p22F_facet_affDim_two P f1 hp hi hf1P
  -- supporting halfspaces
  obtain ⟨a1, b1, ha1, hle1, heq1⟩ := FACET_OF_POLYHEDRON hp hf1P
  obtain ⟨a2, b2, ha2, hle2, heq2⟩ := FACET_OF_POLYHEDRON hp hf2P
  obtain ⟨a3, b3, ha3, hle3, heq3⟩ := FACET_OF_POLYHEDRON hp hf3P
  -- values of the normals on the edge
  have hval : ∀ (a : V3) (b : ℝ) (f : Set V3), (e ⊆ f) →
      f = P ∩ {x : V3 | a ⬝ᵥ x = b} → ∀ x ∈ e, a ⬝ᵥ x = b := by
    intro a b f hsub hf x hx
    have hxf : x ∈ f := hsub hx
    rw [hf] at hxf
    exact hxf.2
  have h1e : ∀ x ∈ e, a1 ⬝ᵥ x = b1 := hval a1 b1 f1 hf1e.1.1 heq1
  have h2e : ∀ x ∈ e, a2 ⬝ᵥ x = b2 := hval a2 b2 f2 hf2e.1.1 heq2
  have h3e : ∀ x ∈ e, a3 ⬝ᵥ x = b3 := hval a3 b3 f3 hf3e.1.1 heq3
  -- `e` is 1-dimensional, hence has two distinct points
  have hene : e.Nonempty := nonempty_iff_ne_empty.2 hf1e.2.1
  have hdime : affDim e = 1 := by rw [hf1e.2.2, hd1]; norm_num
  obtain ⟨v, hv, w, hw, hvw⟩ : ∃ v ∈ e, ∃ w ∈ e, v ≠ w := by
    by_contra hcon2
    push_neg at hcon2
    obtain ⟨v0, hv0⟩ := hene
    have hsingle : e = {v0} := by
      refine Subset.antisymm (fun y hy => ?_) (singleton_subset_iff.2 hv0)
      rw [Set.mem_singleton_iff]
      exact (hcon2 v0 hv0 y hy).symm
    rw [hsingle, affDim_singleton] at hdime
    norm_num at hdime
  set d : V3 := w - v with hddef
  have hd0 : d ≠ 0 := by
    rw [hddef]
    exact sub_ne_zero.2 hvw.symm
  have ha1d : a1 ⬝ᵥ d = 0 := by
    rw [hddef]
    show a1.ofLp ⬝ᵥ (w.ofLp - v.ofLp) = 0
    rw [dotProduct_sub, h1e w hw, h1e v hv, sub_self]
  have ha2d : a2 ⬝ᵥ d = 0 := by
    rw [hddef]
    show a2.ofLp ⬝ᵥ (w.ofLp - v.ofLp) = 0
    rw [dotProduct_sub, h2e w hw, h2e v hv, sub_self]
  have ha3d : a3 ⬝ᵥ d = 0 := by
    rw [hddef]
    show a3.ofLp ⬝ᵥ (w.ofLp - v.ofLp) = 0
    rw [dotProduct_sub, h3e w hw, h3e v hv, sub_self]
  have hker1 : a1 ∈ LinearMap.ker (dotRight d) := by
    rw [LinearMap.mem_ker]
    show d.ofLp ⬝ᵥ a1.ofLp = 0
    rw [dotProduct_comm]
    exact ha1d
  have hker2 : a2 ∈ LinearMap.ker (dotRight d) := by
    rw [LinearMap.mem_ker]
    show d.ofLp ⬝ᵥ a2.ofLp = 0
    rw [dotProduct_comm]
    exact ha2d
  have hker3 : a3 ∈ LinearMap.ker (dotRight d) := by
    rw [LinearMap.mem_ker]
    show d.ofLp ⬝ᵥ a3.ofLp = 0
    rw [dotProduct_comm]
    exact ha3d
  have hkerfin : Module.finrank ℝ (LinearMap.ker (dotRight d)) = 2 :=
    finrank_ker_dotRight d hd0
  have hspanle : Submodule.span ℝ ({a1, a2} : Set V3) ≤ LinearMap.ker (dotRight d) := by
    rw [Submodule.span_le]
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx
    · exact hker1
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hker2
  -- proportional normals give one inclusion between the facets
  have hsub_of_smul : ∀ {a a' : V3} {b b' : ℝ} {c : ℝ} {f g : Set V3},
      f = P ∩ {x : V3 | a ⬝ᵥ x = b} → g = P ∩ {x : V3 | a' ⬝ᵥ x = b'} →
      a' = c • a → (f ∩ g).Nonempty → f ⊆ g := by
    intro a a' b b' c f g hf hg hc hne
    obtain ⟨p, hpf, hpg⟩ := hne
    have hfp : a ⬝ᵥ p = b := by
      rw [hf] at hpf
      exact hpf.2
    have hgp : a' ⬝ᵥ p = b' := by
      rw [hg] at hpg
      exact hpg.2
    have hbp : c * b = b' := by
      rw [← hgp, hc, dotV_smul_l, hfp]
    intro x hx
    have hxP : x ∈ P := by
      rw [hf] at hx
      exact hx.1
    have hxa : a ⬝ᵥ x = b := by
      rw [hf] at hx
      exact hx.2
    rw [hg]
    refine ⟨hxP, ?_⟩
    show a' ⬝ᵥ x = b'
    rw [hc]
    show (c • a).ofLp ⬝ᵥ x.ofLp = b'
    rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul, hxa, hbp]
  have hindep : LinearIndependent ℝ ![a1, a2] := by
    rw [LinearIndependent.pair_iff' ha1]
    intro c hc
    have hsub : f1 ⊆ f2 :=
      hsub_of_smul heq1 heq2 (by rw [hc]) ⟨v, hf1e.1.1 hv, hf2e.1.1 hv⟩
    exact h12 (facet_eq_of_subset hp hi hf1P hf2P hsub)
  have hspanfin : Module.finrank ℝ (Submodule.span ℝ ({a1, a2} : Set V3)) = 2 := by
    have h := finrank_span_eq_card hindep
    rw [range_pair_fin2, Fintype.card_fin] at h
    exact h
  have hspaneq : Submodule.span ℝ ({a1, a2} : Set V3) = LinearMap.ker (dotRight d) := by
    refine Submodule.eq_of_le_of_finrank_le hspanle ?_
    rw [hspanfin, hkerfin]
  have ha3span : a3 ∈ Submodule.span ℝ ({a1, a2} : Set V3) := by
    rw [hspaneq]
    exact hker3
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 ha3span
  -- `b3 = α b1 + β b2`
  have hb3 : b3 = α * b1 + β * b2 := by
    have hv3 := h3e v hv
    rw [← hαβ, dotV_lin] at hv3
    rw [h1e v hv, h2e v hv] at hv3
    exact hv3.symm
  -- pointwise identity
  have hkey3 : ∀ x ∈ P, a3 ⬝ᵥ x - b3 = α * (a1 ⬝ᵥ x - b1) + β * (a2 ⬝ᵥ x - b2) := by
    intro x _
    rw [← hαβ, dotV_lin]
    have h : α * (a1 ⬝ᵥ x - b1) + β * (a2 ⬝ᵥ x - b2)
        = α * (a1 ⬝ᵥ x) + β * (a2 ⬝ᵥ x) - (α * b1 + β * b2) := by ring
    rw [h, ← hb3]
  -- solving `a1` resp. `a2` from that identity
  have hid1 : α ≠ 0 → ∀ x ∈ P,
      a1 ⬝ᵥ x - b1 = α⁻¹ * (a3 ⬝ᵥ x - b3) + (-β * α⁻¹) * (a2 ⬝ᵥ x - b2) := by
    intro hα x hx
    refine mul_left_cancel₀ hα ?_
    rw [hkey3 x hx]
    field_simp
    ring
  have hid2 : β ≠ 0 → ∀ x ∈ P,
      a2 ⬝ᵥ x - b2 = β⁻¹ * (a3 ⬝ᵥ x - b3) + (-α * β⁻¹) * (a1 ⬝ᵥ x - b1) := by
    intro hβ x hx
    refine mul_left_cancel₀ hβ ?_
    rw [hkey3 x hx]
    field_simp
    ring
  -- sign lemma: two nonpositive terms with positive coefficients summing to 0
  have hsign : ∀ {p q u vv : ℝ}, 0 < p → 0 < q → u ≤ 0 → vv ≤ 0 →
      p * u + q * vv = 0 → u = 0 := by
    intro p q u vv hp hq hu hv' h
    have h1 : p * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le hu
    have h2 : q * vv ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le hv'
    have h3 : p * u = 0 := by linarith
    exact (mul_eq_zero.1 h3).resolve_left hp.ne'
  -- `f3 ⊆ f1` in the same-sign cases
  have hsame : (0 < α ∧ 0 < β) ∨ (α < 0 ∧ β < 0) → f3 ⊆ f1 := by
    rintro (⟨hα, hβ⟩ | ⟨hα, hβ⟩)
    · intro x hx
      have hxP : x ∈ P := by rw [heq3] at hx; exact hx.1
      have hx3 : a3 ⬝ᵥ x = b3 := by rw [heq3] at hx; exact hx.2
      have hu : a1 ⬝ᵥ x - b1 ≤ 0 := sub_nonpos.2 (hle1 hxP)
      have hv2 : a2 ⬝ᵥ x - b2 ≤ 0 := sub_nonpos.2 (hle2 hxP)
      have hzero : α * (a1 ⬝ᵥ x - b1) + β * (a2 ⬝ᵥ x - b2) = 0 := by
        have h := hkey3 x hxP
        rw [sub_eq_zero.2 hx3] at h
        linarith
      have hu0 : a1 ⬝ᵥ x - b1 = 0 := hsign hα hβ hu hv2 hzero
      rw [heq1]
      exact ⟨hxP, sub_eq_zero.1 hu0⟩
    · intro x hx
      have hxP : x ∈ P := by rw [heq3] at hx; exact hx.1
      have hx3 : a3 ⬝ᵥ x = b3 := by rw [heq3] at hx; exact hx.2
      have hu : a1 ⬝ᵥ x - b1 ≤ 0 := sub_nonpos.2 (hle1 hxP)
      have hv2 : a2 ⬝ᵥ x - b2 ≤ 0 := sub_nonpos.2 (hle2 hxP)
      have hzero : (-α) * (a1 ⬝ᵥ x - b1) + (-β) * (a2 ⬝ᵥ x - b2) = 0 := by
        have h := hkey3 x hxP
        rw [sub_eq_zero.2 hx3] at h
        linarith
      have hu0 : a1 ⬝ᵥ x - b1 = 0 :=
        hsign (by linarith : (0:ℝ) < -α) (by linarith : (0:ℝ) < -β) hu hv2 hzero
      rw [heq1]
      exact ⟨hxP, sub_eq_zero.1 hu0⟩
  -- `f1 ⊆ f3` when `α > 0 > β`
  have hmix1 : 0 < α → β < 0 → f1 ⊆ f3 := by
    intro hα hβ x hx
    have hxP : x ∈ P := by rw [heq1] at hx; exact hx.1
    have hx1 : a1 ⬝ᵥ x = b1 := by rw [heq1] at hx; exact hx.2
    have hu3 : a3 ⬝ᵥ x - b3 ≤ 0 := sub_nonpos.2 (hle3 hxP)
    have hu2 : a2 ⬝ᵥ x - b2 ≤ 0 := sub_nonpos.2 (hle2 hxP)
    have hzero : α⁻¹ * (a3 ⬝ᵥ x - b3) + (-β * α⁻¹) * (a2 ⬝ᵥ x - b2) = 0 := by
      have h := hid1 hα.ne' x hxP
      rw [hx1, sub_self] at h
      exact h.symm
    have hu0 : a3 ⬝ᵥ x - b3 = 0 :=
      hsign (inv_pos.2 hα) (mul_pos (by linarith) (inv_pos.2 hα)) hu3 hu2 hzero
    rw [heq3]
    exact ⟨hxP, sub_eq_zero.1 hu0⟩
  -- `f2 ⊆ f3` when `α < 0 < β`
  have hmix2 : α < 0 → 0 < β → f2 ⊆ f3 := by
    intro hα hβ x hx
    have hxP : x ∈ P := by rw [heq2] at hx; exact hx.1
    have hx2 : a2 ⬝ᵥ x = b2 := by rw [heq2] at hx; exact hx.2
    have hu3 : a3 ⬝ᵥ x - b3 ≤ 0 := sub_nonpos.2 (hle3 hxP)
    have hu1 : a1 ⬝ᵥ x - b1 ≤ 0 := sub_nonpos.2 (hle1 hxP)
    have hzero : β⁻¹ * (a3 ⬝ᵥ x - b3) + (-α * β⁻¹) * (a1 ⬝ᵥ x - b1) = 0 := by
      have h := hid2 hβ.ne' x hxP
      rw [hx2, sub_self] at h
      exact h.symm
    have hu0 : a3 ⬝ᵥ x - b3 = 0 :=
      hsign (inv_pos.2 hβ) (mul_pos (by linarith) (inv_pos.2 hβ)) hu3 hu1 hzero
    rw [heq3]
    exact ⟨hxP, sub_eq_zero.1 hu0⟩
  rcases lt_trichotomy α 0 with hαneg | hαzero | hαpos
  · rcases lt_trichotomy β 0 with hβneg | hβzero | hβpos
    · have heq : f3 = f1 :=
        facet_eq_of_subset (P := P) (f := f3) (g := f1) hp hi hf3P hf1P
          (hsame (Or.inr ⟨hαneg, hβneg⟩))
      exact h13 heq.symm
    · -- β = 0: `a3 = α • a1`, so `f3 ⊆ f1`
      have hαne : α ≠ 0 := by
        intro hα0
        rw [hα0, hβzero, zero_smul, zero_smul, zero_add] at hαβ
        exact ha3 hαβ.symm
      have h3a : a3 = α • a1 := by
        rw [hβzero, zero_smul, add_zero] at hαβ
        exact hαβ.symm
      have h1a : a1 = α⁻¹ • a3 := by
        rw [h3a, smul_smul, inv_mul_cancel₀ hαne, one_smul]
      have hsub : f3 ⊆ f1 :=
        hsub_of_smul heq3 heq1 h1a ⟨v, hf3e.1.1 hv, hf1e.1.1 hv⟩
      have heq : f3 = f1 :=
        facet_eq_of_subset (P := P) (f := f3) (g := f1) hp hi hf3P hf1P hsub
      exact h13 heq.symm
    · have hsub : f2 ⊆ f3 := hmix2 hαneg hβpos
      exact h23 (facet_eq_of_subset (P := P) (f := f2) (g := f3) hp hi hf2P hf3P hsub)
  · -- α = 0: `a3 = β • a2`, so `f3 ⊆ f2`
    have hβne : β ≠ 0 := by
      intro hβ0
      rw [hαzero, hβ0, zero_smul, zero_smul, zero_add] at hαβ
      exact ha3 hαβ.symm
    have h3a : a3 = β • a2 := by
      rw [hαzero, zero_smul, zero_add] at hαβ
      exact hαβ.symm
    have h2a : a2 = β⁻¹ • a3 := by
      rw [h3a, smul_smul, inv_mul_cancel₀ hβne, one_smul]
    have hsub : f3 ⊆ f2 :=
      hsub_of_smul heq3 heq2 h2a ⟨v, hf3e.1.1 hv, hf2e.1.1 hv⟩
    have heq : f3 = f2 :=
      facet_eq_of_subset (P := P) (f := f3) (g := f2) hp hi hf3P hf2P hsub
    exact h23 heq.symm
  · rcases lt_trichotomy β 0 with hβneg | hβzero | hβpos
    · have hsub : f1 ⊆ f3 := hmix1 hαpos hβneg
      exact h13 (facet_eq_of_subset (P := P) (f := f1) (g := f3) hp hi hf1P hf3P hsub)
    · -- β = 0: `a3 = α • a1`
      have hαne : α ≠ 0 := by
        intro hα0
        rw [hα0, hβzero, zero_smul, zero_smul, zero_add] at hαβ
        exact ha3 hαβ.symm
      have h3a : a3 = α • a1 := by
        rw [hβzero, zero_smul, add_zero] at hαβ
        exact hαβ.symm
      have h1a : a1 = α⁻¹ • a3 := by
        rw [h3a, smul_smul, inv_mul_cancel₀ hαne, one_smul]
      have hsub : f3 ⊆ f1 :=
        hsub_of_smul heq3 heq1 h1a ⟨v, hf3e.1.1 hv, hf1e.1.1 hv⟩
      have heq : f3 = f1 :=
        facet_eq_of_subset (P := P) (f := f3) (g := f1) hp hi hf3P hf1P hsub
      exact h13 heq.symm
    · have heq : f3 = f1 :=
        facet_eq_of_subset (P := P) (f := f3) (g := f1) hp hi hf3P hf1P
          (hsame (Or.inl ⟨hαpos, hβpos⟩))
      exact h13 heq.symm
