/-
PackingAuto22: port of `scripts/packing/counting_spheres.hl` (Flyspeck chapter
"packing / Counting Spheres", T. Hales, 7335 lines; 1 def + 92 theorems).

FILE MAP (how this feeds the final Kepler count)
  This chapter is the density-asymptotics machinery feeding the final Kepler
  count: a packing's points inside the ball `B(0,r)` number at most
  `pi r^3 / sqrt 18 + c r^2`, and the local "counting" side of the Kepler
  inequality reduces to classifying polyhedral Voronoi cells around packing
  points.  The file carries three payloads.
  (a) Planar polyhedron kit (polytope1-style, `real^2`): supporting-hyperplane
      facet representations (`facet_rep_*`), cyclic `Arg`-sorting of facets
      (`poly_sort_*`, `POLYSORT_BIJ2`), the bisector-insertion toolkit, and the
      EUSOTYP/EUSOTYP2 "Euler stereotypical" theorems producing the g/h vertex
      walks around a facet used to sum dihedral angles.
  (b) Volumetric reduction: `fchanged`/`sol` analysis of facets (`GOTCJAH`:
      `2*pi - 2*n*asn(t*sin(pi/n)) <= sol 0 WF`), rcone geometry, wedge
      decomposition, and the 4*pi facet solid-angle sum
      `POLYHEDRON_FACET_SUM_4Pi`.
  (c) Counting endgame: finiteness of packings in the annulus
      (`fat_lemma1`), weak saturation (`weak_saturation`,
      `SATURATE_BALL_ANNULUS`), the YSSKQOY theta-angle bank feeding
      `DLWCHEM` (a saturated annulus packing has `CARD V = 13 \/ 14 \/ 15`)
      and `XULJEPR` (existence of a unit-norm-2 center forces the local
      annulus inequality).  DLWCHEM/XULJEPR are the counting branch facts
      consumed by the final Kepler count (packing2/counting lane).
  Source layout: 1 `new_definition` (`poly_sort_fn`) + 2 `new_specification`s
  (`facet_rep_a/b`, `bisector_point`) + 92 theorems.

ENCODING NOTES
  - HOL `real^3` <-> `V3` (Kepler.Geom); `packing` <-> `Packing`
    (Kepler/Statement.lean:35); `ball_annulus` <-> `ballAnnulus`
    (PackingAuto2: `closedBall 0 (2*h0) \ ball 0 2`, the Marchal annulus);
    `2 % v` scaling <-> `t • v`; `vec 0` <-> `0`.
  - HOL `real^2` (planar section: facets, `Arg`-sorts, EUSOTYP_simple) <-> `ℂ`:
    complex `Arg`, `/`, `norm` are native there; the planar dot product is
    `dot2 a b = (a * conj b).re` (= the standard real inner product under
    re/im coordinates); planar `polyhedron/facet_of` are the `*C` copies of
    Polytope's `polyhedron/FacetOf` (proper-face form `c ≠ P` for facets).
  - `facet_rep_a/b` and `bisector_point` are `new_specification`s: ported via
    `Classical.choose` from their existence theorems (faithful and
    choice-free-in-statements).
  - `measurable s` <-> `MeasurableSet volume s` (PackingAuto10
    style); `radial_norm r x C` <-> `Kepler.Geom.radialNorm`; `normball p r`
    <-> `Metric.closedBall p r` (HOL closed ball); `sol` <-> `Kepler.Geom.sol`.
  - `BIJ f a b` <-> `Set.BijOn f a b`; `INJ f a b` <-> `Set.InjOn f a b` plus
    image containment; `HAS_SIZE n` <-> `s.Finite ∧ s.ncard = n`; `CARD s` <->
    `s.ncard`; `1..n` <-> `Finset.Icc 1 n`; sums over sets <-> `∑ x ∈ s.toFinset`
    under `open Classical in` (HOL `sum V f`).
  - `is_realinterval s` <-> `∃ a b, s = Icc a b`; `real_interval [a,b]` <->
    `Icc a b`; `has_real_derivative f f' (atreal x within s)` <->
    `HasDerivWithinAt f f' s x`; the Calc_derivative artifact `derived_form`
    is encoded pointwise as `derivedFormP22 f f' x s`.
  - Fan/hypermap kit: `hypermap1_of_fanx (x,V,E)` is NOT ported anywhere in
    this checkout (ConformingDefs.lean:26), so it is stubbed here as
    `hypermap1OfFanxP22 : Hypermap Dart3` (Dart3 = V3 × V3 × V3); flyspeck
    `dart/edge_map/face_map/node/face_set/number_of_faces/plain_hypermap/
    simple_hypermap H` map to the `Hypermap` API fields; `d1_fan`, `e_fan`,
    `vertices p`, `edges p`, `dartset_leads_into_fan`,
    `topological_component_yfan` are `_p22` opaque stubs.
  - `cone0 x U` is DEFINED here as `affGe {x} U` (flyspeck cone0 = aff_gt of
    the apex through U; CONE0_AFF_GT becomes rfl).
  - `regular_spherical_polygon_area th k` is DEFINED here in closed form
    `2*pi - 2*k*asn(cos th * sin (pi/k))` (matches its flyspeck value at
    `th = cos 0.797`, i.e. theorem regular_spherical_polygon_area_797);
    `asnFnhk`, `vol_solid_triangle`, `weakly_saturated`,
    `local_annulus_inequality`, `pack_ineq_def_a` are `_p22` stubs.

## NEEDS (giant fill-in markers)
  - `hypermap1OfFanxP22`: NEEDS `hypermap1_of_fanx` (fan.hl / Planarity lane).
  - `verticesP22`, `edgesP22`, `dartsetLeadsIntoFanP22`,
    `topologicalComponentYfanP22`: NEEDS polytope/topology fan lanes.
  - `weaklySaturatedP22`: NEEDS PackingAuto3 (pack3.hl) — no olean on this
    branch.  `localAnnulusInequalityP22`, `packIneqDefAP22`: NEEDS pack1.hl
    (PackingAuto1, no olean).  `asnFnhkP22`: NEEDS Ysskqoy.hl
    (PackingAuto18 bank, no olean).  `volSolidTriangleP22`: NEEDS sphere.hl
    vol_solid_triangle.  `THETA_BOUNDS`: NEEDS Flyspeck_constants.bounds
    (`h0 < sqrt 3`, cf. PackingAuto15.H0_LT_SQRT2, not importable here).
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto11
import Kepler.Text.PackingAuto12
import Kepler.Text.PackingAuto13
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Encoding layer (planar section, notation wrappers) -/

/-- Planar dot product on `ℂ` standing in for HOL `dot` on `real^2`. -/
def dot2 (x y : ℂ) : ℝ := (x * star y).re

/-- HOL `asn` (arcsin). -/
noncomputable def asn (x : ℝ) : ℝ := Real.arcsin x

/-- HOL `acs` (arccos). -/
noncomputable def acs (x : ℝ) : ℝ := Real.arccos x

/-- HOL `sqrt3`. -/
noncomputable def sqrt3 : ℝ := Real.sqrt 3

/-- Planar copy of Polytope.`FaceOf` (polytope1.ml:22 face kit). -/
def faceOfC (t s : Set ℂ) : Prop :=
  t ⊆ s ∧ Convex ℝ t ∧
    ∀ a b x : ℂ, a ∈ s → b ∈ s → x ∈ t → x ∈ openSegment ℝ a b → a ∈ t ∧ b ∈ t

/-- Planar copy of HOL `facet_of` (proper face). -/
def facetOfC (f s : Set ℂ) : Prop := faceOfC f s ∧ f ≠ s

/-- Planar copy of HOL `polyhedron` (polytope1.ml:2546): every point is in a
facet. -/
def polyhedronC (P : Set ℂ) : Prop :=
  ∀ x : ℂ, x ∈ P → ∃ c : Set ℂ, facetOfC c P ∧ x ∈ c

/-- HOL `P hull S` = convex hull of `P ∪ S`. -/
def hullP22 (P S : Set V3) : Set V3 := convexHull ℝ (P ∪ S)

/-- HOL `normball p r` (measure.hl): the (open) ball, as in flyspeck `ball`. -/
def normballP22 (p : V3) (r : ℝ) : Set V3 := Metric.ball p r

/-- HOL `is_realinterval s` (Calc_derivative). -/
def isRealIntervalP22 (s : Set ℝ) : Prop := ∃ a b : ℝ, s = Icc a b

/-- HOL `derived_form` (Calc_derivative kit), encoded pointwise. -/
def derivedFormP22 (f f' : ℝ → ℝ) (x : ℝ) (_s : Set ℝ) : Prop :=
  HasDerivWithinAt f (f' x) _s x

/-- HOL `measurable s` (measure.hl) on ℝ³. -/
def measurableP22 (s : Set V3) : Prop := MeasurableSet s

/-! ## `_p22` stub layer (missing upstream defs; see NEEDS in header) -/

/-- HOL dart type: `real^3#3` (the `hypermap1_of_fanx` darts are `(u,v,w)`
vertex triples). -/
abbrev Dart3 := V3 × V3 × V3

noncomputable instance : DecidableEq Dart3 := Classical.decEq _

/-- HOL `pr2 (u,v,w) = v`. -/
def pr2 (d : Dart3) : V3 := d.2.1

/-- HOL `pr3 (u,v,w) = w`. -/
def pr3 (d : Dart3) : V3 := d.2.2

/-- NEEDS `hypermap1_of_fanx (x,V,E)` (fan.hl; Planarity lane). Stub value:
the empty hypermap. -/
theorem permutesOn_refl (s : Finset α) : PermutesOn (Equiv.refl α) s := fun _ _ => rfl

def hypermap1OfFanxP22 (x : V3) (V : Set V3) (E : Set (Set V3)) : Hypermap Dart3 :=
  { darts := ∅, edgeMap := .refl _, nodeMap := .refl _, faceMap := .refl _,
    edgeMap_permutes := permutesOn_refl _, nodeMap_permutes := permutesOn_refl _,
    faceMap_permutes := permutesOn_refl _, comp_eq_one := rfl }

/-- HOL `d_fan (x,V,E)`: the darts of `hypermap1_of_fanx (x,V,E)`. -/
def dFanP22 (x : V3) (V : Set V3) (E : Set (Set V3)) : Set Dart3 :=
  (hypermap1OfFanxP22 x V E).darts

/-- NEEDS HOL `d1_fan (x,V,E)` (fan.hl; distinct from `d_fan` a priori).
Stub: empty. -/
def d1FanP22 (x : V3) (V : Set V3) (E : Set (Set V3)) : Set Dart3 := ∅

/-- NEEDS HOL `e_fan (x,V,E) d` (fan.hl): next dart around `pr2 d`.
Stub: identity. -/
def eFanP22 (x : V3) (V : Set V3) (E : Set (Set V3)) (d : Dart3) : Dart3 := d

/-- HOL `set_of_edge v V E`: vertices adjacent to `v`. -/
def setOfEdgeP22 (v : V3) (V : Set V3) (E : Set (Set V3)) : Set V3 :=
  {w : V3 | {v, w} ∈ E}

/-- NEEDS HOL `vertices p` (polytope vertex set; polytope lane). Stub: ∅. -/
def verticesP22 (p : Set V3) : Set V3 := ∅

/-- NEEDS HOL `edges p` polytope-edge set (polytope lane; Polytope.`edges`
exists but is not wired to the fan kit). Stub: ∅. -/
def edgesP22 (p : Set V3) : Set (Set V3) := ∅

/-- NEEDS HOL `dartset_leads_into_fan (x,V,E) f` (fan.hl). Stub: ∅. -/
def dartsetLeadsIntoFanP22 (x : V3) (V : Set V3) (E : Set (Set V3))
    (f : Set Dart3) : Set V3 := ∅

/-- NEEDS HOL `topological_component_yfan (x,V,E) U` (yfan.hl). Stub. -/
def topologicalComponentYfanP22 (x : V3) (V : Set V3) (E : Set (Set V3))
    (U : Set V3) : Prop := True

/-- HOL `cone0 x U` (3d.tex): the open cone `aff_gt {x} U`. -/
def cone0P22 (x : V3) (U : Set V3) : Set V3 := affGe {x} U

/-- HOL `pad2d3d : real^2 -> real^3`: embed the plane as the 3rd-coordinate-0
subspace (planar `real^2` encoded as `ℂ`). -/
def pad2d3dP22 (z : ℂ) : V3 :=
  WithLp.toLp 2 (fun i : Fin 3 => match i with | 0 => z.re | 1 => z.im | 2 => 0)

/-- HOL `dropout 3 : real^3 -> real^2`: forget the 3rd coordinate. -/
def dropout3P22 (v : V3) : ℂ :=
  Complex.mk ((v : Fin 3 → ℝ) 0) ((v : Fin 3 → ℝ) 1)

/-- NEEDS `asnFnhk h k a b c d` (Ysskqoy.hl; PackingAuto18 bank). Stub: 0. -/
noncomputable def asnFnhkP22 (h : ℝ) (k : ℕ) (_a _b _c _d : ℝ) : ℝ := 0

/-- HOL `regular_spherical_polygon_area th k`, closed form `2*pi - 2*k*asn
(th * sin (pi/k))` (`th` taken as the cosine of the half-angle, matching the
flyspeck usage `regular_spherical_polygon_area (cos 0.797) k`; NEEDS
spherical.hl def to replace). -/
noncomputable def regularSphericalPolygonAreaP22 (th : ℝ) (k : ℕ) : ℝ :=
  2 * Real.pi - 2 * k * asn (th * Real.sin (Real.pi / k))

/-- NEEDS HOL `vol_solid_triangle x u v w r` (sphere.hl). Stub: 0. -/
noncomputable def volSolidTriangleP22 (x u v w : V3) (r : ℝ) : ℝ := 0

/-- NEEDS HOL `weakly_saturated V r c` (pack3.hl; PackingAuto3, no olean).
Stub. -/
def weaklySaturatedP22 (V : Set V3) (r c : ℝ) : Prop := True

/-- NEEDS HOL `local_annulus_inequality V` (pack1.hl; PackingAuto1, no olean).
Stub. -/
def localAnnulusInequalityP22 (V : Set V3) : Prop := True

/-- NEEDS HOL `pack_ineq_def_a` (pack1.hl: the numerical packing-inequality
conjunction). Stub. -/
def packIneqDefAP22 : Prop := True

/-! ## #1 Finiteness, annulus membership, facet representations -/

/-- HOL `fat_lemma1` (Fatugpd.lemma1): packings in the annulus are finite. -/
theorem fat_lemma1 (S : Set V3) (hP : Packing S) (hS : S ⊆ ballAnnulus) : S.Finite := by
  have hb : S ⊆ Metric.ball 0 (2 * h0 + 1) := fun v hv =>
    Metric.closedBall_subset_ball (by linarith) (Metric.mem_closedBall.mpr (hS hv).1)
  exact (hP.finite_inter_ball (2 * h0 + 1)).subset fun v hv => ⟨hv, hb hv⟩

/-- HOL `ckq_in_ball_annulus` (pack_defs.hl ball_annulus membership). -/
theorem ckq_in_ball_annulus (v : V3) :
    v ∈ ballAnnulus ↔ 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0 ∧ v ≠ 0 := by
  constructor
  · intro h
    have h2 : ¬ (‖v‖ < 2) := by rw [← dist_zero_right]; exact h.2
    have h1 : dist v 0 ≤ 2 * h0 := Metric.mem_closedBall.mp h.1
    exact ⟨le_of_not_gt h2, by rwa [dist_zero_right] at h1,
      fun hv => h2 (by rw [hv]; simp)⟩
  · rintro ⟨h1, h2, -⟩
    exact ⟨Metric.mem_closedBall.mpr (by rwa [dist_zero_right]), by
      rw [Metric.mem_ball, dist_zero_right]; linarith⟩

/-- HOL `lemma` (counting_spheres.hl:47): upward closure at the endpoint. -/
theorem endpoint_closure_lemma (a2 b c : ℝ) (ha : 0 < a2) (hc : 0 < c)
    (h : ∀ t : ℝ, 0 ≤ t → t < c → a2 * t ≤ b) :
    ∀ t : ℝ, 0 ≤ t → t ≤ c → a2 * t ≤ b := by
  intro t ht htc
  rcases eq_or_lt_of_le htc with heq | hlt
  · subst heq
    by_contra hcon
    have hb : b < a2 * t := by linarith
    have h1 : b / a2 < t := (div_lt_iff₀ ha).mpr (by linarith)
    have hq : a2 * (t / 2) ≤ b := h (t / 2) (by positivity) (by linarith)
    have hlow : t / 2 ≤ b / a2 := (le_div_iff₀ ha).mpr (by rwa [mul_comm])
    have ht0 : 0 ≤ (b / a2 + t) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    have h3 : (b / a2 + t) / 2 < t := by
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    have h4 : a2 * ((b / a2 + t) / 2) = (b + a2 * t) / 2 := by
      field_simp
    have h5 := h ((b / a2 + t) / 2) ht0 h3
    rw [h4] at h5
    linarith
  · exact h t ht hlt

/-- HOL `eus1` (counting_spheres.hl:85): facets of a planar polyhedron have
supporting-hyperplane representations.  GIANT. -/
theorem eus1 (P c : Set ℂ) (hP : polyhedronC P) (hc : facetOfC c P) :
    ∃ a : ℂ, ∃ b : ℝ, ‖a‖ = 1 ∧
      (∀ r : ℝ, 0 < r → (∀ p : ℂ, ‖p‖ < r → p ∈ P) → r ≤ b) ∧
      P ⊆ {x : ℂ | dot2 a x ≤ b} ∧
      c = P ∩ {x : ℂ | dot2 a x = b} := by
  sorry

/-- HOL `facet_rep_uniq` (counting_spheres.hl:161). GIANT. -/
theorem facet_rep_uniq (P c1 c2 : Set ℂ) (a : ℂ) (b1 b2 : ℝ)
    (hP : polyhedronC P) (h1 : facetOfC c1 P) (h2 : facetOfC c2 P)
    (s1 : P ⊆ {x : ℂ | dot2 a x ≤ b1}) (s2 : P ⊆ {x : ℂ | dot2 a x ≤ b2})
    (e1 : c1 = P ∩ {x : ℂ | dot2 a x = b1}) (e2 : c2 = P ∩ {x : ℂ | dot2 a x = b2}) :
    b1 = b2 ∧ c1 = c2 := by
  sorry

/-- The facet representation pair chosen by `facet_rep_spec`. -/
private noncomputable def facetRepPair : Set ℂ × Set ℂ → ℂ × ℝ :=
  fun Pc => if h : polyhedronC Pc.1 ∧ facetOfC Pc.2 Pc.1 then
    ((eus1 Pc.1 Pc.2 h.1 h.2).choose,
      Classical.choose (Classical.choose_spec (eus1 Pc.1 Pc.2 h.1 h.2)))
    else (0, 0)

/-- HOL `facet_rep_spec` (counting_spheres.hl:184): a global choice of facet
representations; gives `facet_rep_a` / `facet_rep_b`. -/
theorem facet_rep_spec :
    ∃ a : Set ℂ → Set ℂ → ℂ, ∃ b : Set ℂ → Set ℂ → ℝ, ∀ (P c : Set ℂ),
      polyhedronC P → facetOfC c P →
        ‖a P c‖ = 1 ∧
        (∀ r : ℝ, 0 < r → (∀ p : ℂ, ‖p‖ < r → p ∈ P) → r ≤ b P c) ∧
        P ⊆ {x : ℂ | dot2 (a P c) x ≤ b P c} ∧
        c = P ∩ {x : ℂ | dot2 (a P c) x = b P c} := by
  classical
  refine ⟨fun P c => (facetRepPair (P, c)).1, fun P c => (facetRepPair (P, c)).2, ?_⟩
  intro P c hP hF
  have hspec := Classical.choose_spec (Classical.choose_spec (eus1 P c hP hF))
  simp only [facetRepPair]
  split
  · exact hspec
  · rename_i h
    exact absurd (And.intro hP hF) h

/-- HOL `facet_rep_def` (new_specification of `facet_rep_a`). -/
noncomputable def facet_rep_a (P c : Set ℂ) : ℂ := Classical.choose facet_rep_spec P c

/-- HOL `facet_rep_def` (new_specification of `facet_rep_b`). -/
noncomputable def facet_rep_b (P c : Set ℂ) : ℝ :=
  Classical.choose (Classical.choose_spec facet_rep_spec) P c

/-- Unfolding of the `facet_rep_a/b` specification. -/
theorem facet_rep_props (P c : Set ℂ) (hP : polyhedronC P) (hc : facetOfC c P) :
    ‖facet_rep_a P c‖ = 1 ∧
      (∀ r : ℝ, 0 < r → (∀ p : ℂ, ‖p‖ < r → p ∈ P) → r ≤ facet_rep_b P c) ∧
      P ⊆ {x : ℂ | dot2 (facet_rep_a P c) x ≤ facet_rep_b P c} ∧
      c = P ∩ {x : ℂ | dot2 (facet_rep_a P c) x = facet_rep_b P c} :=
  (Classical.choose_spec (Classical.choose_spec facet_rep_spec)) P c hP hc

/-- HOL `facet_rep_uniq_c` (counting_spheres.hl:200). GIANT. -/
theorem facet_rep_uniq_c (P c1 c2 : Set ℂ) (hP : polyhedronC P)
    (h1 : facetOfC c1 P) (h2 : facetOfC c2 P)
    (h : facet_rep_a P c1 = facet_rep_a P c2) : c1 = c2 := by
  sorry

/-- Expansion of the planar dot product in coordinates. -/
theorem dot2_expand (z w : ℂ) : dot2 z w = z.re * w.re + z.im * w.im := by
  rw [dot2, Complex.mul_re]
  simp

theorem dot2_comm (z w : ℂ) : dot2 z w = dot2 w z := by
  rw [dot2_expand, dot2_expand]
  ring

theorem dot2_sub_r (z u w : ℂ) : dot2 z (u - w) = dot2 z u - dot2 z w := by
  rw [dot2_expand, dot2_expand, dot2_expand]
  simp [mul_sub]
  ring

theorem dot2_sub_l (z u w : ℂ) : dot2 (u - w) z = dot2 u z - dot2 w z := by
  rw [dot2_expand, dot2_expand, dot2_expand]
  simp [sub_mul]
  ring

/-- HOL `norm1_cauchy_eq` (counting_spheres.hl:216): unit vectors with inner
product 1 coincide. -/
theorem norm1_cauchy_eq (x y : ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : dot2 x y = 1) : x = y := by
  have key : ∀ w : ℂ, dot2 w w = ‖w‖ ^ 2 := by
    intro w
    have hns : Complex.normSq w = w.re * w.re + w.im * w.im := Complex.normSq_apply w
    rw [dot2_expand, Complex.sq_norm]
    linarith
  have hxs : dot2 x x = 1 := by rw [key, hx]; norm_num
  have hys : dot2 y y = 1 := by rw [key, hy]; norm_num
  have h0 : dot2 (x - y) (x - y) = 0 := by
    rw [dot2_sub_l, dot2_sub_r, dot2_sub_r, dot2_comm y x]
    linarith
  rw [key] at h0
  have hxy0 : x - y = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h0)
  exact eq_of_sub_eq_zero hxy0

/-- HOL `facet_rep_in_facet` (counting_spheres.hl:227). GIANT. -/
theorem facet_rep_in_facet (P c1 c2 : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (h1 : facetOfC c1 P) (h2 : facetOfC c2 P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h : facet_rep_b P c1 ≤ dot2 (facet_rep_a P c1) (r • facet_rep_a P c2)) :
    c1 = c2 := by
  sorry

/-- HOL `facet_rep_refl` (counting_spheres.hl:257). GIANT. -/
theorem facet_rep_refl (P c : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (hc : facetOfC c P) (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) :
    dot2 (facet_rep_a P c) (r • facet_rep_a P c) ≤ facet_rep_b P c := by
  sorry

/-- HOL `DOT_EQ_IMP_INEQ_LEMMA` (counting_spheres.hl:274). GIANT. -/
theorem DOT_EQ_IMP_INEQ_LEMMA (a a' : ℂ) (b b' : ℝ)
    (hiff : ∀ x : ℂ, dot2 a x = b ↔ dot2 a' x = b') (hb : 0 < b) (hb' : 0 < b') :
    ∀ x : ℂ, dot2 a x ≠ 0 → (dot2 a x ≤ b ↔ dot2 a' x ≤ b') := by
  sorry

/-- HOL `DOT_EQ_IMP_INEQ` (counting_spheres.hl:302). GIANT. -/
theorem DOT_EQ_IMP_INEQ (a a' : ℂ) (b b' : ℝ)
    (hiff : ∀ x : ℂ, dot2 a x = b ↔ dot2 a' x = b') (hb : 0 ≤ b) (hb' : 0 < b') :
    ∀ x : ℂ, dot2 a x ≤ b ↔ dot2 a' x ≤ b' := by
  sorry

/-- HOL `affine_facet_hyper` (counting_spheres.hl:320). GIANT. -/
theorem affine_facet_hyper (P c : Set ℂ) (a : ℂ) (b : ℝ)
    (hc : facetOfC c P) (hP : polyhedronC P) (haff : (affineSpan ℝ P : Set ℂ) = univ)
    (ha : a ≠ 0) (h : P ∩ {x : ℂ | dot2 a x = b} = c) :
    (affineSpan ℝ c : Set ℂ) = {x : ℂ | dot2 a x = b} := by
  sorry

/-- HOL `POLYHEDRON_MEMBER` (counting_spheres.hl:346). GIANT. -/
theorem POLYHEDRON_MEMBER (P : Set ℂ) (r : ℝ) (x : ℂ) (hP : polyhedronC P)
    (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h : ∀ c : Set ℂ, facetOfC c P → dot2 (facet_rep_a P c) x ≤ facet_rep_b P c) :
    x ∈ P := by
  sorry

/-- HOL `facet_rep_in_poly` (counting_spheres.hl:435). GIANT. -/
theorem facet_rep_in_poly (P c : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (hc : facetOfC c P) (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) :
    (r • facet_rep_a P c : ℂ) ∈ P := by
  sorry

/-- HOL `facet_arg_lt_pi` (counting_spheres.hl:453). GIANT. -/
theorem facet_arg_lt_pi (P c : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (hb : Bornology.IsBounded P) (hc : facetOfC c P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) :
    ∃ c' : Set ℂ, facetOfC c' P ∧
      0 < Complex.arg (facet_rep_a P c' / facet_rep_a P c) ∧
      Complex.arg (facet_rep_a P c' / facet_rep_a P c) < Real.pi := by
  sorry

/-- HOL `eus_cos` (counting_spheres.hl:510). -/
theorem eus_cos (phi psi : ℝ) (h1 : 0 ≤ psi) (h2 : psi ≤ phi)
    (h3 : phi ≤ 2 * Real.pi - psi) : Real.cos phi ≤ Real.cos psi := by
  have hanti := Real.strictAntiOn_cos
  rcases le_total phi Real.pi with hpi | hpi
  · have hpile : psi ≤ Real.pi := le_trans h2 hpi
    rcases lt_or_eq_of_le h2 with hlt | heq
    · exact le_of_lt (hanti (Set.mem_Icc.mpr ⟨h1, hpile⟩)
        (Set.mem_Icc.mpr ⟨by linarith, hpi⟩) hlt)
    · rw [← heq]
  · have hpsi : psi ≤ Real.pi := by linarith
    have h4 : 2 * Real.pi - phi ≤ Real.pi := by linarith
    have h5 : psi ≤ 2 * Real.pi - phi := by linarith
    have h6 : Real.cos (2 * Real.pi - phi) = Real.cos phi := by
      have h7 : Real.cos phi = Real.cos (phi - 2 * Real.pi) := by
        simpa using (Real.cos_periodic (phi - 2 * Real.pi)).symm
      rw [show 2 * Real.pi - phi = -(phi - 2 * Real.pi) by ring, Real.cos_neg]
      exact h7.symm
    rcases lt_or_eq_of_le h5 with hlt | heq
    · have hm := hanti (Set.mem_Icc.mpr ⟨h1, hpsi⟩)
        (Set.mem_Icc.mpr ⟨by linarith, h4⟩) hlt
      rw [h6] at hm
      exact le_of_lt hm
    · rw [heq, h6]

/-- HOL `insert_v` (counting_spheres.hl:529): the bisector insertion point
lies in the polyhedron. GIANT. -/
theorem insert_v (P c c' : Set ℂ) (r : ℝ) (v : ℂ) (psi : ℝ)
    (hP : polyhedronC P) (hc : facetOfC c P) (hc' : facetOfC c' P)
    (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h1 : Complex.arg (v / facet_rep_a P c) = psi) (h2 : 0 < psi)
    (h3 : psi < Real.pi / 2)
    (h4 : Complex.arg (facet_rep_a P c' / facet_rep_a P c) = 2 * psi)
    (h5 : ∀ c'' : Set ℂ, facetOfC c'' P →
      Complex.arg (facet_rep_a P c'' / facet_rep_a P c) < 2 * psi → c'' = c)
    (h6 : ‖v‖ = r / Real.cos psi) : v ∈ P := by
  sorry

/-- HOL `facet_rep_a_uniq` (counting_spheres.hl:640). GIANT. -/
theorem facet_rep_a_uniq (P c1 c2 : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (h1 : facetOfC c1 P) (h2 : facetOfC c2 P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h : ∃ s : ℝ, 0 < s ∧ facet_rep_a P c1 = s • facet_rep_a P c2) :
    c1 = c2 := by
  sorry

/-- HOL `poly_sort_fn` (counting_spheres.hl:678, the chapter's single
`new_definition`). -/
def poly_sort_fn (P : Set ℂ) (u : ℂ) (c1 c2 : Set ℂ) : Prop :=
  facetOfC c1 P ∧ facetOfC c2 P ∧
    Complex.arg (facet_rep_a P c1 / u) ≤ Complex.arg (facet_rep_a P c2 / u)

/-- HOL `poly_sort_antisym` (counting_spheres.hl:682). GIANT. -/
theorem poly_sort_antisym (P : Set ℂ) (u : ℂ) (c1 c2 : Set ℂ) (r : ℝ)
    (hP : polyhedronC P) (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h12 : poly_sort_fn P u c1 c2) (h21 : poly_sort_fn P u c2 c1) (hu : u ≠ 0) :
    c1 = c2 := by
  sorry

/-- HOL `poly_sort_trans` (counting_spheres.hl:715). GIANT. -/
theorem poly_sort_trans (P : Set ℂ) (u : ℂ) (c1 c2 c3 : Set ℂ) (r : ℝ)
    (hP : polyhedronC P) (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (hu : u ≠ 0) (h12 : poly_sort_fn P u c1 c2) (h23 : poly_sort_fn P u c2 c3) :
    poly_sort_fn P u c1 c3 := by
  sorry

/-- HOL `POLY_SORT_LEMMA` (counting_spheres.hl:729). GIANT. -/
theorem POLY_SORT_LEMMA (P : Set ℂ) (n : ℕ) (s : Set (Set ℂ)) (r : ℝ) (u : ℂ)
    (hs : s = {c : Set ℂ | facetOfC c P}) (hP : polyhedronC P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) (hu : u ≠ 0)
    (hsize : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → Set ℂ, s = f '' Set.Icc 1 n ∧ ∀ j k : ℕ, j ∈ Set.Icc 1 n →
      k ∈ Set.Icc 1 n → j < k → ¬ poly_sort_fn P u (f k) (f j) := by
  sorry

/-- HOL `POLY_SORT` (counting_spheres.hl:746). GIANT. -/
theorem POLY_SORT (P : Set ℂ) (n : ℕ) (s : Set (Set ℂ)) (r : ℝ) (u : ℂ)
    (hs : s = {c : Set ℂ | facetOfC c P}) (hP : polyhedronC P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) (hu : u ≠ 0)
    (hsize : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → Set ℂ, s = f '' Set.Icc 1 n ∧ ∀ j k : ℕ, j ∈ Set.Icc 1 n →
      k ∈ Set.Icc 1 n → j < k →
      Complex.arg (facet_rep_a P (f j) / u) <
        Complex.arg (facet_rep_a P (f k) / u) := by
  sorry

/-- HOL `POLY_SORT_BIJ` (counting_spheres.hl:795). GIANT. -/
theorem POLY_SORT_BIJ (P : Set ℂ) (n : ℕ) (s : Set (Set ℂ)) (r : ℝ) (u : ℂ)
    (hs : s = {c : Set ℂ | facetOfC c P}) (hP : polyhedronC P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) (hu : u ≠ 0)
    (hsize : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → Set ℂ, s = f '' Set.Icc 1 n ∧ Set.BijOn f (Set.Icc 1 n) s ∧
      ∀ j k : ℕ, j ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → j < k →
      Complex.arg (facet_rep_a P (f j) / u) <
        Complex.arg (facet_rep_a P (f k) / u) := by
  sorry

/-- HOL `facet_rep_nz` (counting_spheres.hl:817). -/
theorem facet_rep_nz (P c : Set ℂ) (hP : polyhedronC P) (hc : facetOfC c P) :
    facet_rep_a P c ≠ 0 := by
  have h := facet_rep_props P c hP hc
  intro h0
  rw [h0] at h
  exact absurd h.1 (by simp)

/-- HOL `bisector_point_exists` (counting_spheres.hl:825). GIANT. -/
theorem bisector_point_exists (P c c' : Set ℂ) (r : ℝ) :
    ∃ v : ℂ, ∀ psi : ℝ, polyhedronC P → facetOfC c P → facetOfC c' P → 0 < r →
      (∀ p : ℂ, ‖p‖ < r → p ∈ P) →
      psi = Complex.arg (facet_rep_a P c' / facet_rep_a P c) / 2 →
      (∀ c'' : Set ℂ, facetOfC c'' P →
        Complex.arg (facet_rep_a P c'' / facet_rep_a P c) < 2 * psi → c'' = c) →
      psi < Real.pi / 2 → c' ≠ c →
      v ∈ P ∧ ‖v‖ = r / Real.cos psi ∧
      Complex.arg (v / facet_rep_a P c) = psi ∧
      Complex.arg (facet_rep_a P c' / v) = psi := by
  sorry

/-- HOL `bisector_point` (new_specification, counting_spheres.hl:943). -/
noncomputable def bisector_point (P c c' : Set ℂ) (r : ℝ) : ℂ :=
  Classical.choose (bisector_point_exists P c c' r)

/-- Unfolding of the `bisector_point` specification. -/
theorem bisector_point_props (P c c' : Set ℂ) (r : ℝ) (psi : ℝ)
    (hP : polyhedronC P) (hc : facetOfC c P) (hc' : facetOfC c' P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (hpsi : psi = Complex.arg (facet_rep_a P c' / facet_rep_a P c) / 2)
    (hmin : ∀ c'' : Set ℂ, facetOfC c'' P →
      Complex.arg (facet_rep_a P c'' / facet_rep_a P c) < 2 * psi → c'' = c)
    (hlt : psi < Real.pi / 2) (hne : c' ≠ c) :
    bisector_point P c c' r ∈ P ∧ ‖bisector_point P c c' r‖ = r / Real.cos psi ∧
      Complex.arg (bisector_point P c c' r / facet_rep_a P c) = psi ∧
      Complex.arg (facet_rep_a P c' / bisector_point P c c' r) = psi :=
  Classical.choose_spec (bisector_point_exists P c c' r)
    psi hP hc hc' hr hrad hpsi hmin hlt hne

/-- HOL `regular_spherical_polygon_area_asnFnhk` (counting_spheres.hl:945).
GIANT (relies on the Ysskqoy `asnFnhk` kit). -/
theorem regular_spherical_polygon_area_asnFnhk (h : ℝ) (k : ℕ) (hk : 3 ≤ k)
    (hh : 1 ≤ h ∧ h ≤ h0) :
    regularSphericalPolygonAreaP22
        (h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2) k =
      2 * Real.pi - 2 * k * asnFnhkP22 h k 1 1 1 1 := by
  sorry

/-- HOL `regular_spherical_polygon_area_797` (counting_spheres.hl:955). -/
theorem regular_spherical_polygon_area_797 (k : ℕ) (hk : 3 ≤ k) :
    regularSphericalPolygonAreaP22 (Real.cos 0.797) k =
      2 * Real.pi - 2 * k * asn (Real.cos 0.797 * Real.sin (Real.pi / k)) := by
  unfold regularSphericalPolygonAreaP22
  congr 1

/-- HOL `BIEFJHU_explicit` (counting_spheres.hl:965). GIANT. -/
theorem BIEFJHU_explicit (h : ℝ) (k : ℕ) (hpa : packIneqDefAP22)
    (hh : 1 ≤ h ∧ h ≤ h0) (hk : 3 ≤ k) :
    (0.591 - 0.0331 * k + 0.506 * lfun h) ≤
      max 0 (regularSphericalPolygonAreaP22
        (h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2) k) := by
  sorry

/-- HOL `UKBRPFE_explicit` (counting_spheres.hl:999). GIANT. -/
theorem UKBRPFE_explicit (k : ℕ) (hpa : packIneqDefAP22) (hk : 3 ≤ k) :
    (0.591 - 0.0331 * k + 0.506 * lfun 1 + 1) ≤
      max 0 (regularSphericalPolygonAreaP22 (Real.cos 0.797) k) := by
  sorry

/-- HOL `DLWCHEM_sum` (counting_spheres.hl:1020). GIANT. -/
theorem DLWCHEM_sum (h : ℕ → ℝ) (k : ℕ → ℕ) (n : ℕ) (hpa : packIneqDefAP22)
    (hn : 12 < n)
    (hik : ∀ i : ℕ, i < n → 3 ≤ k i ∧ 1 ≤ h i ∧ h i ≤ h0)
    (hksum : ∑ i ∈ Finset.range n, k i ≤ 6 * n - 12)
    (hasum : ∑ i ∈ Finset.range n,
        max 0 (regularSphericalPolygonAreaP22
          (h i * sqrt3 / 4 + Real.sqrt (1 - (h i / 2) ^ 2) / 2) (k i)) ≤ 4 * Real.pi)
    (hlsum : 12 < ∑ i ∈ Finset.range n, lfun (h i)) : n < 16 := by
  sorry

/-- HOL `XULJEPR_sum` (counting_spheres.hl:1052). GIANT. -/
theorem XULJEPR_sum (h : ℕ → ℝ) (k : ℕ → ℕ) (n : ℕ) (hpa : packIneqDefAP22)
    (hn : 12 < n) (h0eq : h 0 = 1)
    (hik : ∀ i : ℕ, i < n → 3 ≤ k i ∧ 1 ≤ h i ∧ h i ≤ h0)
    (hksum : ∑ i ∈ Finset.range n, k i ≤ 6 * n - 12)
    (hasum : max 0 (regularSphericalPolygonAreaP22 (Real.cos 0.797) (k 0)) +
        ∑ i ∈ Finset.Icc 1 (n - 1),
          max 0 (regularSphericalPolygonAreaP22
            (h i * sqrt3 / 4 + Real.sqrt (1 - (h i / 2) ^ 2) / 2) (k i)) ≤
        4 * Real.pi)
    (hlsum : 12 < ∑ i ∈ Finset.range n, lfun (h i)) : False := by
  sorry

/-- HOL `REAL_CONVEX_ON_SECOND_SECANT` (counting_spheres.hl:1099). GIANT. -/
theorem REAL_CONVEX_ON_SECOND_SECANT (f f' f'' : ℝ → ℝ) (s : Set ℝ)
    (hi : isRealIntervalP22 s) (hs : ¬ ∃ a : ℝ, s = {a})
    (hd1 : ∀ x : ℝ, x ∈ s → HasDerivWithinAt f (f' x) s x)
    (hd2 : ∀ x : ℝ, x ∈ s → HasDerivWithinAt f' (f'' x) s x)
    (hnn : ∀ x : ℝ, x ∈ s → 0 ≤ f'' x) :
    ∀ x y : ℝ, x ∈ s → y ∈ s → f y - f x ≤ f' y * (y - x) := by
  sorry

/-- HOL `asn_sin_t''_alt` (counting_spheres.hl:1122, Calc_derivative form).
GIANT. -/
theorem asn_sin_t_sec_alt (x t alpha : ℝ) (h1 : |Real.sin x * t| < 1)
    (h2 : Real.cos alpha = Real.sin x * t) :
    derivedFormP22 (fun x => 1 - (Real.cos x * t) * (Real.sqrt (1 - (Real.sin x * t) ^ 2))⁻¹)
      (fun x => t * (1 - t ^ 2) * Real.sin x * (|Real.sin alpha| ^ 3)⁻¹) x
      (Set.Icc 0 Real.pi) := by
  sorry

/-- HOL `real_interval_not_sing` (counting_spheres.hl:1159). -/
theorem real_interval_not_sing (a b : ℝ) (h : a < b) :
    ¬ ∃ c : ℝ, Set.Icc a b = {c} := by
  rintro ⟨c, hc⟩
  have ha : a = c := by
    have : a ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨le_refl a, le_of_lt h⟩
    rw [hc] at this
    exact Set.mem_singleton_iff.mp this
  have hb : b = c := by
    have : b ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨le_of_lt h, le_refl b⟩
    rw [hc] at this
    exact Set.mem_singleton_iff.mp this
  exact absurd (ha.trans hb.symm) (ne_of_lt h)

/-- HOL `g_convex` (counting_spheres.hl:1173). GIANT. -/
theorem g_convex (t : ℝ) (ht : 0 < t ∧ t < 1) :
    ∃ s : Set ℝ, ∃ f' f'' : ℝ → ℝ,
      s = Set.Icc 0 Real.pi ∧ isRealIntervalP22 s ∧ ¬ ∃ a : ℝ, s = {a} ∧
      (∀ x : ℝ, x ∈ s → HasDerivWithinAt (fun x => x - asn (Real.sin x * t)) (f' x) s x) ∧
      (∀ x : ℝ, x ∈ s → HasDerivWithinAt f' (f'' x) s x) ∧
      (∀ x : ℝ, x ∈ s → 0 ≤ f'' x) := by
  sorry

/-- HOL `GOTCJAH_convex_sum` (counting_spheres.hl:1230). GIANT. -/
theorem GOTCJAH_convex_sum (n : ℕ) (t : ℝ) (bet : ℕ → ℝ) (u : ℝ) (hn : 0 < n)
    (hu1 : u ≤ n * Real.pi) (hu2 : 0 ≤ u) (ht : 0 < t ∧ t < 1)
    (hsum : ∑ i ∈ Finset.range n, bet i = u)
    (hb : ∀ i : ℕ, i < n → 0 ≤ bet i ∧ bet i ≤ Real.pi) :
    u - n * asn (Real.sin (u / n) * t) ≤
      ∑ i ∈ Finset.range n, (bet i - asn (Real.sin (bet i) * t)) := by
  sorry

/-- HOL `dih_dot` (counting_spheres.hl:1272). GIANT. -/
theorem dih_dot (u v w : V3) (hu : u ≠ 0) (h1 : (w - u) ⬝ᵥ v = 0)
    (h2 : (w - u) ⬝ᵥ u = 0) : dihV 0 u v w = Real.pi / 2 := by
  sorry

/-- HOL `abs_1_prod` (counting_spheres.hl:1295). -/
theorem abs_1_prod (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
  rw [abs_mul]
  exact le_trans (mul_le_mul hx hy (by norm_num) (by norm_num)) (by norm_num)

/-- HOL `sloc2_ortho` (counting_spheres.hl:1306). GIANT. -/
theorem sloc2_ortho (va vb vc : V3)
    (hcp : ¬ Coplanar ({0, va, vb, vc} : Set V3))
    (h : dihV 0 vc va vb = Real.pi / 2) :
    let bet := dihV 0 vb vc va
    let alp := dihV 0 va vb vc
    let t := Real.cos (arcV 0 vb vc)
    Real.cos alp = Real.sin bet * t := by
  sorry

/-- HOL `vol_solid_triangle_ortho` (counting_spheres.hl:1335). GIANT. -/
theorem vol_solid_triangle_ortho (u v w : V3)
    (hcp : ¬ Coplanar ({0, u, v, w} : Set V3))
    (h1 : (w - u) ⬝ᵥ v = 0) (h2 : (w - u) ⬝ᵥ u = 0) :
    let bet := dihV 0 v u w
    let t := Real.cos (arcV 0 v u)
    3 * volSolidTriangleP22 0 u v w 1 = bet - asn (Real.sin bet * t) := by
  sorry

/-- HOL `INJ_IMAGE` (counting_spheres.hl:1386). -/
theorem INJ_IMAGE {α β : Type*} {f : α → β} {a : Set α} {b : Set β}
    (h : Set.InjOn f a ∧ f '' a ⊆ b) : f '' a ⊆ b := h.2

/-- HOL `INJ_CARD` (counting_spheres.hl:1395). -/
theorem INJ_CARD {α β : Type*} [DecidableEq α] [DecidableEq β] {a : Set α}
    {b : Set β} {f : α → β} (hb : b.Finite)
    (h : Set.InjOn f a ∧ f '' a ⊆ b) : a.Finite ∧ a.ncard ≤ b.ncard := by
  have him : (f '' a).Finite := hb.subset h.2
  have hfa : a.Finite := (Set.finite_image_iff h.1).mp him
  exact ⟨hfa, by
    rw [← Set.InjOn.ncard_image h.1]
    exact Set.ncard_le_ncard h.2 hb⟩

/-- HOL `card_packing_ball` (counting_spheres.hl:1418). GIANT. -/
theorem card_packing_ball (r : ℝ) (hr : 0 ≤ r) :
    ∃ n : ℕ, ∀ S : Set V3, Packing S → S ⊆ Metric.ball 0 r →
      S.Finite ∧ S.ncard ≤ n := by
  sorry

/-- HOL `card_packing_annulus` (counting_spheres.hl:1454). GIANT. -/
theorem card_packing_annulus :
    ∃ n : ℕ, ∀ S : Set V3, Packing S → S ⊆ ballAnnulus →
      S.Finite ∧ S.ncard ≤ n := by
  sorry

/-- HOL `FINITE_MAX_EXISTS` (counting_spheres.hl:1479). -/
theorem FINITE_MAX_EXISTS (s : Set ℕ) (hne : s ≠ ∅) (hf : s.Finite) :
    ∃ a : ℕ, a ∈ s ∧ ∀ b : ℕ, b ∈ s → b ≤ a := by
  exact Set.exists_max_image s (fun b => b) hf (Set.nonempty_iff_ne_empty.mpr hne)

/-- HOL `PACKING_INSERT` (counting_spheres.hl:1518). -/
theorem PACKING_INSERT (v : V3) (S : Set V3) (hP : Packing S) (hv : v ∉ S)
    (hd : ∀ w ∈ S, 2 ≤ dist v w) : Packing (insert v S) := by
  intro u hu w hw hdist
  simp only [Set.mem_insert_iff] at hu hw
  rcases hu with hueq | huS
  · rw [hueq] at hdist ⊢
    rcases hw with hweq | hwS
    · rw [hweq] at hdist ⊢
    · exact absurd hdist (not_lt.mpr (hd w hwS))
  · rcases hw with hweq | hwS
    · rw [hweq] at hdist ⊢
      rw [dist_comm u v] at hdist
      exact absurd hdist (not_lt.mpr (hd u huS))
    · exact hP u huS w hwS hdist

/-- HOL `weak_saturation` (counting_spheres.hl:1527). GIANT. -/
theorem weak_saturation (W S : Set V3) (r : ℝ) (hr : 2 ≤ r ∧ r ≤ 2 * h0)
    (hSW : S ⊆ W) (hP : Packing W) (hW : W ⊆ ballAnnulus)
    (hsep : ∀ v w : V3, S v → W w → dist v w < r → v = w) :
    ∃ V : Set V3, V ⊆ ballAnnulus ∧ Packing V ∧ weaklySaturatedP22 V r (2 * h0) ∧
      V.Finite ∧ W ⊆ V ∧
      (∀ v w : V3, S v → V w → dist v w < r → v = w) := by
  sorry

/-- HOL `dropout_pad2d3d` (counting_spheres.hl:1664). -/
theorem dropout_pad2d3d (x : ℂ) : dropout3P22 (pad2d3dP22 x) = x := by
  unfold dropout3P22 pad2d3dP22
  rw [coe_toLp]

/-- HOL `pad2d3d_dropout` (counting_spheres.hl:1680). -/
theorem pad2d3d_dropout (v : V3) (h : (v : Fin 3 → ℝ) 2 = 0) :
    pad2d3dP22 (dropout3P22 v) = v := by
  have hcoe : ∀ w : V3, WithLp.toLp 2 w.ofLp = w := fun w => WithLp.toLp_ofLp 2 w
  refine (hcoe (pad2d3dP22 (dropout3P22 v))).symm.trans ?_
  have hcoe2 : (pad2d3dP22 (dropout3P22 v)).ofLp = v.ofLp := by
    funext i
    fin_cases i <;>
      simp [pad2d3dP22, dropout3P22, WithLp.ofLp_toLp, h]
  rw [hcoe2]

/-- HOL `pad2d3d_dropout_lemma` (counting_spheres.hl:1710). -/
theorem pad2d3d_dropout_lemma {α : Type*} (A : Set α) (P : α → Prop) (h : α → α)
    (h1 : ∀ x ∈ A, P x) (h2 : ∀ x : α, P x → h x = x) : h '' A = A := by
  ext y
  simp only [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [h2 x (h1 x hx)]
  · intro hy
    exact ⟨y, hy, h2 y (h1 y hy)⟩

/-- HOL `pad2d3d_dot_v` (counting_spheres.hl:1719). -/
theorem pad2d3d_dot_v (x y : ℂ) :
    (pad2d3dP22 x) ⬝ᵥ (pad2d3dP22 y) = dot2 x y := by
  rw [← inner_eq_dot, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, dot2, Complex.mul_re, Fin.sum_univ_three, WithLp.ofLp_toLp, pad2d3dP22]
  ring_nf

/-- HOL `pad_in` (counting_spheres.hl:1727). -/
theorem pad_in (x : ℂ) (A : Set V3) (hA : ∀ u ∈ A, (u : Fin 3 → ℝ) 2 = 0) :
    pad2d3dP22 x ∈ A ↔ x ∈ dropout3P22 '' A := by
  constructor
  · intro hx
    exact ⟨pad2d3dP22 x, hx, (dropout_pad2d3d x).symm⟩
  · rintro ⟨u, hu, hxu⟩
    rw [← hxu]
    rwa [pad2d3d_dropout u (hA u hu)]

/-- HOL `pad2d3d_facet` (counting_spheres.hl:1737). GIANT. -/
theorem pad2d3d_facet (P : Set V3) (n : ℕ) (hP : polyhedron P)
    (hz : ∀ u ∈ P, (u : Fin 3 → ℝ) 2 = 0)
    (hn : ({c : Set V3 | FacetOf c P}).Finite ∧ ({c : Set V3 | FacetOf c P}).ncard = n) :
    ({d : Set ℂ | facetOfC d (dropout3P22 '' P)}).Finite ∧
      ({d : Set ℂ | facetOfC d (dropout3P22 '' P)}).ncard = n := by
  sorry

/-- HOL `complex_frac_cancel` (counting_spheres.hl:1767). -/
theorem complex_frac_cancel (a b c : ℂ) (hb : b ≠ 0) :
    (a / b) / (c / b) = a / c := by
  by_cases hc : c = 0
  · simp [hc]
  · field_simp

/-- HOL `REAL_CX0` (counting_spheres.hl:1781). HOL `real z` ↔ `Complex.im z = 0`. -/
theorem REAL_CX0 (z : ℂ) (h1 : Complex.im z = 0) (h2 : Complex.re z = 0) :
    z = 0 := by
  exact Complex.ext (by simpa using h2) (by simpa using h1)

/-- HOL `ARG_INV_ALT` (counting_spheres.hl:1791). GIANT. -/
theorem ARG_INV_ALT (u x y : ℂ) (hu : u ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Complex.arg (x / u) ≠ Complex.arg (y / u)) :
    Complex.arg (x / y) = 2 * Real.pi - Complex.arg (y / x) := by
  sorry

/-- HOL `ARG_ORDER` (counting_spheres.hl:1822). GIANT. -/
theorem ARG_ORDER (u : ℂ) (h : ℕ → ℂ) (n : ℕ) (hu : u ≠ 0)
    (h1 : ∀ i : ℕ, i ∈ Finset.Icc 1 n → h i ≠ 0)
    (h2 : ∀ i j : ℕ, i ∈ Finset.Icc 1 n → j ∈ Finset.Icc 1 n → i < j →
      Complex.arg (h i / u) < Complex.arg (h j / u))
    (h3 : h (n + 1) = h 1) :
    ∀ i j : ℕ, i ∈ Finset.Icc 1 n → j ∈ Finset.Icc 1 n → i ≠ j →
      Complex.arg (h (i + 1) / h i) ≤ Complex.arg (h j / h i) := by
  sorry

/-- HOL `POLYSORT_BIJ2` (counting_spheres.hl:1964). GIANT. -/
theorem POLYSORT_BIJ2 (P : Set ℂ) (n : ℕ) (s : Set (Set ℂ)) (r : ℝ) (u : ℂ)
    (hs : s = {c : Set ℂ | facetOfC c P}) (hb : Bornology.IsBounded P) (hP : polyhedronC P)
    (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) (hu : u ≠ 0)
    (hsize : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → Set ℂ, s = f '' Set.Icc 1 n ∧ Set.BijOn f (Set.Icc 1 n) s ∧
      (∀ i k : ℕ, i ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → i ≠ k →
        Complex.arg (facet_rep_a P (f (i + 1)) / facet_rep_a P (f i)) ≤
          Complex.arg (facet_rep_a P (f k) / facet_rep_a P (f i))) ∧
      (∀ i : ℕ, i ∈ Set.Icc 1 n →
        Complex.arg (facet_rep_a P (f (i + 1)) / facet_rep_a P (f i)) < Real.pi) ∧
      f (n + 1) = f 1 ∧
      (∀ j k : ℕ, j ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → j < k →
        Complex.arg (facet_rep_a P (f j) / u) <
          Complex.arg (facet_rep_a P (f k) / u)) := by
  sorry

/-- HOL `EMPTY_NOT_EXISTS_IN` (counting_spheres.hl:2104). -/
theorem EMPTY_NOT_EXISTS_IN {α : Type*} (a : Set α) :
    a = ∅ ↔ ¬ ∃ x : α, x ∈ a := by
  simp [Set.eq_empty_iff_forall_notMem]

/-- HOL `EUSOTYP_simple` (counting_spheres.hl:2112). GIANT. -/
theorem EUSOTYP_simple (P : Set ℂ) (s : Set (Set ℂ)) (r n : ℕ) (u2 : ℂ)
    (hP : polyhedronC P) (hb : Bornology.IsBounded P) (hs : s = {c : Set ℂ | facetOfC c P})
    (hsize : s.Finite ∧ s.ncard = n) (hr : 0 < r) (hu : u2 ≠ 0)
    (hrad : ∀ p2 : ℂ, ‖p2‖ < r → p2 ∈ P) :
    ∃ g h : ℕ → ℂ,
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → g i ∈ P ∧ ‖g i‖ = r) ∧
      g (n + 1) = g 1 ∧
      (∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j < k →
        Complex.arg (g j / u2) < Complex.arg (g k / u2)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → h i ∈ P ∧
        ‖h i‖ = r / Real.cos (Complex.arg (g (i + 1) / g i) / 2)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        Complex.arg (h i / g i) = Complex.arg (g (i + 1) / g i) / 2 ∧
        Complex.arg (g (i + 1) / h i) = Complex.arg (g (i + 1) / g i) / 2) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        dot2 (g i) (h i - g i) = 0 ∧ dot2 (g (i + 1)) (h i - g (i + 1)) = 0) ∧
      1 < n ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → g i ≠ 0) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → h i ≠ 0) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → Complex.arg (g (i + 1) / g i) < Real.pi) := by
  sorry

/-- HOL `pad2d3d_SUB` (counting_spheres.hl:2325). -/
theorem pad2d3d_SUB (x y : ℂ) :
    pad2d3dP22 x - pad2d3dP22 y = pad2d3dP22 (x - y) := by
  have hcoe : ∀ w : V3, WithLp.toLp 2 w.ofLp = w := fun w => WithLp.toLp_ofLp 2 w
  have h1 : (pad2d3dP22 x - pad2d3dP22 y).ofLp = (pad2d3dP22 (x - y)).ofLp := by
    funext i
    fin_cases i <;>
      simp [pad2d3dP22, WithLp.ofLp_toLp]
  rw [← hcoe (pad2d3dP22 x - pad2d3dP22 y), h1, hcoe (pad2d3dP22 (x - y))]

/-- HOL `EUSOTYP_general` (counting_spheres.hl:2336). GIANT. -/
theorem EUSOTYP_general (P A : Set V3) (n : ℕ) (s : Set (Set V3)) (r : ℝ)
    (u0 u1 u2 : V3) (hP : polyhedron P) (hb : Bornology.IsBounded P) (hPA : P ⊆ A)
    (hs : s = {c : Set V3 | FacetOf c P})
    (hsize : s.Finite ∧ s.ncard = n) (hr : 0 < r) (hu2 : u2 ≠ u0) (hu1 : u1 ≠ u0)
    (hu0 : u0 ∈ P) (hu2A : u2 ∈ A)
    (hA : ∀ v : V3, v ∈ A ↔ (v - u0) ⬝ᵥ (u1 - u0) = 0)
    (hrad : ∀ p : V3, dist p u0 < r → p ∈ A → p ∈ P) :
    ∃ g h : ℕ → V3,
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → g i ∈ P ∧ dist (g i) u0 = r) ∧
      g (n + 1) = g 1 ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → h i ∈ P ∧
        ‖h i - u0‖ = r / Real.cos (azim u0 u1 (g i) (g (i + 1)) / 2)) ∧
      (∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j < k →
        azim u0 u1 u2 (g j) < azim u0 u1 u2 (g k)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        azim u0 u1 (g i) (h i) = azim u0 u1 (g i) (g (i + 1)) / 2 ∧
        azim u0 u1 (h i) (g (i + 1)) = azim u0 u1 (g i) (g (i + 1)) / 2) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        (g i - u0) ⬝ᵥ (h i - g i) = 0 ∧ (g (i + 1) - u0) ⬝ᵥ (h i - g (i + 1)) = 0) ∧
      1 < n ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → g i ≠ u0) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → h i ≠ u0) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → azim u0 u1 (g i) (g (i + 1)) < Real.pi) := by
  sorry

/-- HOL `AZIM_SUM_LE` (counting_spheres.hl:2430). GIANT. -/
theorem AZIM_SUM_LE (x y z w1 w2 w3 : V3)
    (h1 : ¬ Collinear3 x y z) (h2 : ¬ Collinear3 x y w1) (h3 : ¬ Collinear3 x y w2)
    (h4 : ¬ Collinear3 x y w3)
    (h5 : azim x y z w1 ≤ azim x y z w2) (h6 : azim x y z w2 ≤ azim x y z w3) :
    azim x y w1 w3 = azim x y w1 w2 + azim x y w2 w3 := by
  sorry

/-- HOL `AZIM_NN` (counting_spheres.hl:2454). -/
theorem AZIM_NN (x y z u : V3) : 0 ≤ azim x y z u := azim_nonneg x y z u

/-- HOL `AZIM_BASE_SHIFT_LT` (counting_spheres.hl:2463). GIANT. -/
theorem AZIM_BASE_SHIFT_LT (x y z z' w1 w2 w3 : V3)
    (h1 : ¬ Collinear3 x y z) (h2 : ¬ Collinear3 x y z') (h3 : ¬ Collinear3 x y w1)
    (h4 : ¬ Collinear3 x y w2) (h5 : ¬ Collinear3 x y w3)
    (h6 : azim x y z w1 < azim x y z w2) (h7 : azim x y z w2 < azim x y z w3)
    (h8 : azim x y z' w1 < azim x y z' w3) :
    azim x y z' w1 < azim x y z' w2 ∧ azim x y z' w2 < azim x y z' w3 := by
  sorry

/-- HOL `AZIM_COMP_LT` (counting_spheres.hl:2513). GIANT. -/
theorem AZIM_COMP_LT (x y z u v : V3) (h1 : 0 < azim x y z u)
    (h2 : azim x y z u < azim x y z v) : azim x y v z < azim x y u z := by
  sorry

/-- HOL `AZIM_COMP_LE` (counting_spheres.hl:2524). GIANT. -/
theorem AZIM_COMP_LE (x y z u v : V3) (h1 : 0 < azim x y z u)
    (h2 : azim x y z u ≤ azim x y z v) : azim x y v z ≤ azim x y u z := by
  sorry

/-- HOL `WEDGE_ORDER_DISJOINT` (counting_spheres.hl:2535). GIANT. -/
theorem WEDGE_ORDER_DISJOINT (x y z : V3) (n : ℕ) (g : ℕ → V3)
    (h1 : ¬ Collinear3 x y z)
    (h2 : ∀ i : ℕ, i ∈ Finset.Icc 1 n → ¬ Collinear3 x y (g i))
    (h3 : g (n + 1) = g 1)
    (h4 : ∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j < k →
      azim x y z (g j) < azim x y z (g k)) :
    ∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j ≠ k →
      (wedge x y (g j) (g (j + 1)) ∩ wedge x y (g k) (g (k + 1))) = ∅ := by
  sorry

/-- HOL `ORDER_AZIM_SUM2Pi` (counting_spheres.hl:2633). GIANT. -/
theorem ORDER_AZIM_SUM2Pi (x y z : V3) (n : ℕ) (g : ℕ → V3)
    (h1 : ¬ Collinear3 x y z)
    (h2 : ∀ i : ℕ, i ∈ Finset.Icc 1 n → ¬ Collinear3 x y (g i))
    (h3 : g (n + 1) = g 1) (hn : 1 < n)
    (h4 : ∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j < k →
      azim x y z (g j) < azim x y z (g k)) :
    ∑ i ∈ Finset.Icc 1 n, azim x y (g i) (g (i + 1)) = 2 * Real.pi := by
  sorry

/-- HOL `AFFINE_VEC0` (counting_spheres.hl:2680). GIANT. -/
theorem AFFINE_VEC0 (u : V3) (t : ℝ) (ht : t ≠ 1) :
    (0 : V3) ∈ affineSpan ℝ ({u, t • u} : Set V3) := by
  sorry

/-- HOL `RELATIVE_INTERIOR_AFFINE_FACE` (counting_spheres.hl:2702). GIANT. -/
theorem RELATIVE_INTERIOR_AFFINE_FACE (C : Set V3) (p : V3) (f : Set V3)
    (hc : Convex ℝ C) (hf : FaceOf f C) (hap : p ∈ (affineSpan ℝ f : Set V3))
    (hip : p ∈ intrinsicInterior ℝ C) : f = C := by
  sorry

/-- HOL `SUBSET_P_HULL` (counting_spheres.hl:2720). -/
theorem SUBSET_P_HULL (P S : Set V3) : S ⊆ hullP22 P S := by
  show S ⊆ convexHull ℝ (P ∪ S)
  exact subset_trans (Set.subset_union_right) (subset_convexHull ℝ (P ∪ S))

/-- HOL `FCHANGED_AFFINE` (counting_spheres.hl:2724). GIANT. -/
theorem FCHANGED_AFFINE (p f : Set V3) (hp : polyhedron p) (hb : Bornology.IsBounded p)
    (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    fchanged f ∩ (affineSpan ℝ f : Set V3) = intrinsicInterior ℝ f := by
  sorry

/-- HOL `RCONE_PREP` (counting_spheres.hl:2765). -/
theorem RCONE_PREP (p v u0 : V3) (b t : ℝ) (hb : 0 < b) (hv : v ≠ 0)
    (hvv : 0 < v ⬝ᵥ v) (hu0 : u0 = (b / (v ⬝ᵥ v)) • v) (ht1 : 0 < t) (ht2 : t < 1)
    (hpv : p ⬝ᵥ v = b) :
    u0 ⬝ᵥ u0 = b * b / (v ⬝ᵥ v) ∧
      p ⬝ᵥ u0 = b * b / (v ⬝ᵥ v) ∧
      dist p u0 ^ 2 = p ⬝ᵥ p - b * b / (v ⬝ᵥ v) := by
  sorry

/-- HOL `RCONE_DISK` (counting_spheres.hl:2802). GIANT. -/
theorem RCONE_DISK (p v u0 : V3) (b r t : ℝ) (hb : 0 < b) (hv : v ≠ 0)
    (hvv : 0 < v ⬝ᵥ v) (hd : dist p u0 < r)
    (hu0 : u0 = (b / (v ⬝ᵥ v)) • v) (ht1 : 0 < t) (ht2 : t < 1)
    (hpv : p ⬝ᵥ v = b)
    (hr : r = b * Real.sqrt (1 - t ^ 2) / (t * ‖v‖)) :
    p ∈ rconeGt 0 v t := by
  sorry

/-- HOL `RDISK_R` (counting_spheres.hl:2859). GIANT. -/
theorem RDISK_R (v u0 : V3) (b t : ℝ) (hb : 0 < b) (hv : v ≠ 0) (hvv : 0 < v ⬝ᵥ v)
    (ht1 : 0 < t) (ht2 : t < 1) (hu0 : u0 = (b / (v ⬝ᵥ v)) • v) :
    ∃ r : ℝ, 0 < r ∧
      (∀ p : V3, dist p u0 < r → p ⬝ᵥ v = b → p ∈ rconeGt 0 v t) ∧
      (∀ w : V3, dist w u0 = r → w ⬝ᵥ v = b → Real.cos (arcV 0 u0 w) = t) := by
  sorry

/-- HOL `FCHANGED_MEASURABLE` (counting_spheres.hl:2940). GIANT. -/
theorem FCHANGED_MEASURABLE (p f : Set V3) (r : ℝ) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    MeasurableSet (fchanged f ∩ normballP22 0 r) := by
  sorry

/-- HOL `RADIAL_NORMBALL` (counting_spheres.hl:2968). -/
theorem RADIAL_NORMBALL (p : V3) (r : ℝ) : radialNorm r p (normballP22 p r) := by
  refine ⟨fun y hy => hy, ?_⟩
  intro u hu t ht1 ht2
  have hu' : ‖u‖ < r := by
    have h1 : dist (p + u) p < r := Metric.mem_ball.mp hu
    rwa [dist_eq_norm, add_sub_cancel_left] at h1
  have htn : ‖t • u‖ = t * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht1]
  have h2 : dist (p + t • u) p < r := by
    rw [dist_eq_norm, add_sub_cancel_left, htn]
    linarith
  exact h2

/-- HOL `FCHANGED_RADIAL` (counting_spheres.hl:2986). GIANT. -/
theorem FCHANGED_RADIAL (p f : Set V3) (r : ℝ) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    radialNorm r 0 (fchanged f ∩ normballP22 0 r) := by
  sorry

/-- HOL `WEDGE_SPLIT` (counting_spheres.hl:3025). GIANT. -/
theorem WEDGE_SPLIT (u0 u1 u2 u3 w : V3) (h1 : ¬ Collinear3 u0 u1 u2)
    (h2 : ¬ Collinear3 u0 u1 u3) (hw : w ∈ wedge u0 u1 u2 u3) :
    ¬ Collinear3 u0 u1 w ∧
      wedge u0 u1 u2 w ∩ wedge u0 u1 w u3 = ∅ ∧
      wedge u0 u1 u2 w ⊆ wedge u0 u1 u2 u3 ∧
      wedge u0 u1 w u3 ⊆ wedge u0 u1 u2 u3 := by
  sorry

/-- HOL `cone0_subset_lune` (counting_spheres.hl:3058). GIANT. -/
theorem cone0_subset_lune (u0 u1 u2 u3 : V3) :
    cone0P22 u0 {u1, u2, u3} ⊆ affGe {u0, u1} {u2, u3} := by
  sorry

/-- HOL `COLLINEAR_UNEQUAL` (counting_spheres.hl:3075). -/
theorem COLLINEAR_UNEQUAL {a : Type*} [AddCommGroup a] [Module ℝ a] (u0 u1 u2 : a)
    (h : ¬ Collinear ℝ ({u0, u1, u2} : Set a)) :
    u2 ∉ ({u0, u1} : Set a) ∧ u1 ≠ u0 := by
  refine ⟨?_, ?_⟩
  · intro hu
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu2 | hu2
    · have hset : ({u0, u1, u2} : Set a) = {u0, u1} := by
        rw [hu2]
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset] at h
      exact h (collinear_pair ℝ u0 u1)
    · have hset : ({u0, u1, u2} : Set a) = {u0, u1} := by
        rw [hu2]
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [hset] at h
      exact h (collinear_pair ℝ u0 u1)
  · intro hu
    rw [hu] at h
    have hset : ({u0, u0, u2} : Set a) = {u0, u2} := by
      ext z
      simp
    rw [hset] at h
    exact h (collinear_pair ℝ u0 u2)

/-- HOL `HAS_SIZE_GE_2` (counting_spheres.hl:3089). -/
theorem HAS_SIZE_GE_2 {α : Type*} [DecidableEq α] (s : Set α) (hf : s.Finite)
    (h : 1 < s.ncard) : ∀ x ∈ s, ∃ y ∈ s, y ≠ x := by
  intro x hx
  by_contra hno
  push_neg at hno
  have hset : s = {x} := by
    ext y
    simp only [Set.mem_singleton_iff]
    constructor
    · exact fun hy => hno y hy
    · intro hy
      rw [hy]
      exact hx
  rw [hset] at h
  simp at h

/-- HOL `TWO_IMP_HAS_SIZE_GE_2` (counting_spheres.hl:3106). -/
theorem TWO_IMP_HAS_SIZE_GE_2 {α : Type*} [DecidableEq α] (s : Set α) (x y : α)
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) (hf : s.Finite) : 1 < s.ncard := by
  have hsub : ({x, y} : Set α) ⊆ s := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have h2 : ({x, y} : Set α).ncard = 2 := by
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, hxy]
  have hle := Set.ncard_le_ncard hsub hf
  rw [h2] at hle
  exact hle

/-- HOL `AFF_GT_RELATIVE_INTERIOR` (counting_spheres.hl:3120). GIANT. -/
theorem AFF_GT_RELATIVE_INTERIOR (s : Set V3) (hf : s.Finite) (h : 1 < s.ncard) :
    affGe (∅ : Set V3) s ⊆ intrinsicInterior ℝ (convexHull ℝ s) := by
  sorry

/-- HOL `NOT_COLLINEAR_AFF_DIM_2` (counting_spheres.hl:3160). GIANT. -/
theorem NOT_COLLINEAR_AFF_DIM_2 (u0 u1 u2 : V3) (h : ¬ Collinear3 u0 u1 u2) :
    affDim ({u0, u1, u2} : Set V3) = 2 := by
  sorry

/-- HOL `FACET_AFF_DIM_2` (counting_spheres.hl:3171). GIANT. -/
theorem FACET_AFF_DIM_2 (p f : Set V3) (hp : polyhedron p)
    (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p) : affDim f = 2 := by
  sorry

/-- HOL `CONE0_FCHANGED_AFF_GT` (counting_spheres.hl:3185). GIANT. -/
theorem CONE0_FCHANGED_AFF_GT (s : Set V3) (hf : s.Finite) (h : 1 < s.ncard)
    (h0 : (0 : V3) ∉ s) : cone0P22 0 s ⊆ fchanged (convexHull ℝ s) := by
  sorry

/-- HOL `CONE0_FCHANGED` (counting_spheres.hl:3288). GIANT. -/
theorem CONE0_FCHANGED (p f : Set V3) (u0 u1 u2 : V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p)
    (hc : ¬ Collinear3 u0 u1 u2) (hsub : {u0, u1, u2} ⊆ f) :
    cone0P22 0 {u0, u1, u2} ⊆ fchanged f := by
  sorry

/-- HOL `collinear_translate_axis` (counting_spheres.hl:3332). GIANT. -/
theorem collinear_translate_axis (t : ℝ) (u1 u2 : V3) :
    Collinear3 (t • u1) u1 u2 ↔ Collinear3 0 (u1 - t • u1) u2 := by
  sorry

/-- HOL `azim_axis` (counting_spheres.hl:3347). GIANT. -/
theorem azim_axis (t : ℝ) (u1 u w : V3)
    (h1 : ¬ Collinear3 (t • u1) u1 u) (h2 : ¬ Collinear3 (t • u1) u1 w) :
    azim (t • u1) u1 u w = azim 0 (u1 - t • u1) u w := by
  sorry

/-- HOL `EUSOTYP2_general` (counting_spheres.hl:3411). GIANT. -/
theorem EUSOTYP2_general (P : Set V3) (c3 : Set V3) (A : Set V3) (n : ℕ) (t : ℝ)
    (u v : V3) (b : ℝ) (hp : polyhedron P) (hb : Bornology.IsBounded P)
    (hi : (0 : V3) ∈ interior P) (hfac : FacetOf c3 P) (hc3A : c3 ⊆ A)
    (hPA : P ∩ A = c3) (hAeq : A = {p : V3 | p ⬝ᵥ v = b})
    (hsize : ({c : Set V3 | FacetOf c c3}).Finite ∧
      ({c : Set V3 | FacetOf c c3}).ncard = n)
    (hbpos : 0 < b) (ht1 : 0 < t) (ht2 : t < 1) (hcv : ¬ Collinear3 0 v u)
    (hsub1 : rconeGt 0 v t ⊆ fchanged c3)
    (hsub2 : rconeGt 0 v t ∩ A ⊆ c3) :
    ∃ g h : ℕ → V3,
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → g i ∈ c3 ∧ Real.cos (arcV 0 v (g i)) = t) ∧
      g (n + 1) = g 1 ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → h i ∈ c3) ∧
      (∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j < k →
        azim 0 v u (g j) < azim 0 v u (g k)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        azim 0 v (g i) (h i) = azim 0 v (g i) (g (i + 1)) / 2 ∧
        azim 0 v (h i) (g (i + 1)) = azim 0 v (g i) (g (i + 1)) / 2) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        (h i - g i) ⬝ᵥ v = 0 ∧ (h i - g (i + 1)) ⬝ᵥ v = 0 ∧
        (h i - g i) ⬝ᵥ g i = 0 ∧ (h i - g (i + 1)) ⬝ᵥ g (i + 1) = 0) ∧
      1 < n ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → ¬ Collinear3 0 v (g i)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → ¬ Collinear3 0 v (h i)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → azim 0 v (g i) (g (i + 1)) < Real.pi) := by
  sorry

/-- HOL `CONE0_SUBSET_WEDGE` (counting_spheres.hl:3752). GIANT. -/
theorem CONE0_SUBSET_WEDGE (v u w : V3) (h1 : ¬ Collinear3 0 v u)
    (h2 : ¬ Collinear3 0 v w) (h3 : 0 < azim 0 v u w) (h4 : azim 0 v u w < Real.pi) :
    cone0P22 0 {v, u, w} ⊆ wedge 0 v u w := by
  sorry

/-- HOL `CONE0_AFF_GT` (counting_spheres.hl:3770). -/
theorem CONE0_AFF_GT (x : V3) (U : Set V3) : cone0P22 x U = affGe {x} U := rfl

/-- HOL `DISJOINT0_SCALE` (counting_spheres.hl:3778). -/
theorem DISJOINT0_SCALE (t : ℝ) (u0 u1 u2 : V3)
    (hd : Disjoint ({0} : Set V3) {u0, u1, u2}) (ht : t ≠ 0) :
    Disjoint ({0} : Set V3) {t • u0, u1, u2} := by
  have h0 : (0 : V3) ∉ ({u0, u1, u2} : Set V3) := Set.disjoint_singleton_left.mp hd
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_insert_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl hx
  rcases hx with hx | hx | hx
  · rcases smul_eq_zero.mp hx.symm with hx' | hx'
    · exact ht hx'
    · rw [hx'] at h0
      exact h0 (Set.mem_insert_iff.mpr (Or.inl rfl))
  · exact h0 (by rw [hx]; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inl rfl))))
  · exact h0 (by rw [hx]; exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inr rfl))))

/-- HOL `CONE0_SCALE` (counting_spheres.hl:3792). GIANT. -/
theorem CONE0_SCALE (t : ℝ) (u0 u1 u2 : V3)
    (hd : Disjoint ({0} : Set V3) {u0, u1, u2}) (ht : 0 < t) :
    cone0P22 0 {u0, u1, u2} = cone0P22 0 {t • u0, u1, u2} := by
  sorry

/-- HOL `CONE0_FCHANGED_SCALE` (counting_spheres.hl:3837). GIANT. -/
theorem CONE0_FCHANGED_SCALE (p f : Set V3) (u0 u1 u2 : V3) (t : ℝ)
    (hp : polyhedron p) (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p)
    (hf : FacetOf f p) (hcp : ¬ Coplanar ({0, u0, u1, u2} : Set V3))
    (hsub : {t • u0, u1, u2} ⊆ f) (ht : 0 < t) :
    cone0P22 0 {u0, u1, u2} ⊆ fchanged f := by
  sorry

/-- HOL `gotcjah_sol_half` (counting_spheres.hl:3879). GIANT. -/
theorem gotcjah_sol_half (c3 : Set V3) (v : V3) (b : ℝ) (P W : Set V3) (t rho : ℝ)
    (bet : ℝ) (w0 w1 : V3) (s : ℝ)
    (hP : polyhedron P) (hbP : Bornology.IsBounded P) (hb : 0 < b)
    (hi : (0 : V3) ∈ interior P) (hf : FacetOf c3 P) (hfc : fchanged c3 = W)
    (ht : 0 < t ∧ t < 1) (hrho : 0 < rho) (hs : 0 < s)
    (hPA : P ∩ {p : V3 | p ⬝ᵥ v = b} = c3) (hsub : rconeGt 0 v t ⊆ W)
    (hv : v ≠ 0) (hvv : 0 < v ⬝ᵥ v) (hcos : Real.cos (arcV 0 v w0) = t)
    (hsv : s • v ∈ c3) (hw0 : w0 ∈ c3) (hw1 : w1 ∈ c3)
    (hnc : ¬ Collinear3 0 v w0) (hnc1 : ¬ Collinear3 0 v w1)
    (hpos : 0 < dihV 0 v w0 w1) (hlt : dihV 0 v w0 w1 < Real.pi)
    (hbet : dihV 0 v w0 w1 = bet) (h1 : (w1 - w0) ⬝ᵥ v = 0)
    (h2 : (w1 - w0) ⬝ᵥ w0 = 0) :
    ∃ X : Set V3, X = cone0P22 0 {v, w0, w1} ∧
      X ⊆ affGe {0, v} {w0, w1} ∩ W ∧
      MeasurableSet (X ∩ normballP22 0 rho) ∧
      radialNorm rho 0 (X ∩ normballP22 0 rho) ∧
      bet - asn (Real.sin bet * t) = sol 0 X := by
  sorry

/-- HOL `gotcjah_sol_lemma` (counting_spheres.hl:3985). GIANT. -/
theorem gotcjah_sol_lemma (c3 : Set V3) (v : V3) (b : ℝ) (P W : Set V3) (t rho : ℝ)
    (bet : ℝ) (w0 w1 w2 : V3) (s : ℝ)
    (hP : polyhedron P) (hbP : Bornology.IsBounded P) (hb : 0 < b)
    (hi : (0 : V3) ∈ interior P) (hf : FacetOf c3 P) (hfc : fchanged c3 = W)
    (ht : 0 < t ∧ t < 1) (hrho : 0 < rho) (hs : 0 < s)
    (hPA : P ∩ {p : V3 | p ⬝ᵥ v = b} = c3) (hsub : rconeGt 0 v t ⊆ W)
    (hv : v ≠ 0) (hvv : 0 < v ⬝ᵥ v) (hcos0 : Real.cos (arcV 0 v w0) = t)
    (hcos2 : Real.cos (arcV 0 v w2) = t)
    (hsv : s • v ∈ c3) (hw0 : w0 ∈ c3) (hw1 : w1 ∈ c3) (hw2 : w2 ∈ c3)
    (hnc0 : ¬ Collinear3 0 v w0) (hnc1 : ¬ Collinear3 0 v w1)
    (hnc2 : ¬ Collinear3 0 v w2)
    (hbet : azim 0 v w0 w2 / 2 = bet) (hlt : azim 0 v w0 w2 < Real.pi)
    (h01 : azim 0 v w0 w1 = bet) (h12 : azim 0 v w1 w2 = bet)
    (h1 : (w1 - w0) ⬝ᵥ v = 0) (h2 : (w1 - w0) ⬝ᵥ w0 = 0)
    (h3 : (w1 - w2) ⬝ᵥ v = 0) (h4 : (w1 - w2) ⬝ᵥ w2 = 0) :
    ∃ X : Set V3, X ⊆ wedge 0 v w0 w2 ∩ W ∧
      MeasurableSet (X ∩ normballP22 0 rho) ∧
      radialNorm rho 0 (X ∩ normballP22 0 rho) ∧
      2 * (bet - asn (Real.sin bet * t)) = sol 0 X := by
  sorry

/-- HOL `c3_lemma` (counting_spheres.hl:4128). -/
theorem c3_lemma (c3 : Set V3) (v : V3) (b : ℝ) (hsub : c3 ⊆ {p : V3 | p ⬝ᵥ v = b})
    (hb : 0 < b) : {p : V3 | p ⬝ᵥ v = b} ∩ fchanged c3 ⊆ c3 := by
  intro p hp
  obtain ⟨v1, t, hpt, hv1c, ht⟩ := hp.2
  have h1 : v1 ∈ c3 := intrinsicInterior_subset hv1c
  have hv1b : v1 ⬝ᵥ v = b := hsub h1
  have h2 : p ⬝ᵥ v = t * b := by
    have e1 : p ⬝ᵥ v = (t • v1) ⬝ᵥ v := by rw [← hpt]
    rw [e1, ← inner_eq_dot, inner_smul_left]
    simp only [show (starRingEnd ℝ) t = t from rfl]
    rw [inner_eq_dot v1 v, hv1b]
  have h4 : t = 1 := mul_right_cancel₀ (ne_of_gt hb) (by
    rw [← h2, hp.1, one_mul])
  rw [hpt, h4, one_smul]
  exact h1

/-- HOL `NOT_COLLINEAR` (counting_spheres.hl:4150). GIANT. -/
theorem NOT_COLLINEAR (v : V3) (hv : v ≠ 0) : ∃ u : V3, ¬ Collinear3 0 v u := by
  sorry

/-- HOL `gotcjah_prep` (counting_spheres.hl:4174). GIANT. -/
theorem gotcjah_prep (c : Set V3) (v : V3) (b : ℝ) (P : Set V3) (WF : Set V3)
    (t : ℝ) (n : ℕ) (u0 : V3) (A : Set V3)
    (hP : polyhedron P) (hbP : Bornology.IsBounded P) (hb : 0 < b)
    (hi : (0 : V3) ∈ interior P) (hf : FacetOf c P) (hA : A = {p : V3 | p ⬝ᵥ v = b})
    (hu0 : u0 = (b / (v ⬝ᵥ v)) • v) (hfc : fchanged c = WF) (ht : 0 < t ∧ t < 1)
    (hPA : P ∩ {p : V3 | p ⬝ᵥ v = b} = c) (hsub : rconeGt 0 v t ⊆ WF)
    (hsize : ({u : Set V3 | FacetOf u c}).Finite ∧ ({u : Set V3 | FacetOf u c}).ncard = n) :
    c ⊆ A ∧ v ≠ 0 ∧ 0 < v ⬝ᵥ v ∧ u0 ∈ rconeGt 0 v t ∧ u0 ∈ c ∧
      rconeGt 0 v t ∩ A ⊆ c ∧ ∃ u : V3, ¬ Collinear3 0 v u := by
  sorry

/-- HOL `convex_sum_corollary` (counting_spheres.hl:4276). GIANT. -/
theorem convex_sum_corollary (n : ℕ) (t : ℝ) (bet : ℕ → ℝ) (hn : 0 < n)
    (ht : 0 < t ∧ t < 1) (hsum : ∑ i ∈ Finset.Icc 1 n, bet i = Real.pi)
    (hb : ∀ i : ℕ, i ∈ Finset.Icc 1 n → 0 ≤ bet i ∧ bet i ≤ Real.pi) :
    Real.pi - n * asn (Real.sin (Real.pi / n) * t) ≤
      ∑ i ∈ Finset.Icc 1 n, (bet i - asn (Real.sin (bet i) * t)) := by
  sorry

/-- HOL `SOL_SUBSET` (counting_spheres.hl:4305). GIANT. -/
theorem SOL_SUBSET (x : V3) (s t : Set V3) (r : ℝ) (hr : 0 < r)
    (hms : MeasurableSet (s ∩ normballP22 x r)) (hmt : MeasurableSet (t ∩ normballP22 x r))
    (hsub : s ⊆ t) (hrs : radialNorm r x (s ∩ normballP22 x r))
    (hrt : radialNorm r x (t ∩ normballP22 x r)) : sol x s ≤ sol x t := by
  sorry

/-- HOL `GOTCJAH` (counting_spheres.hl:4366, via GOTCJAH_concl). GIANT. -/
theorem GOTCJAH (c : Set V3) (v : V3) (b : ℝ) (P : Set V3) (WF : Set V3) (t : ℝ)
    (n : ℕ) (hP : polyhedron P) (hbP : Bornology.IsBounded P) (hb : 0 < b)
    (hi : (0 : V3) ∈ interior P) (hf : FacetOf c P) (hfc : fchanged c = WF)
    (ht : 0 < t ∧ t < 1)
    (hc : c = P ∩ {p : V3 | p ⬝ᵥ v = b} ∧ rconeGt 0 v t ⊆ WF)
    (hsize : ({u : Set V3 | FacetOf u c}).Finite ∧ ({u : Set V3 | FacetOf u c}).ncard = n) :
    2 * Real.pi - 2 * n * asn (t * Real.sin (Real.pi / n)) ≤ sol 0 WF := by
  sorry

/-- HOL `rcone_def_alt` (counting_spheres.hl:4561). -/
theorem rcone_def_alt (v : V3) (t : ℝ) (p : V3) :
    p ∈ rconeGt 0 v t ↔ ‖p‖ * ‖v‖ * t < p ⬝ᵥ v := by
  simp [rconeGt, dist_zero_right]

/-- HOL `rcone_refl` (counting_spheres.hl:4570). -/
theorem rcone_refl (v : V3) (t : ℝ) (ht : t < 1) (hv : v ≠ 0) : v ∈ rconeGt 0 v t := by
  rw [rcone_def_alt]
  have hnn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [← norm_sq_eq_dot v, pow_two ‖v‖]
  nlinarith [sq_pos_of_pos (mul_pos hnn (sub_pos.mpr ht))]

/-- HOL `rcone_nz` (counting_spheres.hl:4586). -/
theorem rcone_nz (v p : V3) (t : ℝ) (ht : 0 < t) (hp : p ∈ rconeGt 0 v t) :
    p ≠ 0 ∧ v ≠ 0 := by
  rw [rcone_def_alt] at hp
  exact ⟨fun h0 => by subst h0; simp at hp, fun h0 => by subst h0; simp at hp⟩

/-- HOL `rcone_dot_pos` (counting_spheres.hl:4596). -/
theorem rcone_dot_pos (v : V3) (t : ℝ) (p : V3) (ht : 0 < t)
    (hp : p ∈ rconeGt 0 v t) : 0 < p ⬝ᵥ v := by
  have h := (rcone_def_alt v t p).mp hp
  have hnn : 0 ≤ ‖p‖ * ‖v‖ * t := by
    positivity
  linarith

/-- HOL `cos_bounds_0_Pi2` (counting_spheres.hl:4643). -/
theorem cos_bounds_0_Pi2 (x : ℝ) (h1 : 0 < x) (h2 : x < Real.pi / 2) :
    0 < Real.cos x ∧ Real.cos x < 1 := by
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩, ?_⟩
  have h := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨le_refl 0, Real.pi_pos.le⟩)
    (Set.mem_Icc.mpr ⟨h1.le, le_trans h2.le (by linarith [Real.pi_pos])⟩) h1
  simpa using h

/-- HOL `rcone_gt_arcV` (counting_spheres.hl:4618). GIANT. -/
theorem rcone_gt_arcV (v p : V3) (g : ℝ) (hg1 : 0 < g) (hg2 : g < Real.pi / 2)
    (hp : p ∈ rconeGt 0 v (Real.cos g)) : arcV 0 p v < g := by
  sorry

/-- HOL `rcone_gt_arc_triangle` (counting_spheres.hl:4685). GIANT. -/
theorem rcone_gt_arc_triangle (p v w : V3) (gv gw : ℝ) (hw : w ≠ 0)
    (h1 : 0 < gv) (h2 : gv < Real.pi / 2) (hp : p ∈ rconeGt 0 v (Real.cos gv))
    (h3 : gv + gw ≤ arcV 0 v w) : gw < arcV 0 p w := by
  sorry

/-- HOL `rcone_gt_facet` (counting_spheres.hl:4710). GIANT. -/
theorem rcone_gt_facet (gv gw : ℝ) (v w q p : V3) (h1 : 0 < gv ∧ gv < Real.pi / 2)
    (h2 : 0 < gw ∧ gw < Real.pi / 2) (hw : w ≠ 0)
    (hp : p ∈ rconeGt 0 v (Real.cos gv))
    (hq : q = ((‖v‖ * Real.cos gv) / (p ⬝ᵥ v)) • p)
    (h4 : gv + gw ≤ arcV 0 v w) : q ⬝ᵥ w < ‖w‖ * Real.cos gw := by
  sorry

/-- HOL `BIJ_SYM` (counting_spheres.hl:4784). GIANT. -/
theorem BIJ_SYM {a : Type*} {b : Type*} (A : Set a) (B : Set b)
    (h : ∃ f : a → b, Set.BijOn f A B) : ∃ g : b → a, Set.BijOn g B A := by
  sorry

/-- HOL `BIJ_TRANS` (counting_spheres.hl:4793). -/
theorem BIJ_TRANS {a b c : Type*} (A : Set a) (B : Set b) (C : Set c)
    (h1 : ∃ f : a → b, Set.BijOn f A B) (h2 : ∃ g : b → c, Set.BijOn g B C) :
    ∃ h : a → c, Set.BijOn h A C := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  exact ⟨g ∘ f, Set.BijOn.comp hg hf⟩

/-- HOL `PREIMAGE_BIJ` (counting_spheres.hl:4802). GIANT. -/
theorem PREIMAGE_BIJ {a b c : Type*} (A : Set a) (B : Set b) (C : Set c)
    (f : a → c) (g : b → c)
    (h1 : ∀ x : a, x ∈ A → f x ∈ C) (h2 : ∀ y : b, y ∈ B → g y ∈ C)
    (h3 : ∀ z : c, z ∈ C → ∃ p, Set.BijOn p {x : a | f x = z} {y : b | g y = z}) :
    ∃ q, Set.BijOn q A B := by
  sorry

/-- HOL `BIJ_FACET_HYPERFACE` (counting_spheres.hl:4821). GIANT. -/
theorem BIJ_FACET_HYPERFACE (p : Set V3) (hp : polyhedron p) (hb : Bornology.IsBounded p)
    (hi : (0 : V3) ∈ interior p) :
    ∃ b : Set V3 → Set Dart3, Set.BijOn b
      {f : Set V3 | FacetOf f p}
      ((hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).faceSet : Set (Set Dart3)) := by
  sorry

/-- HOL `POLYHEDRON_CONFORMING_FAN` (counting_spheres.hl:4842). GIANT. -/
theorem POLYHEDRON_CONFORMING_FAN (p : Set V3) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) :
    ∃ h : Fan.FAN 0 (verticesP22 p) (edgesP22 p),
      conformingFan 0 (verticesP22 p) (edgesP22 p) h := by
  sorry

/-- HOL `POLYHEDRON_D1_D` (counting_spheres.hl:4855). GIANT. -/
theorem POLYHEDRON_D1_D (p : Set V3) (hb : Bornology.IsBounded p) (hp : polyhedron p)
    (hi : (0 : V3) ∈ interior p) :
    dFanP22 0 (verticesP22 p) (edgesP22 p) = d1FanP22 0 (verticesP22 p) (edgesP22 p) := by
  sorry

/-- HOL `POLYHEDRON_PLAIN` (counting_spheres.hl:4866). GIANT. -/
theorem POLYHEDRON_PLAIN (p : Set V3) (hb : Bornology.IsBounded p) (hp : polyhedron p)
    (hi : (0 : V3) ∈ interior p) :
    (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).Plain := by
  sorry

/-- HOL `POLYHEDRON_NODE_3` (counting_spheres.hl:4905). GIANT. -/
theorem POLYHEDRON_NODE_3 (p : Set V3) (x : Dart3) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
    (hx : x ∈ dFanP22 0 (verticesP22 p) (edgesP22 p)) :
    3 ≤ ((hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).node x).ncard := by
  sorry

/-- HOL `POLYHEDRON_TGJISOK` (counting_spheres.hl:4955). GIANT. -/
theorem POLYHEDRON_TGJISOK (p : Set V3) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) :
    (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).darts.card ≤
      6 * (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).numberOfFaces - 12 := by
  sorry

/-- HOL `EDGE_PAIR_pr23` (counting_spheres.hl:5003). GIANT. -/
theorem EDGE_PAIR_pr23 (x : V3) (V : Set V3) (E : Set (Set V3)) (d d' : Dart3)
    (h : eFanP22 x V E d = d') : pr2 d = pr3 d' ∧ pr3 d = pr2 d' := by
  sorry

/-- HOL `EDGE_pr23` (counting_spheres.hl:5020). GIANT. -/
theorem EDGE_pr23 (x : V3) (V : Set V3) (E : Set (Set V3)) (y y1 : Dart3)
    (hfan : Fan.FAN x V E)
    (hcard : ∀ v ∈ V, (setOfEdgeP22 v V E).ncard > 1)
    (hy : y ∈ d1FanP22 x V E) (hy1 : y1 ∈ d1FanP22 x V E)
    (hpr : ({pr2 y, pr3 y} : Set V3) = {pr2 y1, pr3 y1}) (hne : y ≠ y1) :
    (hypermap1OfFanxP22 x V E).edgeMap y1 = y := by
  sorry

/-- HOL `SIMPLE_FACE_EDGE_INJ` (counting_spheres.hl:5066). GIANT. -/
theorem SIMPLE_FACE_EDGE_INJ {α : Type*} [DecidableEq α] (H : Hypermap α) (y y1 : α)
    (hs : H.Simple) (hnode : 1 < (H.node (H.faceMap y)).ncard)
    (hy : y ∈ H.darts) (hfy : y ∈ H.face y1) : y ≠ H.edgeMap y1 := by
  sorry

/-- HOL `INJ_EDGES_FACE_pr23` (counting_spheres.hl:5119). GIANT. -/
theorem INJ_EDGES_FACE_pr23 (p : Set V3) (f : Set Dart3) (y1 y : Dart3)
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
    (hf : f ∈ (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).faceSet)
    (hy : y ∈ f) (hy1 : y1 ∈ f)
    (hpr : ({pr2 y, pr3 y} : Set V3) = {pr2 y1, pr3 y1}) : y = y1 := by
  sorry

/-- HOL `BIJ_EDGES_DART_FACE` (counting_spheres.hl:5178). GIANT. -/
theorem BIJ_EDGES_DART_FACE (p : Set V3) (f : Set Dart3) (f1 : Set V3)
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
    (hf : f ∈ (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).faceSet)
    (hf1 : FacetOf f1 p)
    (hlead : fchanged f1 =
      dartsetLeadsIntoFanP22 0 (verticesP22 p) (edgesP22 p) f) :
    ∃ b, Set.BijOn b (edges f1) f := by
  sorry

/-- HOL `SEGMENT_EDGE_ONTO` (counting_spheres.hl:5206). GIANT. -/
theorem SEGMENT_EDGE_ONTO (p : Set V3) (e : Set V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (he : edgeOf e p) :
    ∃ v w : V3, e = segment ℝ v w := by
  sorry

/-- HOL `EDGE_OF_FACET_OF` (counting_spheres.hl:5217). GIANT. -/
theorem EDGE_OF_FACET_OF (p c e : Set V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p) (hc : FacetOf c p) :
    edgeOf e c ↔ FacetOf e c := by
  sorry

/-- HOL `EDGE_OF_FACET_EDGE` (counting_spheres.hl:5238). GIANT. -/
theorem EDGE_OF_FACET_EDGE (p c e : Set V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p) (hc : FacetOf c p)
    (he : FacetOf e c) : edgeOf e p := by
  sorry

/-- HOL `BIJ_FACET2_EDGE` (counting_spheres.hl:5253). GIANT. -/
theorem BIJ_FACET2_EDGE (p c : Set V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p) (hc : FacetOf c p) :
    ∃ b, Set.BijOn b (edges c) {u : Set V3 | FacetOf u c} := by
  sorry

/-- HOL `HYPERFACE_EXISTS` (counting_spheres.hl:5286). GIANT. -/
theorem HYPERFACE_EXISTS (P : Set V3) (U : Set V3) (hb : Bornology.IsBounded P)
    (hp : polyhedron P) (hi : (0 : V3) ∈ interior P)
    (hU : topologicalComponentYfanP22 0 (verticesP22 P) (edgesP22 P) U) :
    ∃! f : Set Dart3, f ∈ (hypermap1OfFanxP22 0 (verticesP22 P) (edgesP22 P)).faceSet ∧
      dartsetLeadsIntoFanP22 0 (verticesP22 P) (edgesP22 P) f = U := by
  sorry

/-- HOL `BIJ_DART_POLYEDGE` (counting_spheres.hl:5301). GIANT. -/
theorem BIJ_DART_POLYEDGE (P : Set V3) (hb : Bornology.IsBounded P)
    (hp : polyhedron P) (hi : (0 : V3) ∈ interior P) :
    ∃ b : Dart3 → Set V3 × Set V3, Set.BijOn b
      ((hypermap1OfFanxP22 0 (verticesP22 P) (edgesP22 P)).darts : Set Dart3)
      {fe : Set V3 × Set V3 | FacetOf fe.2 fe.1 ∧ FacetOf fe.1 P} := by
  sorry

/-- HOL `FINITE_EDGE` (counting_spheres.hl:5417). GIANT. -/
theorem FINITE_EDGE (P : Set V3) (hp : polyhedron P) (hb : Bornology.IsBounded P) :
    (∀ f : Set V3, FacetOf f P → ({e : Set V3 | FacetOf e f}).Finite) ∧
      ({f : Set V3 | FacetOf f P}).Finite ∧
      ({fe : Set V3 × Set V3 | FacetOf fe.1 P ∧ FacetOf fe.2 fe.1}).Finite := by
  sorry

open Classical in
/-- HOL `polyhedron_sum_sum_edge` (counting_spheres.hl:5443). GIANT. -/
theorem polyhedron_sum_sum_edge (P : Set V3) (hb : Bornology.IsBounded P)
    (hp : polyhedron P) (hf : ({f : Set V3 | FacetOf f P}).Finite) :
    (∑ f ∈ hf.toFinset,
        (({e : Set V3 | FacetOf e f}).ncard : ℝ)) =
      (({fe : Set V3 × Set V3 | FacetOf fe.1 P ∧ FacetOf fe.2 fe.1}).ncard : ℝ) := by
  sorry

open Classical in
/-- HOL `polyhedron_edge_sum` (counting_spheres.hl:5476). GIANT. -/
theorem polyhedron_edge_sum (P : Set V3) (n : ℝ) (hb : Bornology.IsBounded P)
    (hp : polyhedron P) (hi : (0 : V3) ∈ interior P)
    (hsize : ({f : Set V3 | FacetOf f P}).Finite ∧
      ({f : Set V3 | FacetOf f P}).ncard = n)
    (hn : 2 ≤ n) :
    (∑ f ∈ hsize.1.toFinset,
        (({e : Set V3 | FacetOf e f}).ncard : ℝ)) ≤ 6 * n - 12 := by
  sorry

/-- HOL `FACET_RELEVANT` (counting_spheres.hl:5624). GIANT. -/
theorem FACET_RELEVANT (V : Set (V3 × ℝ)) (p : V3) (v0 : V3 × ℝ)
    (hV : V.Finite) (hpos : ∀ w ∈ V, 0 < w.2)
    (hv0 : v0.1 ⬝ᵥ p = v0.2) (hv0V : v0 ∈ V)
    (hrest : ∀ w ∈ V, w ≠ v0 → w.1 ⬝ᵥ p < w.2) :
    ∃ t : ℝ, v0.2 < v0.1 ⬝ᵥ (t • p) ∧
      ∀ w ∈ V, w ≠ v0 → w.1 ⬝ᵥ (t • p) < w.2 := by
  sorry

/-- HOL `FACET_OF_POLYHEDRON_EXPLICIT_ALT` (counting_spheres.hl:5706). GIANT. -/
theorem FACET_OF_POLYHEDRON_EXPLICIT_ALT (V : Set (V3 × ℝ)) (P : Set V3)
    (hV : V.Finite) (hi : (0 : V3) ∈ interior P)
    (hVpos : ∀ v ∈ V, 0 < v.2)
    (hint : (⋂ v ∈ V, {p : V3 | v.1 ⬝ᵥ p ≤ v.2}) = P)
    (hVne : ∀ v ∈ V, v.1 ≠ 0)
    (hstrict : ∀ v ∈ V, ∃ p : V3, v.1 ⬝ᵥ p = v.2 ∧
      ∀ w ∈ V, w ≠ v → w.1 ⬝ᵥ p < w.2) :
    Set.BijOn (fun v : V3 × ℝ => P ∩ {p : V3 | v.1 ⬝ᵥ p = v.2}) V
      {c : Set V3 | FacetOf c P} := by
  sorry

/-- HOL `EXISTS_M_POLYHEDRON` (counting_spheres.hl:5888). GIANT. -/
theorem EXISTS_M_POLYHEDRON (V : Set V3) (theta : V3 → ℝ) (r : ℝ) (n : ℝ)
    (hV : V ⊆ ballAnnulus) (hP : Packing V)
    (hws : weaklySaturatedP22 V r (2 * h0))
    (hsize : V.Finite ∧ V.ncard = n) (hne : V ≠ ∅)
    (hr : 2 ≤ r ∧ r ≤ 2 * h0)
    (htheta : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → theta v + theta w ≤ arcV 0 v w)
    (hthetapos : ∀ v ∈ V, 0 < theta v ∧ theta v < Real.pi / 2) :
    ∃ b : V3 → ℝ, ∃ f : V3 → Set V3, ∃ h : V3 → Set V3, ∃ P : Set V3,
      (∀ v ∈ V, h v = {p : V3 | v ⬝ᵥ p ≤ b v}) ∧
      (⋂ v ∈ V, h v) = P ∧
      (∀ v ∈ V, 0 < b v) ∧ polyhedron P ∧ Bornology.IsBounded P ∧
      (0 : V3) ∈ interior P ∧
      Set.BijOn f V {c : Set V3 | FacetOf c P} ∧
      (∀ v ∈ V, f v = P ∩ {p : V3 | v ⬝ᵥ p = b v}) ∧
      (∀ v ∈ V, b v = ‖v‖ * Real.cos (theta v)) ∧
      (∀ v ∈ V, rconeGt 0 v (Real.cos (theta v)) ⊆ fchanged (f v)) ∧
      (∀ v ∈ V, 0 < Real.cos (theta v) ∧ Real.cos (theta v) < 1) := by
  sorry

/-- HOL `LMFUN_LE_1` (counting_spheres.hl:6155). -/
theorem LMFUN_LE_1 (h : ℝ) (hh : 1 ≤ h) : lmfun h ≤ 1 := by
  have h01 : (0 : ℝ) < h0 - 1 := by norm_num [h0]
  unfold lmfun
  split
  · next hle =>
    rw [div_le_iff₀ h01]
    linarith
  · linarith

/-- HOL `FACET_FINITE` (counting_spheres.hl:6294). GIANT. -/
theorem FACET_FINITE (p f : Set V3) (hp : polyhedron p) (hf : FacetOf f p) :
    ({e : Set V3 | FacetOf e f}).Finite := by
  sorry

/-- HOL `BIJ_SUM` (counting_spheres.hl:6308). GIANT (set-sum reindexing). -/
theorem BIJ_SUM {a i : Type*} [DecidableEq a] [DecidableEq i] {A : Set a} {B : Set i}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (f : i → ℝ) (ab : a → i) (h : Set.BijOn ab A B) (hA : A.Finite) (hB : B.Finite) :
    (∑ x ∈ hA.toFinset, f (ab x)) = (∑ y ∈ hB.toFinset, f y) := by
  sorry

/-- HOL `CARD_AT_LEAST3` (counting_spheres.hl:6318). -/
theorem CARD_AT_LEAST3 {α : Type*} [DecidableEq α] (x y z : α) (A : Set α)
    (hf : A.Finite) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hxy : x ≠ y)
    (hyz : y ≠ z) (hxz : x ≠ z) : 3 ≤ A.ncard := by
  have hsub : ({x, y, z} : Set α) ⊆ A := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have h3 : ({x, y, z} : Set α).ncard = 3 := by
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, hxy, hyz, hxz]
  have hle : ({x, y, z} : Set α).ncard ≤ A.ncard := Set.ncard_le_ncard hsub hf
  rw [h3] at hle
  exact hle

/-- HOL `polyhedron_3_facets` (counting_spheres.hl:6345). GIANT. -/
theorem polyhedron_3_facets (p : Set V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (hdim : 1 < affDim p) :
    ({c : Set V3 | FacetOf c p}).Finite ∧ 3 ≤ ({c : Set V3 | FacetOf c p}).ncard := by
  sorry

/-- HOL `facet_3_facets` (counting_spheres.hl:6466). GIANT. -/
theorem facet_3_facets (p f : Set V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    ({e : Set V3 | FacetOf e f}).Finite ∧ 3 ≤ ({e : Set V3 | FacetOf e f}).ncard := by
  sorry

/-- HOL `YSSKQOY_VECTOR` (counting_spheres.hl:6490). GIANT (Ysskqoy bank). -/
theorem YSSKQOY_VECTOR (v w : V3) (theta : V3 → ℝ)
    (hv : v ∈ ballAnnulus) (hw : w ∈ ballAnnulus) (hvw : v ≠ w)
    (hd : 2 ≤ dist v w)
    (htheta : (fun v => acs (‖v‖ / 4) - Real.pi / 6) = theta) :
    theta v + theta w ≤ arcV 0 v w := by
  sorry

/-- NEEDS HOL `arclength` (pack1.hl; PackingAuto1, no olean). Stub: 0. -/
noncomputable def arclength22 (r h : ℝ) (d : ℝ) : ℝ := 0

/-- HOL `PACK_INEQ_DEF_A_797` (counting_spheres.hl:6540). GIANT. -/
theorem PACK_INEQ_DEF_A_797 (v v0 : V3) (hpa : packIneqDefAP22)
    (hv0 : ‖v0‖ = 2) (hd : 2 * h0 ≤ dist v v0)
    (hv : 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0) :
    0.797 + acs (‖v‖ / 4) - Real.pi / 6 < arclength22 (‖v‖) 2 (dist v v0) := by
  sorry

/-- HOL `YSSKQOY_VECTOR2` (counting_spheres.hl:6599). GIANT. -/
theorem YSSKQOY_VECTOR2 (v0 w : V3) (hv0 : v0 ∈ ballAnnulus) (hw : w ∈ ballAnnulus)
    (hwv0 : w ≠ v0) (hd : 2 * h0 ≤ dist w v0) (hpa : packIneqDefAP22)
    (hv0n : ‖v0‖ = 2) :
    0.797 + acs (‖w‖ / 4) - Real.pi / 6 ≤ arcV 0 v0 w := by
  sorry

/-- HOL `YSSKQOY_VECTOR2_ALT` (counting_spheres.hl:6624). GIANT. -/
theorem YSSKQOY_VECTOR2_ALT (V : Set V3) (v w v0 : V3) (theta : V3 → ℝ)
    (hV : V ⊆ ballAnnulus) (hP : Packing V)
    (hv : v ∈ V) (hw : w ∈ V) (hv0 : v0 ∈ V) (hvw : v ≠ w)
    (hfar : ∀ w ∈ V, w ≠ v0 → 2 * h0 ≤ dist w v0)
    (hpa : packIneqDefAP22) (hv0n : ‖v0‖ = 2)
    (htheta : (fun v => if v = v0 then (0.797 : ℝ) else acs (‖v‖ / 4) - Real.pi / 6) = theta) :
    theta v + theta w ≤ arcV 0 v w := by
  sorry

/-- HOL `ACS_ROOT32` (counting_spheres.hl:6657). -/
theorem ACS_ROOT32 : acs (Real.sqrt 3 / 2) = Real.pi / 6 := by
  have h1 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  have hpi : (0:Real) < Real.pi := Real.pi_pos
  rw [acs, ← h1]
  rw [Real.arccos_cos (by linarith) (by linarith)]

/-- HOL `ASN_HALF` (counting_spheres.hl:6668). -/
theorem ASN_HALF : asn (1 / 2) = Real.pi / 6 := by
  rw [asn]
  rw [show (1:Real) / 2 = Real.sin (Real.pi / 6) from Real.sin_pi_div_six.symm]
  rw [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]

/-- HOL `THETA_BOUNDS` (counting_spheres.hl:6679). NEEDS `h0 < sqrt 3`
(Flyspeck_constants.bounds; cf. PackingAuto15.H0_LT_SQRT2, not importable). -/
theorem THETA_BOUNDS (v : V3) (theta : V3 → ℝ) (hv : v ∈ ballAnnulus)
    (htheta : (fun v => acs (‖v‖ / 4) - Real.pi / 6) = theta) :
    0 < theta v ∧ theta v < Real.pi / 2 := by
  sorry

/-- HOL `INJ_FINITE_EXISTS` (counting_spheres.hl:6704). GIANT. -/
theorem INJ_FINITE_EXISTS {a b : Type*} [DecidableEq a] [DecidableEq b] (n : ℝ)
    (A : Set a) (B : Set b) (hA : A.Finite ∧ A.ncard = n) (hB : B.Finite)
    (hn : n ≤ B.ncard) : ∃ j : a → b, (∀ x ∈ A, j x ∈ B) ∧ Set.InjOn j A := by
  sorry

/-- HOL `INJ_EXTENSION` (counting_spheres.hl:6759). GIANT. -/
theorem INJ_EXTENSION {α β : Type*} [DecidableEq α] [DecidableEq β] (A A' : Set α)
    (B : Set β) (j' : α → β) (hA : A.Finite) (hB : B.Finite) (hsub : A' ⊆ A)
    (hinj : Set.InjOn j' A' ∧ ∀ x ∈ A', j' x ∈ B) (hcard : A.ncard ≤ B.ncard) :
    ∃ j : α → β, Set.InjOn j A ∧ (∀ x ∈ A', j x = j' x) ∧ (∀ x ∈ A, j x ∈ B) := by
  sorry

/-- HOL `BIJ_EXTENDS_INJ` (counting_spheres.hl:6794). GIANT. -/
theorem BIJ_EXTENDS_INJ {α β : Type*} [DecidableEq α] [DecidableEq β] (A : Set α)
    (B : Set β) (A' : Set α) (j' : α → β) (hA : A.Finite) (hB : B.Finite)
    (hsub : A' ⊆ A) (hinj : Set.InjOn j' A' ∧ ∀ x ∈ A', j' x ∈ B)
    (hcard : A.ncard = B.ncard) :
    ∃ j : α → β, Set.BijOn j A B ∧ (∀ x ∈ A', j' x = j x) := by
  sorry

open Classical in
/-- HOL `DLWCHEM_VECTOR_sum` (counting_spheres.hl:6814). GIANT. -/
theorem DLWCHEM_VECTOR_sum (k : V3 → ℕ) (theta : V3 → ℝ)
    (hpa : packIneqDefAP22)
    (htheta : (fun v => acs (‖v‖ / 4) - Real.pi / 6) = theta)
    (hk : ∀ v ∈ V, 3 ≤ k v) (hn : 12 < n)
    (hsize : V.Finite ∧ V.ncard = n) (hV : V ⊆ ballAnnulus)
    (hksum : ∑ v ∈ hsize.1.toFinset, (k v : ℝ) ≤ 6 * n - 12)
    (hasum : ∑ v ∈ hsize.1.toFinset,
        max 0 (regularSphericalPolygonAreaP22 (Real.cos (theta v)) (k v)) ≤ 4 * Real.pi)
    (hloc : ¬ localAnnulusInequalityP22 V) : n < 16 := by
  sorry

open Classical in
/-- HOL `XULJEPR_VECTOR_sum` (counting_spheres.hl:6905). GIANT. -/
theorem XULJEPR_VECTOR_sum (k : V3 → ℕ) (V : Set V3) (n : ℝ) (theta : V3 → ℝ)
    (v0 : V3) (hpa : packIneqDefAP22) (hv0 : v0 ∈ V)
    (htheta : (fun v => if v = v0 then (0.797 : ℝ) else acs (‖v‖ / 4) - Real.pi / 6) = theta)
    (hn : 12 < n) (hv0n : ‖v0‖ = 2) (hk : ∀ v ∈ V, 3 ≤ k v)
    (hsize : V.Finite ∧ V.ncard = n) (hV : V ⊆ ballAnnulus)
    (hksum : ∑ v ∈ hsize.1.toFinset, (k v : ℝ) ≤ 6 * n - 12)
    (hasum : ∑ v ∈ hsize.1.toFinset,
        max 0 (regularSphericalPolygonAreaP22 (Real.cos (theta v)) (k v)) ≤ 4 * Real.pi)
    (hloc : ¬ localAnnulusInequalityP22 V) : False := by
  sorry

/-- HOL `SOL_NN` (counting_spheres.hl:7026). GIANT. -/
theorem SOL_NN (x : V3) (U : Set V3)
    (h : ∃ r : ℝ, 0 < r ∧ MeasurableSet (U ∩ normballP22 x r) ∧
      radialNorm r x (U ∩ normballP22 x r)) : 0 ≤ sol x U := by
  sorry

/-- HOL `FACET_SOL_NN` (counting_spheres.hl:7049). GIANT. -/
theorem FACET_SOL_NN (p c : Set V3) (hp : polyhedron p) (hb : Bornology.IsBounded p)
    (hi : (0 : V3) ∈ interior p) (hc : FacetOf c p) : 0 ≤ sol 0 (fchanged c) := by
  sorry

/-- HOL `DLWCHEM` (counting_spheres.hl:7063): the saturated annulus packing has
13, 14 or 15 points. GIANT (the counting endgame). -/
theorem DLWCHEM (V : Set V3) (hP : Packing V) (hpa : packIneqDefAP22)
    (hV : V ⊆ ballAnnulus) (hloc : ¬ localAnnulusInequalityP22 V) :
    V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15 := by
  sorry

/-- HOL `XULJEPR` (counting_spheres.hl:7191): a unit-diameter center forces the
local annulus inequality. GIANT. -/
theorem XULJEPR (V : Set V3) (hP : Packing V) (hV : V ⊆ ballAnnulus)
    (hpa : packIneqDefAP22)
    (hv : ∃ v ∈ V, ‖v‖ = 2 ∧ ∀ u ∈ V, u ≠ v → 2 * h0 ≤ dist u v) :
    localAnnulusInequalityP22 V := by
  sorry

end Kepler.Text
