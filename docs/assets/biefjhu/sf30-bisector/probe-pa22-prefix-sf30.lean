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
    re/im coordinates); planar `polyhedron/facet_of` are faithful copies of
    polytope1.ml facet_of/polyhedron (H-representation, aff_dim form).
  - HOL `Arg` (Ysskqoy kit, range `[0, 2π)`) <-> `holArg` (the `[0, 2π)` lift
    of `Complex.arg`, defined in the encoding layer below).  SF22/SF27
    statement-fix batch (minesweep report §3): `ARG_ORDER`, `insert_v`,
    `poly_sort_fn`, `POLYSORT_BIJ2`, `EUSOTYP_simple` are stated over
    `holArg`, the faithful HOL `Arg` (same defect class as the ARG_INV_ALT
    port note at its block).
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
  - `cone0 x U` is DEFINED here as `affGt {x} U` (flyspeck cone0 = aff_gt of
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
import Kepler.Text.PackingAuto15
import Kepler.Text.Polytope
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

open Kepler.Geom Set Classical

/-! ## Encoding layer (planar section, notation wrappers) -/

/-- Planar dot product on `ℂ` standing in for HOL `dot` on `real^2`. -/
def dot2 (x y : ℂ) : ℝ := (x * star y).re

/-- HOL `Arg` for nonzero arguments (Ysskqoy `ARG` kit, range `[0, 2π)`),
rebuilt from `Complex.arg` (range `(-π, π]`) by lifting negative arguments to
`arg + 2π`.  The original port of `ARG_INV_ALT` used `Complex.arg` directly,
which makes the identity false (HOL `Arg(x/y) = 2*pi - Arg(y/x)` relies on
`Arg` taking values in `[0, 2π)`).  SF22/SF27 statement-fix batch (minesweep
report §3): the same defect class hit `ARG_ORDER`, `insert_v`, `poly_sort_fn`,
`POLYSORT_BIJ2` and `EUSOTYP_simple`; all five are restated over `holArg`.
Defined here in the encoding layer (moved up verbatim from the ARG_INV_ALT
block mid-file) so the earlier poly-sort kit can use it. -/
noncomputable def holArg (z : ℂ) : ℝ :=
  if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi

/-- SF22/SF27 linkage kit: `holArg` is an injective lift of `Complex.arg`
(the two branches map `(-π, 0)` and `[0, π]` to the disjoint intervals
`(π, 2π)` and `[0, π]`), so equal `holArg`s have equal principal arguments.
Used to re-port `poly_sort_antisym` off `Complex.arg`. -/
private theorem p22_holArg_eq_iff (z1 z2 : ℂ) :
    holArg z1 = holArg z2 ↔ Complex.arg z1 = Complex.arg z2 := by
  have hun : ∀ z : ℂ, holArg z =
      if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi :=
    fun z => rfl
  rw [hun z1, hun z2]
  by_cases h1 : 0 ≤ Complex.arg z1 <;> by_cases h2 : 0 ≤ Complex.arg z2
  · rw [if_pos h1, if_pos h2]
  · rw [if_pos h1, if_neg h2]
    constructor
    · intro heq
      have hb1 := Complex.arg_le_pi z1
      have hb2 := Complex.neg_pi_lt_arg z2
      linarith
    · intro harg
      rw [harg] at h1
      have h2n : Complex.arg z2 < 0 := not_le.mp h2
      linarith
  · rw [if_neg h1, if_pos h2]
    constructor
    · intro heq
      have hb1 := Complex.neg_pi_lt_arg z1
      have hb2 := Complex.arg_le_pi z2
      linarith
    · intro harg
      rw [← harg] at h2
      have h1n : Complex.arg z1 < 0 := not_le.mp h1
      linarith
  · rw [if_neg h1, if_neg h2]
    constructor
    · intro heq; linarith
    · intro harg; linarith

/-- HOL `asn` (arcsin). -/
noncomputable def asn (x : ℝ) : ℝ := Real.arcsin x

/-- HOL `acs` (arccos). -/
noncomputable def acs (x : ℝ) : ℝ := Real.arccos x

/-- HOL `sqrt3`. -/
noncomputable def sqrt3 : ℝ := Real.sqrt 3

/-- Planar copy of HOL `aff_dim` (convex1.ml:3784; twin of Polytope.affDim):
`∅ ↦ -1`, else the finrank of the direction of the affine hull. -/
noncomputable def affDimC (s : Set ℂ) : ℤ :=
  if s = ∅ then -1 else (Module.finrank ℝ (vectorSpan ℝ s) : ℤ)

/-- Planar copy of Polytope.`FaceOf` (polytope1.ml:22 face kit). -/
def faceOfC (t s : Set ℂ) : Prop :=
  t ⊆ s ∧ Convex ℝ t ∧
    ∀ a b x : ℂ, a ∈ s → b ∈ s → x ∈ t → x ∈ openSegment ℝ a b → a ∈ t ∧ b ∈ t

/-- Planar copy of HOL `facet_of` (polytope1.ml:1506): `f facet_of s <=>
f face_of s /\ ~(f = {}) /\ aff_dim f = aff_dim s - &1`. -/
def facetOfC (f s : Set ℂ) : Prop :=
  faceOfC f s ∧ f ≠ ∅ ∧ affDimC f = affDimC s - 1

/-- Planar copy of HOL `polyhedron` (polytope1.ml:2546): finite intersection
of halfspaces `{x | a dot x ≤ b}` with `a ≠ 0` (H-representation). -/
def polyhedronC (P : Set ℂ) : Prop :=
  ∃ F : Set (Set ℂ), F.Finite ∧ P = ⋂₀ F ∧
    ∀ h ∈ F, ∃ a : ℂ, ∃ b : ℝ, a ≠ 0 ∧ h = {x : ℂ | dot2 a x ≤ b}

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

/-- HOL `cone0 x U` (sphere.hl:290 `cone0 v S = affsign sgn_gt {v} S`), i.e.
the open cone `aff_gt {x} U` (`Kepler.Geom.affGt`, counting_spheres.hl:3770
CONE0_AFF_GT). -/
def cone0P22 (x : V3) (U : Set V3) : Set V3 := affGt {x} U

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

/-- HOL `facet_rep_uniq` (counting_spheres.hl:161). GIANT. -/
theorem facet_rep_uniq (P c1 c2 : Set ℂ) (a : ℂ) (b1 b2 : ℝ)
    (hP : polyhedronC P) (h1 : facetOfC c1 P) (h2 : facetOfC c2 P)
    (s1 : P ⊆ {x : ℂ | dot2 a x ≤ b1}) (s2 : P ⊆ {x : ℂ | dot2 a x ≤ b2})
    (e1 : c1 = P ∩ {x : ℂ | dot2 a x = b1}) (e2 : c2 = P ∩ {x : ℂ | dot2 a x = b2}) :
    b1 = b2 ∧ c1 = c2 := by
  -- The new `facetOfC` carries `f ≠ ∅` as its second conjunct (§3a ★note): a
  -- nonempty point of each facet pins the supporting value from both sides
  -- (b1 ≤ b2 ≤ b1 by the supporting inequalities at x and y).
  have h1ne : c1.Nonempty := Set.nonempty_iff_ne_empty.mpr h1.2.1
  have h2ne : c2.Nonempty := Set.nonempty_iff_ne_empty.mpr h2.2.1
  obtain ⟨x, hx1⟩ := h1ne
  obtain ⟨y, hy1⟩ := h2ne
  have hxP : x ∈ P := ((e1 ▸ hx1).1 : x ∈ P)
  have hyP : y ∈ P := ((e2 ▸ hy1).1 : y ∈ P)
  have hxb1 : dot2 a x = b1 := (e1 ▸ hx1).2
  have hyb2 : dot2 a y = b2 := (e2 ▸ hy1).2
  have hb12 : b1 ≤ b2 := by rw [← hxb1]; exact s2 hxP
  have hb21 : b2 ≤ b1 := by rw [← hyb2]; exact s1 hyP
  refine ⟨le_antisymm hb12 hb21, ?_⟩
  rw [e1, e2, le_antisymm hb12 hb21]

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

/-- Homogeneity of `dot2` in the second argument (private frozen copy kept for
the `facet_rep_*` kit; identical to the public `dot2_smul_right`). -/
private theorem p22_dot2_smul_right (a x : ℂ) (c : ℝ) : dot2 a (c • x) = c * dot2 a x := by
  rw [dot2_expand, dot2_expand]
  have h1 : (c • x : ℂ).re = c * x.re := by simp
  have h2 : (c • x : ℂ).im = c * x.im := by simp
  rw [h1, h2]
  ring

/-- Self inner product equals squared norm (used by `facet_rep_in_facet`). -/
private theorem p22_dot2_self (w : ℂ) : dot2 w w = ‖w‖ ^ 2 := by
  rw [dot2_expand, Complex.sq_norm, Complex.normSq_apply]

/-- Cauchy–Schwarz for the planar dot product (counting_spheres.hl:227 proof
core: `NORM_CAUCHY_SCHWARZ`). -/
private theorem p22_dot2_cauchy (x y : ℂ) : dot2 x y ≤ ‖x‖ * ‖y‖ := by
  have hxs : ‖x‖ ^ 2 = x.re * x.re + x.im * x.im := by
    rw [Complex.sq_norm]; exact Complex.normSq_apply x
  have hys : ‖y‖ ^ 2 = y.re * y.re + y.im * y.im := by
    rw [Complex.sq_norm]; exact Complex.normSq_apply y
  have hnn : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rcases lt_or_ge (dot2 x y) 0 with h0 | h0
  · linarith
  · have hs : (dot2 x y) ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
      rw [dot2_expand, mul_pow, hxs, hys]
      nlinarith [sq_nonneg (x.re * y.im - x.im * y.re)]
    have hle : |dot2 x y| ≤ |‖x‖ * ‖y‖| := (sq_le_sq).mp hs
    calc dot2 x y ≤ |dot2 x y| := le_abs_self _
      _ ≤ |‖x‖ * ‖y‖| := hle
      _ = ‖x‖ * ‖y‖ := abs_of_nonneg hnn

/-- Additivity of `dot2` in the second argument. -/
theorem dot2_add_right (a x y : ℂ) : dot2 a (x + y) = dot2 a x + dot2 a y := by
  rw [dot2_expand, dot2_expand, dot2_expand]
  simp [Complex.add_re, Complex.add_im]
  ring

/-- Homogeneity of `dot2` in the second argument. -/
theorem dot2_smul_right (a x : ℂ) (c : ℝ) : dot2 a (c • x) = c * dot2 a x := by
  rw [dot2_expand, dot2_expand]
  have h1 : (c • x : ℂ).re = c * x.re := by simp
  have h2 : (c • x : ℂ).im = c * x.im := by simp
  rw [h1, h2]
  ring

/-- A nonzero complex vector has positive self inner product. -/
theorem dot2_self_pos (a : ℂ) (ha : a ≠ 0) : 0 < dot2 a a := by
  rw [dot2_expand]
  have h1 : a.re ≠ 0 ∨ a.im ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact ha (Complex.ext hcon.1 hcon.2)
  rcases h1 with h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg a.im]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg a.re]

/-- HOL `DOT_EQ_IMP_INEQ_LEMMA` (counting_spheres.hl:274). Filled: the shared
hyperplane hypothesis forces `dot2 a' x = (b'/b) * dot2 a x`, so half-space
membership transfers. -/
theorem DOT_EQ_IMP_INEQ_LEMMA (a a' : ℂ) (b b' : ℝ)
    (hiff : ∀ x : ℂ, dot2 a x = b ↔ dot2 a' x = b') (hb : 0 < b) (hb' : 0 < b') :
    ∀ x : ℂ, dot2 a x ≠ 0 → (dot2 a x ≤ b ↔ dot2 a' x ≤ b') := by
  intro x hx
  have key : dot2 a' x = b' * (dot2 a x) / b := by
    have hy : dot2 a ((b / dot2 a x) • x) = b := by
      rw [dot2_smul_right]
      field_simp
    have h2 := (hiff _).mp hy
    rw [dot2_smul_right a' x (b / dot2 a x)] at h2
    have h6 := congrArg (fun t => t * dot2 a x) h2
    rw [mul_right_comm, div_mul_cancel₀ _ hx] at h6
    rw [eq_div_iff (ne_of_gt hb), mul_comm]
    exact h6
  constructor
  · intro hle
    rw [key, div_le_iff₀ hb]
    exact mul_le_mul_of_nonneg_left hle hb'.le
  · intro hle
    rw [key, div_le_iff₀ hb] at hle
    exact le_of_mul_le_mul_left hle hb'

/-- HOL `DOT_EQ_IMP_INEQ` (counting_spheres.hl:302). Filled via the transfer
identity `dot2 a' x = (b'/b) * dot2 a x` (a hyperplane point exists once
`a' ≠ 0`, which also forces `b > 0`; the `a' = 0` case collapses to `a = 0`). -/
theorem DOT_EQ_IMP_INEQ (a a' : ℂ) (b b' : ℝ)
    (hiff : ∀ x : ℂ, dot2 a x = b ↔ dot2 a' x = b') (hb : 0 ≤ b) (hb' : 0 < b') :
    ∀ x : ℂ, dot2 a x ≤ b ↔ dot2 a' x ≤ b' := by
  by_cases ha'0 : a' = 0
  · subst ha'0
    have ha0 : a = 0 := by
      by_contra hne
      have haa : 0 < dot2 a a := dot2_self_pos a hne
      have haa0 : dot2 a a ≠ 0 := ne_of_gt haa
      have hx0 : dot2 a ((b / dot2 a a) • a) = b := by
        rw [dot2_smul_right]; field_simp
      have h2 := (hiff _).mp hx0
      rw [dot2_smul_right (0:ℂ) a (b / dot2 a a)] at h2
      simp [dot2_expand] at h2
      linarith
    subst ha0
    intro x
    constructor <;> intro _ <;>
      simp only [dot2_expand, Complex.zero_re, Complex.zero_im, zero_mul, add_zero] <;>
      linarith
  · have haa'0 : dot2 a' a' ≠ 0 := ne_of_gt (dot2_self_pos a' ha'0)
    have hx₀a' : dot2 a' ((b' / dot2 a' a') • a') = b' := by
      rw [dot2_smul_right]; field_simp
    have hx₀a : dot2 a ((b' / dot2 a' a') • a') = b := (hiff _).mpr hx₀a'
    have hbpos : 0 < b := by
      rcases eq_or_lt_of_le hb with heq | hlt
      · exfalso
        have h1 : dot2 a 0 = 0 := by simp [dot2_expand]
        rw [heq] at h1
        have h2 := (hiff (0:ℂ)).mp h1
        simp [dot2_expand] at h2
        linarith
      · exact hlt
    have key : ∀ y : ℂ, dot2 a' y = (b' / b) * dot2 a y := by
      intro y
      have hLam : dot2 a (y + ((b - dot2 a y) / b) • ((b' / dot2 a' a') • a')) = b := by
        rw [dot2_add_right, dot2_smul_right, hx₀a,
          div_mul_cancel₀ (b - dot2 a y) (ne_of_gt hbpos)]
        ring
      have h2 := (hiff _).mp hLam
      rw [dot2_add_right, dot2_smul_right, hx₀a'] at h2
      field_simp at h2 ⊢
      linear_combination h2
    intro y
    have hy' : dot2 a' y * b = b' * dot2 a y := by
      rw [key y, mul_right_comm, div_mul_cancel₀ (b') (ne_of_gt hbpos)]
    constructor
    · intro h
      rw [key y]
      calc (b' / b) * dot2 a y ≤ (b' / b) * b :=
            mul_le_mul_of_nonneg_left h (div_nonneg hb'.le hbpos.le)
        _ = b' := div_mul_cancel₀ (b') (ne_of_gt hbpos)
    · intro h
      have h2 := mul_le_mul_of_nonneg_right h hbpos.le
      rw [hy'] at h2
      exact le_of_mul_le_mul_left h2 hb'


theorem affDimC_empty : affDimC (∅ : Set ℂ) = -1 :=
  if_pos rfl

theorem affDimC_singleton (x : ℂ) : affDimC {x} = 0 := by
  rw [affDimC, if_neg (by simp)]
  simp [vectorSpan_singleton]

theorem affDimC_mono {s t : Set ℂ} (hsub : s ⊆ t) (hs : s.Nonempty) :
    affDimC s ≤ affDimC t := by
  have hs' : s ≠ ∅ := nonempty_iff_ne_empty.1 hs
  have ht' : t ≠ ∅ := nonempty_iff_ne_empty.1 (hs.mono hsub)
  simp only [affDimC, if_neg hs', if_neg ht']
  exact Nat.cast_le.2 (Submodule.finrank_mono (vectorSpan_mono ℝ hsub))

/-- The linear functional `x ↦ dot2 a x`. -/
def dotRightC (a : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun x := dot2 a x
  map_add' x y := dot2_add_right a x y
  map_smul' r x := by
    show dot2 a (r • x) = (RingHom.id ℝ) r • dot2 a x
    rw [dot2_smul_right]
    simp



theorem dotRightC_apply (a x : ℂ) : dotRightC a x = dot2 a x := rfl

theorem dotRightC_surjective {a : ℂ} (ha : a ≠ 0) : Function.Surjective (dotRightC a) := by
  intro r
  refine ⟨(r / dot2 a a) • a, ?_⟩
  have hnz : dot2 a a ≠ 0 := ne_of_gt (dot2_self_pos a ha)
  rw [dotRightC_apply, dot2_smul_right, div_mul_eq_mul_div]
  field_simp

theorem affDimC_hyperplane {a : ℂ} (ha : a ≠ 0) (b : ℝ) :
    affDimC {x : ℂ | dot2 a x = b} = 1 := by
  set H := {x : ℂ | dot2 a x = b} with hH
  have hker : ∀ x : ℂ, x ∈ LinearMap.ker (dotRightC a) ↔ dot2 a x = 0 :=
    fun x => LinearMap.mem_ker
  have hsurj : Function.Surjective (dotRightC a) := dotRightC_surjective ha
  obtain ⟨p0, hp0'⟩ := hsurj b
  have hp0 : dot2 a p0 = b := hp0'
  have key : vectorSpan ℝ H = LinearMap.ker (dotRightC a) := by
    refine le_antisymm ?_ ?_
    · rw [vectorSpan_def, Submodule.span_le]
      rintro z ⟨p, hp, q, hq, rfl⟩
      simp only [hH, Set.mem_setOf_eq] at hp hq
      have hp' : dot2 a p = b := hp
      have hq' : dot2 a q = b := hq
      have hdiff : dot2 a (p - q) = dot2 a p - dot2 a q := dot2_sub_r a p q
      show dot2 a (p - q) = 0
      rw [hdiff, hp', hq', sub_self]
    · intro z hz
      have hzk : dotRightC a z = 0 := LinearMap.mem_ker.1 hz
      have hpmz : p0 - z ∈ H := by
        simp only [hH, Set.mem_setOf_eq]
        have hsplit : dot2 a (p0 - z) = dot2 a p0 - dot2 a z := dot2_sub_r a p0 z
        rw [hsplit, hp0, show dot2 a z = 0 from hzk, sub_zero]
      show z ∈ vectorSpan ℝ H
      rw [vectorSpan_def]
      exact Submodule.subset_span (Set.mem_vsub.2 ⟨p0, by rw [hH]; exact hp0, p0 - z, hpmz,
        by rw [vsub_eq_sub, sub_sub_self]⟩)
  have h1 : Module.finrank ℝ (LinearMap.ker (dotRightC a)) = 1 := by
    have hnk := LinearMap.finrank_range_add_finrank_ker (dotRightC a)
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hnk
    have h2 : Module.finrank ℝ ℝ = 1 := by
      first
        | exact Module.finrank_self ℝ
        | exact finrank_self
        | norm_num
    rw [h2, Complex.finrank_real_complex] at hnk
    omega
  have hHne : H.Nonempty := ⟨p0, by rw [hH]; exact hp0⟩
  rw [affDimC, if_neg (nonempty_iff_ne_empty.1 hHne), key, h1]
  norm_num

/-- Full-dimensionality from `affineSpan = univ`. -/
theorem affDimC_eq_two_of_affineSpan_eq_univ {P : Set ℂ}
    (haff : (affineSpan ℝ P : Set ℂ) = univ) (hne : P ≠ ∅) : affDimC P = 2 := by
  rw [affDimC, if_neg hne]
  have haff' : (affineSpan ℝ P) = (⊤ : AffineSubspace ℝ ℂ) := by
    refine le_antisymm le_top ?_
    rw [AffineSubspace.le_def']
    intro x _
    show x ∈ (affineSpan ℝ P : Set ℂ)
    rw [haff]
    trivial
  have hvtop : vectorSpan ℝ P = ⊤ := by
    rw [← direction_affineSpan ℝ P, haff', AffineSubspace.direction_top]
  rw [hvtop, finrank_top, Complex.finrank_real_complex]
  norm_num

/-! ## AFF_DIM_EQ_AFFINE_HULL ℂ kit -/

/-- `HOL AFF_DIM_EQ_AFFINE_HULL` ℂ 版：等维数 + 含于仿射子空间 → 仿射包相等。 -/
theorem affineSpanC_eq_of_affDimC_eq {s H : Set ℂ} (hs : s.Nonempty) (hsub : s ⊆ H)
    (Hsp : AffineSubspace ℝ ℂ) (hH : (↑Hsp : Set ℂ) = H) (hdim : affDimC s = affDimC H) :
    (affineSpan ℝ s : Set ℂ) = H := by
  have hHne : (↑Hsp : Set ℂ).Nonempty := hs.mono (by rw [hH]; exact hsub)
  have hHne2 : H ≠ ∅ := by
    rw [← hH]
    exact Set.nonempty_iff_ne_empty.1 hHne
  have hKle : (affineSpan ℝ s) ≤ Hsp := affineSpan_le.2 (by rw [hH]; exact hsub)
  -- vectorSpan of the carrier equals the direction
  have hspan : (affineSpan ℝ (↑Hsp : Set ℂ)) = Hsp := by
    refine le_antisymm (affineSpan_le.2 Set.Subset.rfl) ?_
    rw [AffineSubspace.le_def']
    intro x hx
    exact subset_affineSpan ℝ _ hx
  have hvdir : vectorSpan ℝ (↑Hsp : Set ℂ) = Hsp.direction := by
    rw [← direction_affineSpan ℝ (↑Hsp : Set ℂ), hspan]
  have hfinZ : (Module.finrank ℝ ↥(affineSpan ℝ s).direction : ℤ)
      = (Module.finrank ℝ ↥Hsp.direction : ℤ) := by
    rw [direction_affineSpan ℝ s]
    have h1 : affDimC s = (Module.finrank ℝ (vectorSpan ℝ s) : ℤ) := by
      rw [affDimC, if_neg (nonempty_iff_ne_empty.1 hs)]
    have h2 : affDimC H = (Module.finrank ℝ (vectorSpan ℝ H) : ℤ) := by
      rw [affDimC, if_neg hHne2]
    have h2' : affDimC H = (Module.finrank ℝ ↥Hsp.direction : ℤ) := by
      rw [h2, ← hvdir, hH]
    rw [← h1]
    calc affDimC s = affDimC H := hdim
      _ = (Module.finrank ℝ ↥Hsp.direction : ℤ) := h2'
  have hfin := Nat.cast_injective hfinZ
  have hdir : (affineSpan ℝ s).direction = Hsp.direction :=
    Submodule.eq_of_le_of_finrank_eq
      (le_trans (AffineSubspace.direction_le hKle) (le_of_eq hvdir.symm)) hfin
  have hspanne : (affineSpan ℝ s : Set ℂ).Nonempty := ⟨_, subset_affineSpan ℝ s hs.some_mem⟩
  have hHcoe : ∀ x : ℂ, x ∈ (↑Hsp : Set ℂ) ↔ x ∈ H := fun x => by rw [hH]
  refine Set.ext fun x => ?_
  constructor
  · exact fun hx => (hHcoe x).1 (SetLike.mem_coe.2 (hKle hx))
  · intro hx
    obtain ⟨y, hy⟩ := hspanne
    have hxx : x = (x -ᵥ y) +ᵥ y := (vsub_vadd x y).symm
    have hvy : x -ᵥ y ∈ Hsp.direction :=
      AffineSubspace.vsub_mem_direction ((hHcoe x).2 hx) (SetLike.mem_coe.2 (hKle hy))
    have hmem : (x -ᵥ y) +ᵥ y ∈ (affineSpan ℝ s : Set ℂ) :=
      AffineSubspace.vadd_mem_of_mem_direction (by rw [hdir]; exact hvy) hy
    rwa [← hxx] at hmem


/-- The hyperplane `{x | dot2 a x = b}` as the carrier of an affine subspace. -/
theorem coe_dotHyperplaneC {a : ℂ} {b : ℝ} {p0 : ℂ} (hp0 : dot2 a p0 = b) :
    (↑(AffineSubspace.mk' p0 (LinearMap.ker (dotRightC a))) : Set ℂ)
      = {x : ℂ | dot2 a x = b} := by
  refine Set.ext fun x => ?_
  show (x -ᵥ p0) ∈ (LinearMap.ker (dotRightC a)) ↔ x ∈ {x : ℂ | dot2 a x = b}
  rw [vsub_eq_sub, LinearMap.mem_ker, map_sub, dotRightC_apply, dotRightC_apply, hp0,
    sub_eq_zero]
  exact Iff.rfl

/-- HOL `CONTAINS_BALL_AFFINE_HULL` (Packing3) ℂ 版：含开球 → 仿射包为全空间. -/
theorem CONTAINS_BALL_AFFINE_HULL_C {s : Set ℂ} {x : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball x r ⊆ s) : (affineSpan ℝ s : Set ℂ) = univ := by
  have h1 : affineSpan ℝ (Metric.ball x r) = ⊤ :=
    Metric.isOpen_ball.affineSpan_eq_top ⟨x, Metric.mem_ball_self hr⟩
  have h2 : (affineSpan ℝ s) = (⊤ : AffineSubspace ℝ ℂ) := by
    rw [eq_top_iff, ← h1]
    exact affineSpan_mono ℝ hsub
  rw [h2]
  rfl

/-- HOL `affine_facet_hyper` (counting_spheres.hl:320). Filled (kit wave): the
facet equals `P ∩ H` for the hyperplane `H`, hence `affDimC c = affDimC P - 1`
with `affDimC P = 2` (full-dim) and `affDimC H = 1` (`affDimC_hyperplane`), so
`affineSpanC_eq_of_affDimC_eq` identifies the affine span with `H`. -/
theorem affine_facet_hyper (P c : Set ℂ) (a : ℂ) (b : ℝ)
    (hc : facetOfC c P) (hP : polyhedronC P) (haff : (affineSpan ℝ P : Set ℂ) = univ)
    (ha : a ≠ 0) (h : P ∩ {x : ℂ | dot2 a x = b} = c) :
    (affineSpan ℝ c : Set ℂ) = {x : ℂ | dot2 a x = b} := by
  have hcsubP : c ⊆ P := by rw [← h]; exact Set.inter_subset_left
  have hcsub : c ⊆ {x : ℂ | dot2 a x = b} := by rw [← h]; exact Set.inter_subset_right
  have hcne : c.Nonempty := nonempty_iff_ne_empty.2 hc.2.1
  have hPne : P ≠ ∅ := by
    obtain ⟨xc, hxc⟩ := hcne
    intro hcc
    rw [hcc] at hcsubP
    exact hcsubP hxc
  have hPdim : affDimC P = 2 := affDimC_eq_two_of_affineSpan_eq_univ haff hPne
  have hcdim : affDimC c = affDimC {x : ℂ | dot2 a x = b} := by
    rw [hc.2.2, hPdim, affDimC_hyperplane ha b]
    norm_num
  obtain ⟨p0, hp0⟩ : ∃ p0 : ℂ, dot2 a p0 = b := ⟨(b / dot2 a a) • a, by
    have hdd : dot2 a a ≠ 0 := ne_of_gt (dot2_self_pos a ha)
    rw [dot2_smul_right]
    field_simp⟩
  exact affineSpanC_eq_of_affDimC_eq hcne hcsub _
    (coe_dotHyperplaneC hp0) hcdim

/-! ## FACET_OF_POLYHEDRONC_EXPLICIT kit — ℂ port of the Polytope.lean
minrep/slice mechanism (template :252-1790; planar-encoding-fix.md §2.3).
The V3 dot `⬝ᵥ` becomes `dot2`, `dotRight` becomes `dotRightC`; the minrep
statement keeps the `affineSpan` conjunct of the V3 template verbatim. -/

/-- ℂ twin of Polytope.`mem_rint_iff` (:252). -/
private theorem p22_mem_rint_iffC {s : Set ℂ} {x : ℂ} :
    x ∈ intrinsicInterior ℝ s ↔
      x ∈ s ∧ ∃ ε > 0, (Metric.ball x ε ∩ (affineSpan ℝ s : Set ℂ)) ⊆ s := by
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
      Metric.mem_ball.2 (show dist (w : ℂ) (y : ℂ) < ε from hw.1)
    exact Set.mem_preimage.1 (htsub (hball hwball))
  · rintro ⟨hxmem, ε, hε, hsub⟩
    have hxaff : x ∈ (affineSpan ℝ s : Set ℂ) := subset_affineSpan ℝ s hxmem
    have hsub' : Metric.ball (⟨x, hxaff⟩ : ↥(affineSpan ℝ s)) ε ⊆
        (Subtype.val ⁻¹' s) := by
      intro w hw
      have hwball : w.1 ∈ Metric.ball x ε := hw
      exact Set.mem_preimage.2 (hsub (Set.mem_inter hwball w.2))
    rw [mem_intrinsicInterior]
    exact ⟨⟨x, hxaff⟩, mem_interior.2 ⟨Metric.ball (⟨x, hxaff⟩ : ↥(affineSpan ℝ s)) ε,
      hsub', Metric.isOpen_ball, Metric.mem_ball_self hε⟩, rfl⟩

/-- ℂ twin of Polytope.`affineSpan_lineq` (:280). -/
private theorem p22_affineSpan_lineqC {s : Set ℂ} {p p' q : ℂ}
    (hp : p ∈ (affineSpan ℝ s : Set ℂ)) (hp' : p' ∈ (affineSpan ℝ s : Set ℂ))
    (hq : q ∈ (affineSpan ℝ s : Set ℂ)) (t : ℝ) :
    p' + t • (q - p) ∈ (affineSpan ℝ s : Set ℂ) := by
  have hdir : t • (q -ᵥ p) ∈ (affineSpan ℝ s).direction :=
    Submodule.smul_mem _ t (AffineSubspace.vsub_mem_direction hq hp)
  have hvadd : (t • (q -ᵥ p)) +ᵥ p' = p' + t • (q - p) := by
    rw [vadd_eq_add, vsub_eq_sub]
    module
  rw [← hvadd]
  exact AffineSubspace.vadd_mem_of_mem_direction hdir hp'

/-- ℂ twin of Polytope.`subset_of_faceOf` (:369). -/
private theorem p22_subset_of_faceOfC {t s u : Set ℂ} (hface : faceOfC t s) (husub : u ⊆ s)
    (hdisj : ¬Disjoint t (intrinsicInterior ℝ u)) : u ⊆ t := by
  obtain ⟨b, hb⟩ := Set.not_disjoint_iff.1 hdisj
  obtain ⟨hbu, ε, hε0, hball⟩ := p22_mem_rint_iffC.1 hb.2
  have hbt : b ∈ t := hb.1
  have hbu_aff : b ∈ (affineSpan ℝ u : Set ℂ) := subset_affineSpan ℝ u hbu
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
      · exact p22_affineSpan_lineqC (subset_affineSpan ℝ u hc) hbu_aff hbu_aff lam
    have hd : b + lam • (b - c) ∈ s := husub hdm
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

/-- ℂ twin of Polytope.`faceOf_eq` (:416). -/
private theorem p22_faceOfC_eq {s t u : Set ℂ} (ht : faceOfC t s) (hu : faceOfC u s)
    (h : ¬Disjoint (intrinsicInterior ℝ t) (intrinsicInterior ℝ u)) : t = u := by
  refine subset_antisymm ?_ ?_
  · refine p22_subset_of_faceOfC hu ht.1 fun hd => h ?_
    exact (Disjoint.mono_left intrinsicInterior_subset hd).symm
  · refine p22_subset_of_faceOfC ht hu.1 fun hd => h ?_
    exact Disjoint.mono_left intrinsicInterior_subset hd

/-- ℂ twin of Polytope.`faceOf_disjoint_rinterior` (:427). -/
private theorem p22_faceOfC_disjoint_rinterior {f s : Set ℂ} (hf : faceOfC f s)
    (hne : f ≠ s) : Disjoint f (intrinsicInterior ℝ s) := by
  by_contra h
  exact hne (subset_antisymm hf.1 (p22_subset_of_faceOfC hf (subset_refl s) h))

/-- ℂ twin of Polytope.`faceOf_eq_affineInter` (:461). -/
private theorem p22_faceOfC_eq_affineInter {t s : Set ℂ} (_hs : Convex ℝ s)
    (hface : faceOfC t s) : (affineSpan ℝ t : Set ℂ) ∩ s ⊆ t := by
  by_cases hte : t = ∅
  · rintro (y ⟨hyaff, -⟩)
    rw [hte, AffineSubspace.span_empty, AffineSubspace.bot_coe] at hyaff
    exact absurd hyaff (by simp)
  · obtain ⟨x0, hx0⟩ := nonempty_iff_ne_empty.2 hte
    obtain ⟨x0i, hx0i⟩ := Set.Nonempty.intrinsicInterior hface.2.1 ⟨x0, hx0⟩
    obtain ⟨hx0mem, ε, hε0, hball⟩ := p22_mem_rint_iffC.1 hx0i
    have hx0aff : x0i ∈ (affineSpan ℝ t : Set ℂ) := subset_affineSpan ℝ t hx0mem
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
      have hx0' : x0i + α • (y - x0i) ∈ t := by
        refine hball (Set.mem_inter ?_ (p22_affineSpan_lineqC hx0aff hx0aff hyaff α))
        refine Metric.mem_ball.2 ?_
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hα0]
        calc α * ‖y - x0i‖ ≤ ε / 3 := hαe
          _ < ε := by linarith
      have hx0's : x0i + α • (y - x0i) ∈ s := hface.1 hx0'
      have hx0'a : x0i + α • (y - x0i) ∈ (affineSpan ℝ t : Set ℂ) :=
        p22_affineSpan_lineqC hx0aff hx0aff hyaff α
      have hdmid : x0i + α • (y - x0i) + α • (y - (x0i + α • (y - x0i))) ∈ t := by
        refine hball (Set.mem_inter ?_ (p22_affineSpan_lineqC hx0'a hx0'a hyaff α))
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

/-- A planar halfspace is convex. -/
private theorem p22_convex_halfspaceC (a : ℂ) (b : ℝ) :
    Convex ℝ {x : ℂ | dot2 a x ≤ b} := by
  intro u hu v hv c d hc hd hcd
  simp only [Set.mem_setOf_eq] at hu hv ⊢
  rw [dot2_add_right, dot2_smul_right, dot2_smul_right]
  have h1 : c * dot2 a u ≤ c * b := mul_le_mul_of_nonneg_left hu hc
  have h2 : d * dot2 a v ≤ d * b := mul_le_mul_of_nonneg_left hv hd
  have h3 : c * b + d * b = b := by rw [← add_mul, hcd, one_mul]
  linarith

/-- A planar polyhedron is convex (doc §2.2 scratch twin). -/
private theorem p22_polyhedronC_convex {P : Set ℂ} (hP : polyhedronC P) : Convex ℝ P := by
  obtain ⟨F, hFfin, hs, hFprop⟩ := hP
  refine hs ▸ convex_sInter ?_
  intro G hG
  obtain ⟨a, b, -, hGeq⟩ := hFprop G hG
  rw [hGeq]
  exact p22_convex_halfspaceC a b

/-- HOL `POLYHEDRON_INTER_AFFINE_MINIMAL` ℂ 版 (Polytope:831)：polyhedronC 容许
*冗余无关*的有限半空间表示（真子族必严格放大 `affineSpan ∩ ⋂₀`）。 -/
private theorem p22_polyhedronC_minrep {P : Set ℂ} (hP : polyhedronC P) :
    ∃ F : Set (Set ℂ), F.Finite ∧
      P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F ∧
      (∀ h ∈ F, ∃ a : ℂ, ∃ b : ℝ, a ≠ 0 ∧ h = {x : ℂ | dot2 a x ≤ b}) ∧
      ∀ F', F' ⊂ F → P ⊂ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F' := by
  classical
  obtain ⟨F0, hF0, hs0, hF0prop⟩ := hP
  have hs0' : P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F0 := by
    refine Set.ext fun x => ?_
    constructor
    · intro hx
      exact ⟨subset_affineSpan ℝ P hx, hs0 ▸ hx⟩
    · rintro ⟨-, hx⟩
      exact hs0 ▸ hx
  set Swit : Set (Set (Set ℂ)) := {G : Set (Set ℂ) | G.Finite ∧
    P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ G ∧
    (∀ h ∈ G, ∃ a : ℂ, ∃ b : ℝ, a ≠ 0 ∧ h = {x : ℂ | dot2 a x ≤ b})} with hSwit
  have hWne : Swit.Nonempty := ⟨F0, by
    rw [hSwit, Set.mem_setOf_eq]
    exact ⟨hF0, hs0', hF0prop⟩⟩
  set F := Function.argminOn (f := Set.ncard) Swit hWne with hFdef
  have hFmem : F ∈ Swit := Function.argminOn_mem (f := Set.ncard) Swit hWne
  obtain ⟨hF, hs, hFprop⟩ : (F.Finite ∧ P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F ∧
      ∀ h ∈ F, ∃ a : ℂ, ∃ b : ℝ, a ≠ 0 ∧ h = {x : ℂ | dot2 a x ≤ b}) := hFmem
  refine ⟨F, hF, hs, hFprop, ?_⟩
  intro F' hsub
  have hsubFF : F' ⊆ F := hsub.1
  have hF'fin : F'.Finite := hF.subset hsubFF
  have hF'prop : ∀ h ∈ F', ∃ a : ℂ, ∃ b : ℝ, a ≠ 0 ∧ h = {x : ℂ | dot2 a x ≤ b} :=
    fun h hk => hFprop h (hsubFF hk)
  have hssub : P ⊆ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F' := by
    refine Set.subset_inter (subset_affineSpan ℝ P) ?_
    calc P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F := hs
      _ ⊆ ⋂₀ F := Set.inter_subset_right
      _ ⊆ ⋂₀ F' := Set.sInter_subset_sInter hsubFF
  refine Set.ssubset_iff_subset_ne.2 ⟨hssub, fun heq => ?_⟩
  have hF'mem : F' ∈ Swit := by
    rw [hSwit, Set.mem_setOf_eq]
    exact ⟨hF'fin, heq, hF'prop⟩
  have hlt : F'.ncard < F.ncard := Set.ncard_lt_ncard hsub hF
  exact Function.not_lt_argminOn (f := Set.ncard) Swit hF'mem hlt

/-- ℂ twin of Polytope.`convex_of_minrep` (:1105). -/
private theorem p22_convex_of_minrep {P : Set ℂ} {F : Set (Set ℂ)}
    (hF : F.Finite)
    (hs : P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, ∃ a : ℂ, ∃ b : ℝ, a ≠ 0 ∧ h = {x : ℂ | dot2 a x ≤ b}) :
    Convex ℝ P := by
  have haff : Convex ℝ (affineSpan ℝ P : Set ℂ) := (affineSpan ℝ P).convex
  have hinter : Convex ℝ (⋂₀ F) := convex_sInter (fun G hG => by
    obtain ⟨a, b, -, hGeq⟩ := hFprop G hG
    rw [hGeq]
    exact p22_convex_halfspaceC a b)
  refine hs ▸ Convex.inter haff hinter

/-- Continuity of the planar linear functional `x ↦ dot2 a x`. -/
private theorem p22_continuous_dot2C (a : ℂ) : Continuous (dot2 a) := by
  have h : dot2 a = fun x => a.re * x.re + a.im * x.im := by
    funext x
    exact dot2_expand a x
  rw [h]
  refine Continuous.add ?_ ?_
  · exact Continuous.mul continuous_const Complex.continuous_re
  · exact Continuous.mul continuous_const Complex.continuous_im

/-- HOL `RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT` ℂ 版 (Polytope:874)。 -/
private theorem p22_rint_minrepC {P : Set ℂ} {F : Set (Set ℂ)}
    (a : Set ℂ → ℂ) (b : Set ℂ → ℝ)
    (hF : F.Finite)
    (hs : P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : ℂ | dot2 (a h) x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → P ⊂ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F') :
    intrinsicInterior ℝ P = {x : ℂ | x ∈ P ∧ ∀ h ∈ F, dot2 (a h) x < b h} := by
  classical
  haveI : Finite F := hF
  ext x
  constructor
  · intro hx
    obtain ⟨hxmem, ε, hε0, hball⟩ := p22_mem_rint_iffC.1 hx
    refine ⟨hxmem, fun h hk => ?_⟩
    obtain ⟨haH, hh⟩ := hFprop h hk
    have hxInter : x ∈ ⋂₀ F := by rw [hs] at hxmem; exact hxmem.2
    have hxh : x ∈ h := Set.mem_sInter.1 hxInter h hk
    rw [hh, Set.mem_setOf_eq] at hxh
    have hxA : dot2 (a h) x ≤ b h := hxh
    by_contra hcon
    push_neg at hcon
    have heq : dot2 (a h) x = b h := le_antisymm hxA hcon
    have hsdiff : F \ {h} ⊂ F := by
      refine Set.ssubset_iff_subset_ne.2 ⟨Set.sdiff_subset, fun hEq => ?_⟩
      have hmem' : h ∈ F \ {h} := by rw [hEq]; exact hk
      exact absurd hmem'.2 (by simp)
    obtain ⟨-, z, hzT, hzs⟩ := Set.ssubset_iff_exists.1 (hmin _ hsdiff)
    have hzaff : z ∈ (affineSpan ℝ P : Set ℂ) := hzT.1
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
    have hAz : b h < dot2 (a h) z := by
      have hkz : z ∉ h := by rw [← hih]; exact hzi
      rw [hh] at hkz
      simpa only [Set.mem_setOf_eq, not_le] using hkz
    set t : ℝ := min (1 / 2) (ε / (2 * (‖z - x‖ + 1))) with htdef
    have ht0 : 0 < t := lt_min (by norm_num : (0:ℝ) < 1 / 2)
      (div_pos hε0 (by positivity))
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num : (1 / 2 : ℝ) < 1)
    have hwball : ‖x + t • (z - x) - x‖ < ε := by
      have hstep : x + t • (z - x) - x = t • (z - x) := by rw [smul_sub]; module
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
    have hxaff : x ∈ (affineSpan ℝ P : Set ℂ) := subset_affineSpan ℝ P hxmem
    have hwdist : dist (x + t • (z - x)) x < ε := by
      rw [dist_eq_norm]
      exact hwball
    have hw : x + t • (z - x) ∈ P :=
      hball ⟨Metric.mem_ball.2 hwdist, p22_affineSpan_lineqC hxaff hxaff hzaff t⟩
    have hws : x + t • (z - x) ∈ ⋂₀ F := by rw [hs] at hw; exact hw.2
    have hwh : x + t • (z - x) ∈ h := Set.mem_sInter.1 hws h hk
    rw [hh, Set.mem_setOf_eq] at hwh
    have hwA : dot2 (a h) (x + t • (z - x)) ≤ b h := hwh
    have hAw : dot2 (a h) (x + t • (z - x))
        = dot2 (a h) x + t * (dot2 (a h) z - dot2 (a h) x) := by
      have e1 : dot2 (a h) (x + t • (z - x))
          = dot2 (a h) x + dot2 (a h) (t • (z - x)) := dot2_add_right _ _ _
      have e2 : dot2 (a h) (t • (z - x)) = t * (dot2 (a h) (z - x)) :=
        dot2_smul_right _ _ _
      have e3 : dot2 (a h) (z - x) = dot2 (a h) z - dot2 (a h) x := dot2_sub_r _ _ _
      rw [e1, e2, e3]
    rw [heq] at hAw
    rw [hAw] at hwA
    have hpos' : 0 < t * (dot2 (a h) z - b h) := mul_pos ht0 (by linarith)
    linarith
  · rintro ⟨hxmem, hstrict⟩
    set O : Set ℂ := ⋂ h : {y // y ∈ F}, {y : ℂ | dot2 (a h) y < b h} with hO
    have hOopen : IsOpen O := by
      rw [hO]
      exact isOpen_iInter_of_finite fun h => isOpen_lt
        (p22_continuous_dot2C (a h.1)) continuous_const
    have hxO : x ∈ O := by
      rw [hO, Set.mem_iInter]
      exact fun h => hstrict h.1 h.2
    obtain ⟨δ, hδ0, hballδ⟩ := Metric.isOpen_iff.1 hOopen x hxO
    refine p22_mem_rint_iffC.2 ⟨hxmem, δ, hδ0, fun y hy => ?_⟩
    rw [hs]
    refine ⟨hy.2, fun i hi => ?_⟩
    obtain ⟨-, hhi⟩ := hFprop i hi
    have hyO : y ∈ O := hballδ (Metric.mem_ball.2 hy.1)
    rw [hO] at hyO
    have hyi : dot2 (a i) y < b i := Set.mem_iInter.1 hyO ⟨i, hi⟩
    rw [hhi]
    exact Set.mem_setOf.2 (le_of_lt hyi)

/-- ℂ twin of Polytope.`faceOf_supporting_eq` (:983): a supporting hyperplane
cuts a face. -/
private theorem p22_faceOfC_supporting_eq {s : Set ℂ} (hs : Convex ℝ s) (a : ℂ) (c : ℝ)
    (hsub : ∀ x ∈ s, dot2 a x ≤ c) :
    faceOfC (s ∩ {x : ℂ | dot2 a x = c}) s := by
  refine ⟨Set.inter_subset_left, ?_, ?_⟩
  · intro p hp q hq u v hu1 hv1 hab
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq ⊢
    obtain ⟨hps, hpP⟩ := hp
    obtain ⟨hqs, hqP⟩ := hq
    refine ⟨hs hps hqs hu1 hv1 hab, ?_⟩
    have e1 : dot2 a (u • p + v • q) = u * (dot2 a p) + v * (dot2 a q) := by
      rw [dot2_add_right, dot2_smul_right, dot2_smul_right]
    rw [e1, hpP, hqP]
    have hcc : (u + v) * c = c := by rw [hab, one_mul]
    linarith [mul_add u v c, mul_comm v c, hcc]
  · rintro p q x hps hqs hx hseg
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨hxs, hxe⟩ := hx
    obtain ⟨u, v, hu0, hv0, huv, hxuv⟩ := hseg
    have e1 : dot2 a (u • p + v • q) = u * (dot2 a p) + v * (dot2 a q) := by
      rw [dot2_add_right, dot2_smul_right, dot2_smul_right]
    have hpx : dot2 a x = u * (dot2 a p) + v * (dot2 a q) := by
      rw [← hxuv, e1]
    rw [hxe] at hpx
    have key : u * (c - dot2 a p) + v * (c - dot2 a q) = 0 := by
      have h2 : u * (c - dot2 a p) + v * (c - dot2 a q)
          = (u + v) * c - (u * (dot2 a p) + v * (dot2 a q)) := by ring
      rw [h2, huv, one_mul, ← hpx]
      ring
    have hpp : dot2 a p = c := by
      by_contra hne
      have hgt : dot2 a p < c := lt_of_le_of_ne (hsub p hps) hne
      have hppos : 0 < u * (c - dot2 a p) := mul_pos hu0 (sub_pos.2 hgt)
      have hqpos : 0 ≤ v * (c - dot2 a q) :=
        mul_nonneg hv0.le (sub_nonneg.2 (hsub q hqs))
      linarith
    have hqq : dot2 a q = c := by
      by_contra hne
      have hgt : dot2 a q < c := lt_of_le_of_ne (hsub q hqs) hne
      have hppos : 0 < v * (c - dot2 a q) := mul_pos hv0 (sub_pos.2 hgt)
      have hqpos : 0 ≤ u * (c - dot2 a p) :=
        mul_nonneg hu0.le (sub_nonneg.2 (hsub p hps))
      linarith
    exact ⟨⟨hps, hpp⟩, ⟨hqs, hqq⟩⟩

/-- ℂ twin of Polytope.`FACE_OF_POLYHEDRON_SLICE` (:1030). -/
private theorem p22_faceOfC_slice {P : Set ℂ} {F : Set (Set ℂ)}
    (a : Set ℂ → ℂ) (b : Set ℂ → ℝ) (hF : F.Finite)
    (hs : P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : ℂ | dot2 (a h) x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → P ⊂ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F')
    (h : Set ℂ) (hk : h ∈ F) :
    faceOfC (P ∩ {x : ℂ | dot2 (a h) x = b h}) P := by
  obtain ⟨-, hh⟩ := hFprop h hk
  have hsup : ∀ x ∈ P, dot2 (a h) x ≤ b h := by
    intro x hx
    have hxInter : x ∈ ⋂₀ F := by rw [hs] at hx; exact hx.2
    have hxh : x ∈ h := Set.mem_sInter.1 hxInter h hk
    rw [hh, Set.mem_setOf_eq] at hxh
    exact hxh
  exact p22_faceOfC_supporting_eq
    (p22_convex_of_minrep hF hs (fun k hk => ⟨a k, b k, (hFprop k hk).1, (hFprop k hk).2⟩))
    (a h) (b h) hsup

/-- ℂ twin of Polytope.`slice_sides` (:1115). -/
private theorem p22_slice_sides {P : Set ℂ} {F : Set (Set ℂ)}
    (a : Set ℂ → ℂ) (b : Set ℂ → ℝ) (hF : F.Finite)
    (hs : P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : ℂ | dot2 (a h) x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → P ⊂ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F')
    (hsne : P ≠ ∅) (h : Set ℂ) (hh : h ∈ F) :
    ∃ x z : ℂ, x ∈ P ∧ (∀ i ∈ F, dot2 (a i) x < b i) ∧
      z ∈ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ (F \ {h}) ∧
      dot2 (a h) x < b h ∧ b h < dot2 (a h) z := by
  have hconv := p22_convex_of_minrep hF hs
    (fun k hk => ⟨a k, b k, (hFprop k hk).1, (hFprop k hk).2⟩)
  have hrie : intrinsicInterior ℝ P = {x : ℂ | x ∈ P ∧ ∀ i ∈ F, dot2 (a i) x < b i} :=
    p22_rint_minrepC a b hF hs hFprop hmin
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hconv (nonempty_iff_ne_empty.2 hsne)
  have hx' : x ∈ P ∧ ∀ i ∈ F, dot2 (a i) x < b i := by rw [hrie] at hx; exact hx
  have hsdiff : F \ {h} ⊂ F := by
    refine Set.ssubset_iff_subset_ne.2 ⟨Set.sdiff_subset, fun hEq => ?_⟩
    have hmem' : h ∈ F \ {h} := by rw [hEq]; exact hh
    exact absurd hmem'.2 (by simp)
  obtain ⟨-, z, hzT, hzs⟩ := Set.ssubset_iff_exists.1 (hmin _ hsdiff)
  have hzaff : z ∈ (affineSpan ℝ P : Set ℂ) := hzT.1
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
  have hzA : b h < dot2 (a h) z := by
    have hkz : z ∉ h := by rw [← hih]; exact hzi
    rw [(hFprop h hh).2] at hkz
    simpa only [Set.mem_setOf_eq, not_le] using hkz
  exact ⟨x, z, hx'.1, hx'.2, ⟨hzaff, hzT.2⟩, hx'.2 h hh, hzA⟩

/-- ℂ twin of Polytope.`slice_cross` (:1152). -/
private theorem p22_slice_cross {P : Set ℂ} {F : Set (Set ℂ)}
    (a : Set ℂ → ℂ) (b : Set ℂ → ℝ) (hF : F.Finite)
    (hs : P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : ℂ | dot2 (a h) x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → P ⊂ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F')
    (hsne : P ≠ ∅) (h : Set ℂ) (hh : h ∈ F) :
    ∃ x : ℂ, x ∈ P ∧ dot2 (a h) x = b h ∧
      (∀ i ∈ F, i ≠ h → dot2 (a i) x < b i) ∧ x ∈ (affineSpan ℝ P : Set ℂ) := by
  obtain ⟨p, z, hps, hpstrict, hzs, hpl, hzg⟩ :=
    p22_slice_sides a b hF hs hFprop hmin hsne h hh
  have hpaff : p ∈ (affineSpan ℝ P : Set ℂ) := subset_affineSpan ℝ P hps
  have hzaff : z ∈ (affineSpan ℝ P : Set ℂ) := hzs.1
  obtain ⟨t, htp, ht1, htden⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      t * (dot2 (a h) z - dot2 (a h) p) = b h - dot2 (a h) p :=
    ⟨(b h - dot2 (a h) p) / (dot2 (a h) z - dot2 (a h) p),
      div_pos (by linarith) (by linarith),
      (div_lt_one (by linarith)).2 (by linarith), div_mul_cancel₀ _ (by linarith)⟩
  have hqdot : ∀ w : ℂ, dot2 w (p + t • (z - p)) = dot2 w p + t * (dot2 w z - dot2 w p) := by
    intro w
    have e1 : dot2 w (p + t • (z - p)) = dot2 w p + dot2 w (t • (z - p)) :=
      dot2_add_right _ _ _
    have e2 : dot2 w (t • (z - p)) = t * (dot2 w (z - p)) := dot2_smul_right _ _ _
    have e3 : dot2 w (z - p) = dot2 w z - dot2 w p := dot2_sub_r _ _ _
    rw [e1, e2, e3]
  refine ⟨p + t • (z - p), ?_, ?_, ?_, ?_⟩
  · rw [hs]
    refine ⟨p22_affineSpan_lineqC hpaff hpaff hzaff t, fun i hi => ?_⟩
    rw [(hFprop i hi).2, Set.mem_setOf_eq, hqdot (a i)]
    by_cases hih : i = h
    · rw [← hih] at htden
      linarith
    · have hiz : dot2 (a i) z ≤ b i := by
        have hzi : z ∈ i :=
          Set.mem_sInter.1 hzs.2 i ((Set.mem_sdiff i).2 ⟨hi, hih⟩)
        rw [(hFprop i hi).2] at hzi
        exact hzi
      have hstep : t * (dot2 (a i) z - dot2 (a i) p) ≤ t * (b i - dot2 (a i) p) :=
        mul_le_mul_of_nonneg_left (by linarith) htp.le
      have hkey : t * (b i - dot2 (a i) p) < b i - dot2 (a i) p := by
        refine lt_of_lt_of_le
          (mul_lt_mul_of_pos_right ht1 (by linarith [hpstrict i hi])) ?_
        rw [one_mul]
      linarith
  · rw [hqdot (a h)]
    linarith
  · intro i hi hih
    rw [hqdot (a i)]
    have hiz : dot2 (a i) z ≤ b i := by
      have hzi : z ∈ i := Set.mem_sInter.1 hzs.2 i ((Set.mem_sdiff i).2 ⟨hi, hih⟩)
      rw [(hFprop i hi).2] at hzi
      exact hzi
    have hstep : t * (dot2 (a i) z - dot2 (a i) p) ≤ t * (b i - dot2 (a i) p) :=
      mul_le_mul_of_nonneg_left (by linarith) htp.le
    have hkey : t * (b i - dot2 (a i) p) < b i - dot2 (a i) p := by
      refine lt_of_lt_of_le
        (mul_lt_mul_of_pos_right ht1 (by linarith [hpstrict i hi])) ?_
      rw [one_mul]
    linarith
  · exact p22_affineSpan_lineqC hpaff hpaff hzaff t

/-- ℂ twin of Polytope.`vectorSpan_slice` (:1212): the span of a nonempty
hyperplane slice of `P` is the direction of `P` killed by the slice normal. -/
private theorem p22_vectorSpan_slice {P : Set ℂ} {F : Set (Set ℂ)}
    (a : Set ℂ → ℂ) (b : Set ℂ → ℝ) (hF : F.Finite)
    (hs : P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : ℂ | dot2 (a h) x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → P ⊂ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F')
    (hsne : P ≠ ∅) (h : Set ℂ) (hh : h ∈ F) :
    vectorSpan ℝ (P ∩ {x : ℂ | dot2 (a h) x = b h})
      = vectorSpan ℝ P ⊓ LinearMap.ker (dotRightC (a h)) := by
  classical
  obtain ⟨x0, hx0s, hx0eq, hx0st, hx0aff⟩ := p22_slice_cross a b hF hs hFprop hmin hsne h hh
  haveI : Finite F := hF
  have hlin : ∀ u x y : ℂ, ∀ r : ℝ, dot2 u (x + r • y) = dot2 u x + r * (dot2 u y) := by
    intro u x y r
    have e1 : dot2 u (x + r • y) = dot2 u x + dot2 u (r • y) := dot2_add_right _ _ _
    have e2 : dot2 u (r • y) = r * dot2 u y := dot2_smul_right _ _ _
    rw [e1, e2]
  refine le_antisymm (le_inf (vectorSpan_mono ℝ Set.inter_subset_left) ?_) ?_
  · rw [vectorSpan_def, Submodule.span_le]
    rintro w ⟨p, hp, q, hq, rfl⟩
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq
    change (p -ᵥ q) ∈ ((LinearMap.ker (dotRightC (a h)) : Submodule ℝ ℂ) : Set ℂ)
    rw [vsub_eq_sub, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.map_sub,
      dotRightC_apply, dotRightC_apply]
    have hp' : dot2 (a h) p = b h := hp.2
    have hq' : dot2 (a h) q = b h := hq.2
    rw [hp', hq', sub_self]
  · intro w hw
    obtain ⟨hwW, hwK⟩ := Submodule.mem_inf.1 hw
    have hwK' : dotRightC (a h) w = 0 := LinearMap.mem_ker.1 hwK
    have hwK'' : dot2 (a h) w = 0 := hwK'
    have hwdir : w ∈ (affineSpan ℝ P).direction := by
      rw [direction_affineSpan]
      exact hwW
    set O : Set ℂ := ⋂ i : {y // y ∈ F}, {y : ℂ | dot2 (a i) y < b i ∨ i.1 = h} with hO
    have hOopen : IsOpen O := by
      rw [hO]
      refine isOpen_iInter_of_finite fun i => ?_
      by_cases hih : i.1 = h
      · have hset : {y : ℂ | dot2 (a i) y < b i ∨ i.1 = h} = (univ : Set ℂ) := by
          ext y
          simp [hih]
        rw [hset]
        exact isOpen_univ
      · have hset : {y : ℂ | dot2 (a i) y < b i ∨ i.1 = h}
            = {y : ℂ | dot2 (a i) y < b i} := by
          ext y
          simp [hih]
        rw [hset]
        exact isOpen_lt (p22_continuous_dot2C (a i.1)) continuous_const
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
    have htbdist : dist (x0 + t • w) x0 < ε := by
      rw [dist_eq_norm]
      exact htball
    have hqA : x0 + t • w ∈ (affineSpan ℝ P : Set ℂ) := by
      have hv : (t • w) +ᵥ x0 = x0 + t • w := by rw [vadd_eq_add]; module
      rw [← hv]
      exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hwdir) hx0aff
    have hqH : dot2 (a h) (x0 + t • w) = b h := by
      rw [hlin, hx0eq, hwK'', mul_zero, add_zero]
    have h1 : x0 + t • w ∈ ⋂₀ F := by
      refine Set.mem_sInter.2 fun i hi => ?_
      rw [(hFprop i hi).2, Set.mem_setOf_eq]
      by_cases hih : i = h
      · have hie : dot2 (a i) (x0 + t • w) = b i := by rw [hih]; exact hqH
        rw [hie]
      · have hqO : x0 + t • w ∈ O := hballO (Metric.mem_ball.2 htbdist)
        rw [hO] at hqO
        rcases Set.mem_iInter.1 hqO ⟨i, hi⟩ with h1' | h2
        · exact le_of_lt h1'
        · exact absurd h2 hih
    have hqs : x0 + t • w ∈ P := by
      rw [hs]
      exact ⟨hqA, h1⟩
    have hmemH : x0 + t • w ∈ {y : ℂ | dot2 (a h) y = b h} := by
      rw [Set.mem_setOf_eq]
      exact hqH
    have hmemH0 : x0 ∈ {y : ℂ | dot2 (a h) y = b h} := by
      rw [Set.mem_setOf_eq]
      exact hx0eq
    have hgen : (x0 + t • w - x0 : ℂ) ∈ vectorSpan ℝ (P ∩ {y : ℂ | dot2 (a h) y = b h}) :=
      Submodule.subset_span (Set.mem_vsub.2 ⟨x0 + t • w, ⟨hqs, hmemH⟩,
        x0, ⟨hx0s, hmemH0⟩, by rw [vsub_eq_sub]⟩)
    have hscale : w = (1 / t) • (x0 + t • w - x0) := by
      have hstep : x0 + t • w - x0 = t • w := by rw [add_sub_cancel_left]
      rw [hstep, smul_smul, one_div, inv_mul_cancel₀ ht0.ne', one_smul]
    rw [hscale]
    exact Submodule.smul_mem _ _ hgen

/-- ℂ twin of Polytope.`affDim_slice` (:1318): the slice has codimension one. -/
private theorem p22_affDim_slice {P : Set ℂ} {F : Set (Set ℂ)}
    (a : Set ℂ → ℂ) (b : Set ℂ → ℝ) (hF : F.Finite)
    (hs : P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : ℂ | dot2 (a h) x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → P ⊂ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F')
    (hsne : P ≠ ∅) (h : Set ℂ) (hh : h ∈ F) :
    affDimC (P ∩ {x : ℂ | dot2 (a h) x = b h}) = affDimC P - 1 := by
  classical
  obtain ⟨x0, hx0s, hx0eq, -, -⟩ := p22_slice_cross a b hF hs hFprop hmin hsne h hh
  have hune : (P ∩ {x : ℂ | dot2 (a h) x = b h}).Nonempty :=
    ⟨x0, ⟨hx0s, by rw [Set.mem_setOf_eq]; exact hx0eq⟩⟩
  obtain ⟨p, z, hps, -, hzs, hpl, hzg⟩ := p22_slice_sides a b hF hs hFprop hmin hsne h hh
  have hpaff : p ∈ (affineSpan ℝ P : Set ℂ) := subset_affineSpan ℝ P hps
  have hzaff : z ∈ (affineSpan ℝ P : Set ℂ) := hzs.1
  have hwW : z - p ∈ vectorSpan ℝ P := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hzaff hpaff
  have hwne : dotRightC (a h) (z - p) ≠ 0 := by
    show dot2 (a h) (z - p) ≠ 0
    rw [dot2_sub_r]
    linarith
  have hzp : (z - p : ℂ) ≠ 0 := fun hc => hwne (by rw [hc]; simp)
  have hveq : vectorSpan ℝ (P ∩ {x : ℂ | dot2 (a h) x = b h})
      = vectorSpan ℝ P ⊓ LinearMap.ker (dotRightC (a h)) :=
    p22_vectorSpan_slice a b hF hs hFprop hmin hsne h hh
  have hsup : ((vectorSpan ℝ P ⊓ LinearMap.ker (dotRightC (a h))) ⊔
      (ℝ ∙ (z - p) : Submodule ℝ ℂ)) = vectorSpan ℝ P := by
    refine le_antisymm (sup_le inf_le_left ?_) ?_
    · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 hwW)
    · intro v hv
      have hd0 : dotRightC (a h) (z - p) ≠ 0 := hwne
      refine Submodule.mem_sup.2 ⟨v - (dotRightC (a h) v / dotRightC (a h) (z - p)) • (z - p),
        ?_, (dotRightC (a h) v / dotRightC (a h) (z - p)) • (z - p), ?_, ?_⟩
      · refine ⟨Submodule.sub_mem (p := vectorSpan ℝ P) hv
            (Submodule.smul_mem _ _ hwW), ?_⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.map_sub, LinearMap.map_smul,
          smul_eq_mul]
        field_simp
        ring
      · exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
      · rw [sub_add_cancel]
  have hinf : ((vectorSpan ℝ P ⊓ LinearMap.ker (dotRightC (a h))) ⊓
      (ℝ ∙ (z - p) : Submodule ℝ ℂ)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hvS⟩ := Submodule.mem_inf.1 hv
    obtain ⟨-, hvK⟩ := Submodule.mem_inf.1 hvW
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hvS
    have hker : dotRightC (a h) v = 0 := hvK
    rw [← hc, LinearMap.map_smul, smul_eq_mul] at hker
    have hcv : c = 0 := by
      rcases mul_eq_zero.1 hker with h0 | h0
      · exact h0
      · exact absurd h0 hwne
    rw [← hc, hcv, zero_smul]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq
    (vectorSpan ℝ P ⊓ LinearMap.ker (dotRightC (a h))) (ℝ ∙ (z - p))
  rw [hsup, hinf, finrank_bot, finrank_span_singleton hzp] at h1
  simp only [affDimC, if_neg (nonempty_iff_ne_empty.1 hune), if_neg hsne]
  rw [hveq]
  have e1 : (↑(Module.finrank ℝ (vectorSpan ℝ P)) : ℤ)
      = ↑(Module.finrank ℝ
          (vectorSpan ℝ P ⊓ LinearMap.ker (dotRightC (a h)) : Submodule ℝ ℂ)) + 1 := by
    omega
  omega

/-! ## #13 facetOfCPolyhedronExplicit (ℂ port of Polytope.lean:1390,
HOL polytope.ml:4718 FACET_OF_POLYHEDRON_EXPLICIT) -/

/-- HOL `FACET_OF_POLYHEDRON_EXPLICIT` ℂ 版：对给定冗余无关半空间表示的
polyhedron，facets 恰为单个约束切出的超平面截口。 -/
theorem facetOfCPolyhedronExplicit {P : Set ℂ} {F : Set (Set ℂ)}
    (a : Set ℂ → ℂ) (b : Set ℂ → ℝ) (hF : F.Finite)
    (hs : P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F)
    (hFprop : ∀ h ∈ F, a h ≠ 0 ∧ h = {x : ℂ | dot2 (a h) x ≤ b h})
    (hmin : ∀ F', F' ⊂ F → P ⊂ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F')
    (c : Set ℂ) :
    facetOfC c P ↔ ∃ h, h ∈ F ∧ c = P ∩ {x : ℂ | dot2 (a h) x = b h} := by
  classical
  have hrie : intrinsicInterior ℝ P = {y : ℂ | y ∈ P ∧ ∀ i ∈ F, dot2 (a i) y < b i} :=
    p22_rint_minrepC a b hF hs hFprop hmin
  constructor
  · rintro ⟨hface, hcne, hcdim⟩
    by_cases hse : P = ∅
    · rw [hse] at hface
      exact absurd (Set.eq_empty_of_subset_empty hface.1) hcne
    · have hconv : Convex ℝ P := p22_convex_of_minrep hF hs
        (fun h hk => ⟨a h, b h, (hFprop h hk).1, (hFprop h hk).2⟩)
      have hcs : c ≠ P := by
        intro heq
        rw [heq] at hcdim
        have hpos : (0 : ℤ) ≤ affDimC P := by
          simp only [affDimC, if_neg hse]
          have hh : (0 : ℤ) ≤ (Module.finrank ℝ (vectorSpan ℝ P) : ℤ) := by
            exact_mod_cast Nat.zero_le _
          exact hh
        linarith
      -- a point of the relative interior of the facet
      obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hface.2.1
        (nonempty_iff_ne_empty.2 hcne)
      have hxc : x ∈ c := (p22_mem_rint_iffC.1 hx).1
      have hxinS : x ∈ P := hface.1 hxc
      have hxnot : x ∉ intrinsicInterior ℝ P :=
        Set.disjoint_left.1 (p22_faceOfC_disjoint_rinterior hface hcs) hxc
      -- the tight constraint `j` of the minimal representation at `x`
      obtain ⟨j, hjF, hj⟩ : ∃ i ∈ F, ¬(dot2 (a i) x < b i) := by
        by_contra hcon
        push_neg at hcon
        exact hxnot (by rw [hrie]; exact ⟨hxinS, hcon⟩)
      have hxmem2 : x ∈ ⋂₀ F := by
        rw [hs] at hxinS
        exact hxinS.2
      have hxj : dot2 (a j) x ≤ b j := by
        have h0 : x ∈ j := Set.mem_sInter.1 hxmem2 j hjF
        rw [(hFprop j hjF).2] at h0
        exact h0
      have hjeq : dot2 (a j) x = b j := le_antisymm hxj (not_lt.1 hj)
      have hxu : x ∈ P ∩ {y : ℂ | dot2 (a j) y = b j} :=
        ⟨hxinS, by rw [Set.mem_setOf_eq]; exact hjeq⟩
      -- the facet is contained in the slice (both faces, rint's meet at x)
      have hcu : c ⊆ P ∩ {y : ℂ | dot2 (a j) y = b j} :=
        p22_subset_of_faceOfC (p22_faceOfC_slice a b hF hs hFprop hmin j hjF)
          hface.1 (Set.not_disjoint_iff.2 ⟨x, hxu, hx⟩)
      -- dimension descent
      have hun : (P ∩ {y : ℂ | dot2 (a j) y = b j}).Nonempty := ⟨x, hxu⟩
      have hc' : c.Nonempty := nonempty_iff_ne_empty.2 hcne
      have hcdim' := p22_affDim_slice a b hF hs hFprop hmin hse j hjF
      have hfeq2 : Module.finrank ℝ (vectorSpan ℝ c)
          = Module.finrank ℝ (vectorSpan ℝ (P ∩ {y : ℂ | dot2 (a j) y = b j})) := by
        have h1 : affDimC c = affDimC (P ∩ {y : ℂ | dot2 (a j) y = b j}) := by
          rw [hcdim, hcdim']
        simp only [affDimC, if_neg (nonempty_iff_ne_empty.1 hc'),
          if_neg (nonempty_iff_ne_empty.1 hun)] at h1
        exact_mod_cast h1
      have hveq : vectorSpan ℝ c = vectorSpan ℝ (P ∩ {y : ℂ | dot2 (a j) y = b j}) :=
        Submodule.eq_of_le_of_finrank_le (vectorSpan_mono ℝ hcu)
          (le_of_eq hfeq2.symm)
      have heq2 : (affineSpan ℝ c : AffineSubspace ℝ ℂ)
          = affineSpan ℝ (P ∩ {y : ℂ | dot2 (a j) y = b j}) := by
        refine AffineSubspace.eq_of_direction_eq_of_nonempty_of_le ?_
          ⟨x, subset_affineSpan ℝ _ hxc⟩ (affineSpan_mono ℝ hcu)
        rw [direction_affineSpan, direction_affineSpan, hveq]
      -- the slice is contained in the facet, since their spans agree
      refine ⟨j, hjF, subset_antisymm hcu ?_⟩
      intro y hy
      refine p22_faceOfC_eq_affineInter hconv hface ⟨?_, hy.1⟩
      rw [heq2]
      exact subset_affineSpan ℝ _ hy
  · rintro ⟨j, hjF, rfl⟩
    by_cases hse : P = ∅
    · -- an irredundant representation of `P = ∅` uses `F = ∅`
      have hFe : F = ∅ := by
        by_contra hFne
        have hne0 : (∅ : Set (Set ℂ)) ⊂ F :=
          Set.ssubset_iff_subset_ne.2 ⟨Set.empty_subset _, Ne.symm hFne⟩
        obtain ⟨-, w, hwT, -⟩ := Set.ssubset_iff_exists.1 (hmin _ hne0)
        rw [hse, AffineSubspace.span_empty, AffineSubspace.bot_coe] at hwT
        exact absurd hwT.1 (by simp)
      exact absurd hjF (by rw [hFe]; simp)
    · obtain ⟨x0, hx0s, hx0eq, -, -⟩ := p22_slice_cross a b hF hs hFprop hmin hse j hjF
      refine ⟨p22_faceOfC_slice a b hF hs hFprop hmin j hjF, ?_, ?_⟩
      · exact nonempty_iff_ne_empty.1
          ⟨x0, ⟨hx0s, by rw [Set.mem_setOf_eq]; exact hx0eq⟩⟩
      · exact p22_affDim_slice a b hF hs hFprop hmin hse j hjF

/-- Skolemized minimal halfspace representation of a planar polyhedron
(ℂ twin of Polytope.`minrep_skolem` :1736). -/
private theorem p22_minrep_skolem {P : Set ℂ} (hP : polyhedronC P) :
    ∃ F : Set (Set ℂ), F.Finite ∧ P = (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F ∧
      ∃ a : Set ℂ → ℂ, ∃ b : Set ℂ → ℝ,
        (∀ h ∈ F, a h ≠ 0 ∧ h = {x : ℂ | dot2 (a h) x ≤ b h}) ∧
        ∀ F', F' ⊂ F → P ⊂ (affineSpan ℝ P : Set ℂ) ∩ ⋂₀ F' := by
  classical
  obtain ⟨F, hF, hs, hFprop, hmin⟩ := p22_polyhedronC_minrep hP
  have hFprop' : ∀ h : Set ℂ, ∃ a : ℂ, ∃ b : ℝ, h ∈ F →
      a ≠ 0 ∧ h = {x : ℂ | dot2 a x ≤ b} := by
    intro h
    by_cases hh : h ∈ F
    · obtain ⟨a, b, ha, hb⟩ := hFprop h hh
      exact ⟨a, b, fun _ => ⟨ha, hb⟩⟩
    · refine ⟨0, 0, fun hF0 => absurd hF0 hh⟩
  choose a b ha hb using hFprop'
  exact ⟨F, hF, hs, a, b, fun h hh => ⟨ha h hh, hb h hh⟩, hmin⟩

/-- HOL `FACET_OF_POLYHEDRON` ℂ 版 (Polytope:1753)：polyhedron 的每个 facet
由单个支撑半空间切出。 -/
theorem p22_facetOfCPolyhedron {P : Set ℂ} (hP : polyhedronC P) {c : Set ℂ}
    (hcf : facetOfC c P) :
    ∃ a : ℂ, ∃ b : ℝ, a ≠ 0 ∧ P ⊆ {x : ℂ | dot2 a x ≤ b} ∧
      c = P ∩ {x : ℂ | dot2 a x = b} := by
  obtain ⟨F, hF, hs, a, b, hFprop, hmin⟩ := p22_minrep_skolem hP
  obtain ⟨j, hjF, rfl⟩ := (facetOfCPolyhedronExplicit a b hF hs hFprop hmin c).1 hcf
  refine ⟨a j, b j, (hFprop j hjF).1, ?_, rfl⟩
  intro x hx
  rw [hs] at hx
  have h0 : x ∈ j := Set.mem_sInter.1 hx.2 j hjF
  rw [(hFprop j hjF).2] at h0
  exact h0

/-- HOL `eus1` (counting_spheres.hl:85): facets of a planar polyhedron have
supporting-hyperplane representations.  GIANT. -/
theorem eus1 (P c : Set ℂ) (hP : polyhedronC P) (hc : facetOfC c P) :
    ∃ a : ℂ, ∃ b : ℝ, ‖a‖ = 1 ∧
      (∀ r : ℝ, 0 < r → (∀ p : ℂ, ‖p‖ < r → p ∈ P) → r ≤ b) ∧
      P ⊆ {x : ℂ | dot2 a x ≤ b} ∧
      c = P ∩ {x : ℂ | dot2 a x = b} := by
  -- the supporting halfspace from the facet kit, rescaled to a unit normal
  obtain ⟨a₀, b₀, ha₀, hsub₀, heq₀⟩ := p22_facetOfCPolyhedron hP hc
  have ht : 0 < ‖a₀‖ := norm_pos_iff.mpr ha₀
  have htne : ‖a₀‖ ≠ 0 := ne_of_gt ht
  -- homogeneity of `dot2` in its *first* argument (via commutativity)
  have hsmull : ∀ (t : ℝ) (u w : ℂ), dot2 (t • u) w = t * dot2 u w := by
    intro t u w
    rw [dot2_comm (t • u) w, dot2_smul_right w u t, dot2_comm w u]
  -- the unit normal â := ‖a₀‖⁻¹ • a₀
  have hnormâ : ‖((‖a₀‖⁻¹ : ℝ) • a₀ : ℂ)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), inv_mul_cancel₀ htne]
  refine ⟨(‖a₀‖⁻¹ : ℝ) • a₀, b₀ / ‖a₀‖, hnormâ, ?_, ?_, ?_⟩
  · -- the ball pins the supporting value: r ≤ b₀ / ‖a₀‖
    intro r hr hball
    have h0in : (0 : ℂ) ∈ P := hball 0 (by simpa using hr)
    have hb₀nn : 0 ≤ b₀ := by
      have h0 := hsub₀ h0in
      rw [Set.mem_setOf_eq, dot2_expand] at h0
      simpa using h0
    -- every ball point pins the supporting value from below: s * ‖a₀‖ ≤ b₀
    have hpt : ∀ s : ℝ, 0 ≤ s → s < r → s * ‖a₀‖ ≤ b₀ := by
      intro s hsnn hslt
      have hnb : ‖(s • ((‖a₀‖⁻¹ : ℝ) • a₀) : ℂ)‖ < r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsnn, hnormâ, mul_one]
        exact hslt
      have hle := hsub₀ (hball _ hnb)
      rw [Set.mem_setOf_eq, smul_smul, dot2_smul_right, p22_dot2_self] at hle
      have hconv : (s * ‖a₀‖⁻¹) * ‖a₀‖ ^ 2 = s * ‖a₀‖ := by field_simp
      rw [hconv] at hle
      exact hle
    by_contra hcon
    push_neg at hcon
    have hbllt : b₀ < r * ‖a₀‖ := (div_lt_iff₀ ht).mp hcon
    have hb₀dnn : 0 ≤ b₀ / ‖a₀‖ := div_nonneg hb₀nn ht.le
    have hsnn : 0 ≤ (b₀ / ‖a₀‖ + r) / 2 := div_nonneg (by linarith) (by norm_num)
    have hmid : (b₀ / ‖a₀‖ + r) / 2 < r := by
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    have hle := hpt _ hsnn hmid
    have hgt : b₀ < (b₀ / ‖a₀‖ + r) / 2 * ‖a₀‖ := by
      have h2t : ((b₀ / ‖a₀‖ + r) / 2 * ‖a₀‖) * 2 = b₀ + r * ‖a₀‖ := by field_simp
      linarith
    linarith
  · -- the supporting halfspace, rescaled
    intro x hx
    have hle : dot2 a₀ x ≤ b₀ := hsub₀ hx
    rw [Set.mem_setOf_eq, dot2_comm, dot2_smul_right, dot2_comm, le_div_iff₀ ht,
      mul_assoc, mul_comm (dot2 a₀ x) ‖a₀‖, ← mul_assoc, inv_mul_cancel₀ htne,
      one_mul]
    exact hle
  · -- the facet is exactly the slice of the rescaled hyperplane
    rw [heq₀]
    ext x
    refine ⟨fun hx' => ?_, fun hx' => ?_⟩
    · obtain ⟨hxP, hxe⟩ := hx'
      rw [Set.mem_setOf_eq] at hxe
      refine ⟨hxP, ?_⟩
      rw [Set.mem_setOf_eq, hsmull, hxe]
      ring
    · obtain ⟨hxP, hxe⟩ := hx'
      rw [Set.mem_setOf_eq, hsmull] at hxe
      refine ⟨hxP, ?_⟩
      rw [Set.mem_setOf_eq]
      have h2 := congrArg (fun v : ℝ => v * ‖a₀‖) hxe
      field_simp at h2
      exact h2

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

/-- HOL `facet_rep_uniq_c` (counting_spheres.hl:200). Filled from
`facet_rep_uniq` applied at the common normal direction. -/
theorem facet_rep_uniq_c (P c1 c2 : Set ℂ) (hP : polyhedronC P)
    (h1 : facetOfC c1 P) (h2 : facetOfC c2 P)
    (h : facet_rep_a P c1 = facet_rep_a P c2) : c1 = c2 := by
  have s1 : P ⊆ {x : ℂ | dot2 (facet_rep_a P c1) x ≤ facet_rep_b P c1} :=
    (facet_rep_props P c1 hP h1).2.2.1
  have e1 : c1 = P ∩ {x : ℂ | dot2 (facet_rep_a P c1) x = facet_rep_b P c1} :=
    (facet_rep_props P c1 hP h1).2.2.2
  have s2 : P ⊆ {x : ℂ | dot2 (facet_rep_a P c1) x ≤ facet_rep_b P c2} := by
    have hs := (facet_rep_props P c2 hP h2).2.2.1
    rw [← h] at hs
    exact hs
  have e2 : c2 = P ∩ {x : ℂ | dot2 (facet_rep_a P c1) x = facet_rep_b P c2} := by
    have he := (facet_rep_props P c2 hP h2).2.2.2
    rw [← h] at he
    exact he
  exact (facet_rep_uniq P c1 c2 (facet_rep_a P c1) (facet_rep_b P c1)
    (facet_rep_b P c2) hP h1 h2 s1 s2 e1 e2).2

/-- HOL `facet_rep_in_facet` (counting_spheres.hl:227). GIANT. -/
theorem facet_rep_in_facet (P c1 c2 : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (h1 : facetOfC c1 P) (h2 : facetOfC c2 P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h : facet_rep_b P c1 ≤ dot2 (facet_rep_a P c1) (r • facet_rep_a P c2)) :
    c1 = c2 := by
  have hpr1 := facet_rep_props P c1 hP h1
  have hpr2 := facet_rep_props P c2 hP h2
  have hn1 : ‖facet_rep_a P c1‖ = 1 := hpr1.1
  have hn2 : ‖facet_rep_a P c2‖ = 1 := hpr2.1
  -- every ball point pins the supporting value from below: r ≤ facet_rep_b P c1
  have hpt : ∀ t : ℝ, 0 ≤ t → t < r → t ≤ facet_rep_b P c1 := by
    intro t htnn htlt
    have hnb : ‖(t • facet_rep_a P c1 : ℂ)‖ < r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htnn, hn1]
      simpa using htlt
    have hle : dot2 (facet_rep_a P c1) (t • facet_rep_a P c1) ≤ facet_rep_b P c1 :=
      hpr1.2.2.1 (hrad _ hnb)
    rw [p22_dot2_smul_right, p22_dot2_self, hn1] at hle
    simpa using hle
  have hrb : r ≤ facet_rep_b P c1 := by
    by_contra hcon
    have hblt : facet_rep_b P c1 < r := lt_of_not_ge hcon
    rcases lt_or_ge (facet_rep_b P c1) 0 with hneg | hpos
    · have h0 := hpt 0 (by norm_num) hr
      linarith
    · have ht := hpt ((facet_rep_b P c1 + r) / 2) (by linarith) (by linarith)
      linarith
  -- the hypothesis plus Cauchy–Schwarz forces the inner product to be 1
  rw [p22_dot2_smul_right] at h
  have hcs0 : dot2 (facet_rep_a P c1) (facet_rep_a P c2)
      ≤ ‖facet_rep_a P c1‖ * ‖facet_rep_a P c2‖ :=
    p22_dot2_cauchy _ _
  rw [hn1, hn2, mul_one] at hcs0
  have h1cd : (1 : ℝ) ≤ dot2 (facet_rep_a P c1) (facet_rep_a P c2) := by
    have hmul : r * 1 ≤ r * dot2 (facet_rep_a P c1) (facet_rep_a P c2) := by
      rw [mul_one]; exact hrb.trans h
    exact le_of_mul_le_mul_left hmul hr
  have haeq : facet_rep_a P c1 = facet_rep_a P c2 :=
    norm1_cauchy_eq _ _ hn1 hn2 (le_antisymm hcs0 h1cd)
  exact facet_rep_uniq_c P c1 c2 hP h1 h2 haeq

/-- HOL `facet_rep_refl` (counting_spheres.hl:257). Filled: ball points pin the
supporting value from below (`r ≤ facet_rep_b P c`), and `dot2 â (r • â) = r`. -/
theorem facet_rep_refl (P c : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (hc : facetOfC c P) (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) :
    dot2 (facet_rep_a P c) (r • facet_rep_a P c) ≤ facet_rep_b P c := by
  have hpr := facet_rep_props P c hP hc
  have hn1 : ‖facet_rep_a P c‖ = 1 := hpr.1
  -- every ball point pins the supporting value from below
  have hpt : ∀ t : ℝ, 0 ≤ t → t < r → t ≤ facet_rep_b P c := by
    intro t htnn htlt
    have hnb : ‖(t • facet_rep_a P c : ℂ)‖ < r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htnn, hn1]
      simpa using htlt
    have hle : dot2 (facet_rep_a P c) (t • facet_rep_a P c) ≤ facet_rep_b P c :=
      hpr.2.2.1 (hrad _ hnb)
    rw [p22_dot2_smul_right, p22_dot2_self, hn1] at hle
    simpa using hle
  have hrb : r ≤ facet_rep_b P c := by
    by_contra hcon
    have hblt : facet_rep_b P c < r := lt_of_not_ge hcon
    rcases lt_or_ge (facet_rep_b P c) 0 with hneg | hpos
    · have h0 := hpt 0 (by norm_num) hr
      linarith
    · have ht := hpt ((facet_rep_b P c + r) / 2) (by linarith) (by linarith)
      linarith
  rw [p22_dot2_smul_right, p22_dot2_self, hn1]
  simpa using hrb

/-- HOL `POLYHEDRON_MEMBER` (counting_spheres.hl:346). Filled (EXPLICIT kit
wave): the ball makes `P` full-dimensional; the minimal representation then
satisfies `P = ⋂₀ F`; per constraint the slice is a `facetOfC`
(`facetOfCPolyhedronExplicit`), whose two hyperplane descriptions
(`affine_facet_hyper` twice) transfer the hypothesis via `DOT_EQ_IMP_INEQ`. -/
theorem POLYHEDRON_MEMBER (P : Set ℂ) (r : ℝ) (x : ℂ) (hP : polyhedronC P)
    (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h : ∀ c : Set ℂ, facetOfC c P → dot2 (facet_rep_a P c) x ≤ facet_rep_b P c) :
    x ∈ P := by
  classical
  -- the ball around 0 makes the polyhedron full-dimensional
  have haff := CONTAINS_BALL_AFFINE_HULL_C (s := P) (x := (0 : ℂ)) (r := r) hr
    (fun p hp => hrad p (by simpa [dist_zero_right] using hp))
  obtain ⟨F, hFfin, hs, a, b, hFprop, hmin⟩ := p22_minrep_skolem hP
  have hs' : P = ⋂₀ F := by rw [hs, haff, Set.univ_inter]
  rw [hs']
  refine Set.mem_sInter.2 fun h₀ h₀F => ?_
  obtain ⟨ha₀, h₀eq⟩ := hFprop h₀ h₀F
  -- the hyperplane slice of constraint h₀ is a facet (EXPLICIT kit)
  set c₀ : Set ℂ := P ∩ {y : ℂ | dot2 (a h₀) y = b h₀} with hc₀def
  have hc₀fac : facetOfC c₀ P :=
    (facetOfCPolyhedronExplicit a b hFfin hs hFprop hmin c₀).2 ⟨h₀, h₀F, hc₀def.symm⟩
  obtain ⟨hn1, hbball, hsub, hceq⟩ := facet_rep_props P c₀ hP hc₀fac
  have hbpos : 0 < facet_rep_b P c₀ :=
    lt_of_lt_of_le hr (hbball r hr hrad)
  have hanz : facet_rep_a P c₀ ≠ 0 := by
    intro h0
    rw [h0] at hn1
    exact absurd hn1 (by simp)
  -- both hyperplanes are the affine hull of the slice
  have hA1 : (affineSpan ℝ c₀ : Set ℂ) = {y : ℂ | dot2 (a h₀) y = b h₀} :=
    affine_facet_hyper P c₀ (a h₀) (b h₀) hc₀fac hP haff ha₀ hc₀def.symm
  have hA2 : (affineSpan ℝ c₀ : Set ℂ)
      = {y : ℂ | dot2 (facet_rep_a P c₀) y = facet_rep_b P c₀} :=
    affine_facet_hyper P c₀ (facet_rep_a P c₀) (facet_rep_b P c₀) hc₀fac hP haff
      hanz hceq.symm
  -- hence the two hyperplanes coincide as point sets
  have hiff : ∀ y : ℂ, dot2 (a h₀) y = b h₀ ↔
      dot2 (facet_rep_a P c₀) y = facet_rep_b P c₀ := by
    intro y
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · have m1 : y ∈ (affineSpan ℝ c₀ : Set ℂ) := by
        rw [hA1]
        exact Set.mem_setOf.2 hm
      have m2 : y ∈ {y : ℂ | dot2 (facet_rep_a P c₀) y = facet_rep_b P c₀} := by
        rw [← hA2]
        exact m1
      exact Set.mem_setOf.1 m2
    · have m1 : y ∈ (affineSpan ℝ c₀ : Set ℂ) := by
        rw [hA2]
        exact Set.mem_setOf.2 hm
      have m2 : y ∈ {y : ℂ | dot2 (a h₀) y = b h₀} := by
        rw [← hA1]
        exact m1
      exact Set.mem_setOf.1 m2
  -- `0 ∈ P` pins `b h₀` from below
  have h0P : (0 : ℂ) ∈ P := hrad 0 (by simpa using hr)
  have h0in : (0 : ℂ) ∈ h₀ := by
    have h0P' : (0 : ℂ) ∈ ⋂₀ F := by rw [← hs']; exact h0P
    exact Set.mem_sInter.1 h0P' h₀ h₀F
  have hb₀ : 0 ≤ b h₀ := by
    have h0m : dot2 (a h₀) (0 : ℂ) ≤ b h₀ := by
      have hk := h0in
      rw [h₀eq, Set.mem_setOf_eq] at hk
      exact hk
    have h00 : dot2 (a h₀) (0 : ℂ) = 0 := by rw [dot2_expand]; norm_num
    rw [h00] at h0m
    exact h0m
  have hfin := DOT_EQ_IMP_INEQ (a h₀) (facet_rep_a P c₀) (b h₀)
    (facet_rep_b P c₀) hiff hb₀ hbpos
  show x ∈ h₀
  rw [h₀eq, Set.mem_setOf_eq]
  exact (hfin x).mpr (h c₀ hc₀fac)

/-- HOL `facet_rep_in_poly` (counting_spheres.hl:435). Filled (EXPLICIT kit
wave): `POLYHEDRON_MEMBER` + `facet_rep_refl` (`c' = c` arm) +
`facet_rep_in_facet` (`c' ≠ c` arm). -/
theorem facet_rep_in_poly (P c : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (hc : facetOfC c P) (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) :
    (r • facet_rep_a P c : ℂ) ∈ P := by
  refine POLYHEDRON_MEMBER P r (r • facet_rep_a P c) hP hr hrad fun c' hc' => ?_
  by_cases heq : c' = c
  · rw [heq]
    exact facet_rep_refl P c r hP hc hr hrad
  · by_contra hcon
    push_neg at hcon
    exact heq (facet_rep_in_facet P c' c r hP hc' hc hr hrad (le_of_lt hcon))

/-- HOL `facet_arg_lt_pi` (counting_spheres.hl:453). Filled (EXPLICIT kit wave):
by contradiction, `p := (A+1) • (I * facet_rep_a P c)` lies in `P` by
`POLYHEDRON_MEMBER` — every facet normal satisfies `Im (â'/â) ≤ 0` under the
negated goal — yet `‖p‖ = A+1` exceeds the boundedness radius `A`. -/
theorem facet_arg_lt_pi (P c : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (hb : Bornology.IsBounded P) (hc : facetOfC c P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) :
    ∃ c' : Set ℂ, facetOfC c' P ∧
      0 < Complex.arg (facet_rep_a P c' / facet_rep_a P c) ∧
      Complex.arg (facet_rep_a P c' / facet_rep_a P c) < Real.pi := by
  classical
  -- the boundedness radius
  obtain ⟨A, hA⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
  have hAle : ∀ x ∈ P, ‖x‖ ≤ A := by
    intro x hx
    have h1 := hA hx
    rwa [Metric.mem_closedBall, dist_zero_right] at h1
  -- the reference facet normal
  have hpr := facet_rep_props P c hP hc
  have hn1 : ‖facet_rep_a P c‖ = 1 := hpr.1
  have hac : facet_rep_a P c ≠ 0 := by
    intro h0
    rw [h0] at hn1
    exact absurd hn1 (by simp)
  by_contra hcon
  have h0P : (0 : ℂ) ∈ P := hrad 0 (by simpa using hr)
  have hAnonneg : 0 ≤ A := le_trans (norm_nonneg 0) (hAle 0 h0P)
  set p : ℂ := (A + 1) • (Complex.I * facet_rep_a P c) with hpdef
  have hpnorm : ‖p‖ = A + 1 := by
    rw [hpdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < A + 1),
      norm_mul, Complex.norm_I, hn1]
    norm_num
  -- `p ∈ P` via POLYHEDRON_MEMBER
  have hpP : p ∈ P := by
    refine POLYHEDRON_MEMBER P r p hP hr hrad fun c' hc' => ?_
    have hpr' := facet_rep_props P c' hP hc'
    have hb'pos : 0 < facet_rep_b P c' := lt_of_lt_of_le hr (hpr'.2.1 r hr hrad)
    -- `Im (â'/â) ≤ 0` from the negated goal
    have him : (facet_rep_a P c' / facet_rep_a P c).im ≤ 0 := by
      by_contra himpos
      push_neg at himpos
      have hzne : facet_rep_a P c' / facet_rep_a P c ≠ 0 := by
        have hac' : facet_rep_a P c' ≠ 0 := by
          intro h0
          rw [h0] at hpr'
          exact absurd hpr'.1 (by simp)
        exact div_ne_zero hac' hac
      have hargpos : 0 < Complex.arg (facet_rep_a P c' / facet_rep_a P c) := by
        have h1 : 0 ≤ Complex.arg (facet_rep_a P c' / facet_rep_a P c) :=
          Complex.arg_nonneg_iff.2 (le_of_lt himpos)
        have h2 : Complex.arg (facet_rep_a P c' / facet_rep_a P c) ≠ 0 := by
          intro h0
          have hzig := (Complex.arg_eq_zero_iff.1 h0).2
          exact absurd hzig (ne_of_gt himpos)
        exact lt_of_le_of_ne h1 (Ne.symm h2)
      have harglt : Complex.arg (facet_rep_a P c' / facet_rep_a P c) < Real.pi :=
        (Complex.arg_lt_pi_iff).2 (Or.inr (ne_of_gt himpos))
      exact hcon ⟨c', hc', hargpos, harglt⟩
    -- `dot2 â' p = (A+1) * Im (â'/â)`
    have hkey : dot2 (facet_rep_a P c') p
        = (A + 1) * (facet_rep_a P c' / facet_rep_a P c).im := by
      have hsq : Complex.normSq (facet_rep_a P c) = 1 := by
        rw [← Complex.sq_norm, hn1]
        norm_num
      rw [hpdef, p22_dot2_smul_right, dot2_expand, Complex.I_mul_re, Complex.I_mul_im,
        div_eq_inv_mul, Complex.mul_im, Complex.inv_re,
        Complex.inv_im, hsq]
      field_simp
      ring
    have hkey' : dot2 (facet_rep_a P c') p ≤ 0 := by
      rw [hkey]
      exact mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ A + 1 by linarith) him
    exact le_trans hkey' (le_of_lt hb'pos)
  -- contradiction with the boundedness radius
  have hfinal : ‖p‖ ≤ A := hAle p hpP
  rw [hpnorm] at hfinal
  linarith

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
lies in the polyhedron. GIANT.
SF27 statement-fix (minesweep report §3): the three `Complex.arg` hypotheses
are lifted to `holArg` (range `[0, 2π)`, the faithful HOL `Arg`).  Over the
principal range `(-π, π]` the `h5` antecedent
`Complex.arg (â'' / â) < 2 * psi` is met by every lower-half-plane facet, so
`h5` no longer says "c is the nearest facet in cyclic order" and the HOL
proof (insert_v, counting_spheres.hl:529) cannot be ported; the statement was
frozen, so it is restated over `holArg`. -/
theorem insert_v (P c c' : Set ℂ) (r : ℝ) (v : ℂ) (psi : ℝ)
    (hP : polyhedronC P) (hc : facetOfC c P) (hc' : facetOfC c' P)
    (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h1 : holArg (v / facet_rep_a P c) = psi) (h2 : 0 < psi)
    (h3 : psi < Real.pi / 2)
    (h4 : holArg (facet_rep_a P c' / facet_rep_a P c) = 2 * psi)
    (h5 : ∀ c'' : Set ℂ, facetOfC c'' P →
      holArg (facet_rep_a P c'' / facet_rep_a P c) < 2 * psi → c'' = c)
    (h6 : ‖v‖ = r / Real.cos psi) : v ∈ P := by
  sorry -- DEF-FIX: refill per counting_spheres.hl:529 §3a

/-- HOL `facet_rep_a_uniq` (counting_spheres.hl:640). Filled: the positive-real
multiple hypothesis forces `‖facet_rep_a P c1‖ = s` and `s = 1`, so the normal
directions coincide and `facet_rep_uniq_c` identifies the facets. -/
theorem facet_rep_a_uniq (P c1 c2 : Set ℂ) (r : ℝ) (hP : polyhedronC P)
    (h1 : facetOfC c1 P) (h2 : facetOfC c2 P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h : ∃ s : ℝ, 0 < s ∧ facet_rep_a P c1 = s • facet_rep_a P c2) :
    c1 = c2 := by
  obtain ⟨s, hs0, hseq⟩ := h
  have hn1 : ‖facet_rep_a P c1‖ = 1 := (facet_rep_props P c1 hP h1).1
  have hn2 : ‖facet_rep_a P c2‖ = 1 := (facet_rep_props P c2 hP h2).1
  have hns : ‖facet_rep_a P c1‖ = s := by
    rw [hseq, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hn2, mul_one]
  have hs1 : s = 1 := by rw [← hns, hn1]
  rw [hs1, one_smul] at hseq
  exact facet_rep_uniq_c P c1 c2 hP h1 h2 hseq

/-- HOL `poly_sort_fn` (counting_spheres.hl:678, the chapter's single
`new_definition`).
SF27 statement-fix (minesweep report §3): the comparison is lifted from
`Complex.arg` (range `(-π, π]`) to `holArg` (range `[0, 2π)`, the faithful
HOL `Arg`) — the principal-value order is not the cyclic order (it sorts the
lower half plane after the upper one), so the HOL sorted-facet predicate is
not expressible over `Complex.arg`.  Proven consumers re-ported accordingly:
`poly_sort_antisym` (holArg hop via `p22_holArg_eq_iff`), `poly_sort_trans`
(no change, `le_trans` is generic), `POLY_SORT_LEMMA` (sort key lifted to
`holArg`), `POLY_SORT`/`POLY_SORT_BIJ` (Complex.arg-ordered; re-derived via
`p22_facet_arg_injOn`). -/
def poly_sort_fn (P : Set ℂ) (u : ℂ) (c1 c2 : Set ℂ) : Prop :=
  facetOfC c1 P ∧ facetOfC c2 P ∧
    holArg (facet_rep_a P c1 / u) ≤ holArg (facet_rep_a P c2 / u)

/-- HOL `poly_sort_antisym` (counting_spheres.hl:682). Filled: the two
`poly_sort_fn` hypotheses give equal arguments; `Complex.arg_eq_arg_iff` makes
the normals positive-real multiples and `facet_rep_a_uniq` concludes.
SF27 linkage: equal `holArg`s are converted to equal `Complex.arg`s by
`p22_holArg_eq_iff`; the rest of the proof is unchanged. -/
theorem poly_sort_antisym (P : Set ℂ) (u : ℂ) (c1 c2 : Set ℂ) (r : ℝ)
    (hP : polyhedronC P) (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (h12 : poly_sort_fn P u c1 c2) (h21 : poly_sort_fn P u c2 c1) (hu : u ≠ 0) :
    c1 = c2 := by
  have harg : Complex.arg (facet_rep_a P c1 / u) = Complex.arg (facet_rep_a P c2 / u) :=
    (p22_holArg_eq_iff _ _).mp (le_antisymm h12.2.2 h21.2.2)
  have ha1 : facet_rep_a P c1 ≠ 0 := by
    intro h0
    have h1 : ‖facet_rep_a P c1‖ = 1 := (facet_rep_props P c1 hP h12.1).1
    rw [h0] at h1
    exact absurd h1 (by simp)
  have ha2 : facet_rep_a P c2 ≠ 0 := by
    intro h0
    have h1 : ‖facet_rep_a P c2‖ = 1 := (facet_rep_props P c2 hP h21.1).1
    rw [h0] at h1
    exact absurd h1 (by simp)
  have hd1 : facet_rep_a P c1 / u ≠ 0 := div_ne_zero ha1 hu
  have hd2 : facet_rep_a P c2 / u ≠ 0 := div_ne_zero ha2 hu
  -- equal arguments ⟹ positive-real multiple of each other
  have hkey : ((‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ : ℝ) : ℂ)
        * (facet_rep_a P c1 / u) = facet_rep_a P c2 / u := by
      exact_mod_cast (Complex.arg_eq_arg_iff hd1 hd2).mp harg
  have hpos : 0 < ‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ :=
    div_pos (norm_pos_iff.mpr hd2) (norm_pos_iff.mpr hd1)
  -- cancel `/ u`
  have hcancel : ((‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ : ℝ) : ℂ)
      * facet_rep_a P c1 = facet_rep_a P c2 := by
    calc ((‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ : ℝ) : ℂ)
        * facet_rep_a P c1 = ((‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ : ℝ) : ℂ)
            * (facet_rep_a P c1 / u) * u := by
          rw [mul_assoc, div_mul_cancel₀ _ hu]
      _ = (facet_rep_a P c2 / u) * u := by rw [hkey]
      _ = facet_rep_a P c2 := by
          rw [div_mul_cancel₀ _ hu]
  refine facet_rep_a_uniq P c1 c2 r hP h12.1 h21.1 hr hrad
    ⟨(‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖)⁻¹, inv_pos.mpr hpos, ?_⟩
  have htne : ((‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast ne_of_gt hpos
  rw [Complex.real_smul, Complex.ofReal_inv, eq_inv_mul_iff_mul_eq₀ htne]
  exact hcancel

/-- HOL `poly_sort_trans` (counting_spheres.hl:715). GIANT. -/
theorem poly_sort_trans (P : Set ℂ) (u : ℂ) (c1 c2 c3 : Set ℂ) (r : ℝ)
    (hP : polyhedronC P) (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (hu : u ≠ 0) (h12 : poly_sort_fn P u c1 c2) (h23 : poly_sort_fn P u c2 c3) :
    poly_sort_fn P u c1 c3 := ⟨h12.1, h23.2.1, le_trans h12.2.2 h23.2.2⟩

/-- SF22/SF27 linkage kit: the principal-argument map is still injective on
the facet set of a polyhedron (equal `Complex.arg`s make the facet normals
positive-real multiples by `Complex.arg_eq_arg_iff`; both are unit vectors,
so the multiplier is 1; then `facet_rep_uniq_c`).  Extracted from the
pre-SF27 `POLY_SORT_LEMMA` proof so the `Complex.arg`-ordered `POLY_SORT`/
`POLY_SORT_BIJ` keep standing proofs beside the `holArg`-cyclic
`poly_sort_fn` kit. -/
private theorem p22_facet_arg_injOn (P : Set ℂ) (u : ℂ) (s : Set (Set ℂ))
    (hs : s = {c : Set ℂ | facetOfC c P}) (hP : polyhedronC P) (hu : u ≠ 0) :
    Set.InjOn (fun c : Set ℂ => Complex.arg (facet_rep_a P c / u)) s := by
  intro c1 hc1 c2 hc2 harg
  have hf1 : facetOfC c1 P := by
    have h1 : c1 ∈ s := hc1
    rw [hs] at h1
    exact h1
  have hf2 : facetOfC c2 P := by
    have h1 : c2 ∈ s := hc2
    rw [hs] at h1
    exact h1
  have hn1 : ‖facet_rep_a P c1‖ = 1 := (facet_rep_props P c1 hP hf1).1
  have hn2 : ‖facet_rep_a P c2‖ = 1 := (facet_rep_props P c2 hP hf2).1
  have ha1 : facet_rep_a P c1 ≠ 0 := by
    intro h0
    rw [h0] at hn1
    exact absurd hn1 (by simp)
  have ha2 : facet_rep_a P c2 ≠ 0 := by
    intro h0
    rw [h0] at hn2
    exact absurd hn2 (by simp)
  have hd1 : facet_rep_a P c1 / u ≠ 0 := div_ne_zero ha1 hu
  have hd2 : facet_rep_a P c2 / u ≠ 0 := div_ne_zero ha2 hu
  have hkey : ((‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ : ℝ) : ℂ)
      * (facet_rep_a P c1 / u) = facet_rep_a P c2 / u := by
    exact_mod_cast (Complex.arg_eq_arg_iff hd1 hd2).mp harg
  have hcancel : ((‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ : ℝ) : ℂ)
      * facet_rep_a P c1 = facet_rep_a P c2 := by
    calc ((‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ : ℝ) : ℂ)
        * facet_rep_a P c1 = ((‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ : ℝ) : ℂ)
            * (facet_rep_a P c1 / u) * u := by
          rw [mul_assoc, div_mul_cancel₀ _ hu]
      _ = (facet_rep_a P c2 / u) * u := by rw [hkey]
      _ = facet_rep_a P c2 := by
          rw [div_mul_cancel₀ _ hu]
  set k : ℝ := ‖facet_rep_a P c2 / u‖ / ‖facet_rep_a P c1 / u‖ with hkdef
  have hkpos : 0 < k := div_pos (norm_pos_iff.mpr hd2) (norm_pos_iff.mpr hd1)
  -- unit norms force the positive multiplier to be 1
  have hnorm : ‖facet_rep_a P c2‖ = ‖((k : ℝ) : ℂ)‖ * ‖facet_rep_a P c1‖ := by
    rw [← hcancel, norm_mul]
  rw [hn2, hn1, mul_one, Complex.norm_real, Real.norm_eq_abs] at hnorm
  have hk : k = 1 := by
    rw [← abs_of_pos hkpos]
    exact hnorm.symm
  rw [hk, Complex.ofReal_one, one_mul] at hcancel
  exact facet_rep_uniq_c P c1 c2 hP hf1 hf2 hcancel

/-! ## TOPOLOGICAL_SORT ℂ 版：有限集上单射实值函数的严格递增枚举 -/

/-- HOL `TOPOLOGICAL_SORT` 直译（counting_spheres.hl 的 `poly_sort` 族共用）：
有限集上的单射实值函数可排成严格递增枚举。 -/
private theorem p22_enum_sorted {α : Type*} [Nonempty α] {g : α → ℝ} {s : Set α}
    {n : ℕ} (hs : s.Finite) (hcard : s.ncard = n)
    (hinj : Set.InjOn g s) :
    ∃ f : ℕ → α, s = f '' Set.Icc 1 n ∧
      ∀ j k : ℕ, j ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → j < k → g (f j) < g (f k) := by
  classical
  haveI : Finite ↥s := hs
  haveI : Fintype ↥s := Fintype.ofFinite _
  set t : Finset ↥s := Finset.univ with htdef
  set vals : Finset ℝ := t.image (fun c : ↥s => g c) with hvdef
  have hvcard : vals.card = n := by
    rw [hvdef, htdef, Finset.card_image_of_injOn]
    · rw [Finset.card_univ, Set.fintypeCard_eq_ncard]
      exact hcard
    · intro a ha b hab habc
      exact Subtype.ext (hinj a.prop b.prop habc)
  set e := vals.orderIsoOfFin hvcard with hedef
  have hidx : ∀ k : ℕ, 1 ≤ k → k ≤ n → k - 1 < n := by
    intro k hk1 hkn
    omega
  set w : ℕ → ℝ := fun k =>
    if h : 1 ≤ k ∧ k ≤ n then ((e ⟨k - 1, hidx k h.1 h.2⟩ : ↥vals) : ℝ) else 0 with hwdef
  set f : ℕ → α := fun k =>
    if h : ∃ c ∈ s, g c = w k then Classical.choose h else Classical.arbitrary α with hfdef
  have hwval : ∀ k : ℕ, 1 ≤ k → k ≤ n → w k ∈ (vals : Set ℝ) := by
    intro k hk1 hkn
    simp only [hwdef]
    rw [dif_pos ⟨hk1, hkn⟩]
    exact (e ⟨k - 1, hidx k hk1 hkn⟩).2
  have hwlt : ∀ j k : ℕ, 1 ≤ j → j < k → k ≤ n → w j < w k := by
    intro j k hj1 hjk hkn
    simp only [hwdef]
    rw [dif_pos ⟨hj1, le_trans (le_of_lt hjk) hkn⟩, dif_pos ⟨hj1.trans (le_of_lt hjk), hkn⟩]
    have hilt : (⟨j - 1, hidx j hj1 (le_trans (le_of_lt hjk) hkn)⟩ : Fin n)
        < (⟨k - 1, hidx k (hj1.trans (le_of_lt hjk)) hkn⟩ : Fin n) := by
      have hidxj : ((⟨j - 1, hidx j hj1 (le_trans (le_of_lt hjk) hkn)⟩ : Fin n) : ℕ) = j - 1 := rfl
      have hidxk : ((⟨k - 1, hidx k (hj1.trans (le_of_lt hjk)) hkn⟩ : Fin n) : ℕ) = k - 1 := rfl
      rw [Fin.lt_def, hidxj, hidxk]
      exact Nat.sub_lt_sub_right hj1 hjk
    have hle : ((e ⟨j - 1, hidx j hj1 (le_trans (le_of_lt hjk) hkn)⟩ : ↥vals) : ℝ)
        ≤ ((e ⟨k - 1, hidx k (hj1.trans (le_of_lt hjk)) hkn⟩ : ↥vals) : ℝ) := by
      rw [Subtype.coe_le_coe]
      exact e.map_rel_iff.2 hilt.le
    have hne : ((e ⟨j - 1, hidx j hj1 (le_trans (le_of_lt hjk) hkn)⟩ : ↥vals) : ℝ)
        ≠ ((e ⟨k - 1, hidx k (hj1.trans (le_of_lt hjk)) hkn⟩ : ↥vals) : ℝ) := by
      intro hcc
      have hfe : (⟨j - 1, hidx j hj1 (le_trans (le_of_lt hjk) hkn)⟩ : Fin n)
          = (⟨k - 1, hidx k (hj1.trans (le_of_lt hjk)) hkn⟩ : Fin n) :=
        e.injective (Subtype.coe_injective hcc)
      have hveq : j - 1 = k - 1 := congrArg Fin.val hfe
      have hlt2 : j - 1 < k - 1 := Nat.sub_lt_sub_right hj1 hjk
      rw [hveq] at hlt2
      exact lt_irrefl _ hlt2
    exact lt_of_le_of_ne hle hne
  have hfval : ∀ k : ℕ, 1 ≤ k → k ≤ n → g (f k) = w k ∧ f k ∈ s := by
    intro k hk1 hkn
    have hwmem := hwval k hk1 hkn
    have hv : w k ∈ g '' s := by
      rw [hvdef, htdef, SetLike.mem_coe, Finset.mem_image] at hwmem
      obtain ⟨a, -, hga⟩ := hwmem
      exact ⟨a, a.prop, hga⟩
    obtain ⟨c, hcs, hgc⟩ := hv
    have hex : ∃ c ∈ s, g c = w k := ⟨c, hcs, hgc⟩
    simp only [hfdef]
    rw [dif_pos hex]
    exact ⟨(Classical.choose_spec hex).2, (Classical.choose_spec hex).1⟩
  refine ⟨f, ?_, ?_⟩
  · refine Set.ext fun c => ?_
    constructor
    · intro hcs
      have hgmem : g c ∈ (vals : Set ℝ) := by
        rw [hvdef, htdef, SetLike.mem_coe, Finset.mem_image]
        exact ⟨⟨c, hcs⟩, Finset.mem_univ _, rfl⟩
      set i := e.symm ⟨g c, hgmem⟩ with hidef
      have hil : i.val < n := i.isLt
      have heq : ((e i : ↥vals) : ℝ) = g c := by
        rw [hidef]
        exact congrArg Subtype.val (OrderIso.apply_symm_apply e ⟨g c, hgmem⟩)
      have hwval1 : w (i.val + 1) = g c := by
        simp only [hwdef]
        rw [dif_pos (by omega : 1 ≤ i.val + 1 ∧ i.val + 1 ≤ n)]
        have hfin : (⟨i.val + 1 - 1, hidx (i.val + 1) (by omega) (by omega)⟩ : Fin n) = i := by
          refine Fin.ext ?_
          show i.val + 1 - 1 = i.val
          omega
        rw [hfin]
        exact heq
      have hfval1 : g (f (i.val + 1)) = g c := by
        have hv1 := hfval (i.val + 1) (by omega) (by omega)
        rw [hv1.1]
        exact hwval1
      refine ⟨i.val + 1, ⟨by omega, by omega⟩, ?_⟩
      have hex : ∃ c' ∈ s, g c' = w (i.val + 1) := ⟨c, hcs, hwval1.symm⟩
      simp only [hfdef]
      rw [dif_pos hex]
      have hfeq : g (Classical.choose hex) = g c := by
        rw [(Classical.choose_spec hex).2]
        exact hwval1
      exact hinj (Classical.choose_spec hex).1 hcs hfeq
    · rintro ⟨k, hk, rfl⟩
      exact (hfval k hk.1 hk.2).2
  · intro j k hj hk hjk
    rw [(hfval j hj.1 hj.2).1, (hfval k hk.1 hk.2).1]
    exact hwlt j k hj.1 hjk hk.2

/-- HOL `POLY_SORT_LEMMA` (counting_spheres.hl:729). Filled (EXPLICIT kit
wave): the argument map is injective on the facet set (`poly_sort_antisym`);
`p22_enum_sorted` (TOPOLOGICAL_SORT) produces the increasing enumeration.
SF27 linkage: with `poly_sort_fn` stated over `holArg` the enumeration is
built over the `holArg` map (injective on facets by `poly_sort_antisym`), so
the conclusion is the holArg-cyclic order statement. -/
theorem POLY_SORT_LEMMA (P : Set ℂ) (n : ℕ) (s : Set (Set ℂ)) (r : ℝ) (u : ℂ)
    (hs : s = {c : Set ℂ | facetOfC c P}) (hP : polyhedronC P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) (hu : u ≠ 0)
    (hsize : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → Set ℂ, s = f '' Set.Icc 1 n ∧ ∀ j k : ℕ, j ∈ Set.Icc 1 n →
      k ∈ Set.Icc 1 n → j < k → ¬ poly_sort_fn P u (f k) (f j) := by
  have hinj : Set.InjOn (fun c : Set ℂ => holArg (facet_rep_a P c / u)) s := by
    intro c1 hc1 c2 hc2 harg
    have hf1 : facetOfC c1 P := by
      have h1 : c1 ∈ s := hc1
      rw [hs] at h1
      exact h1
    have hf2 : facetOfC c2 P := by
      have h1 : c2 ∈ s := hc2
      rw [hs] at h1
      exact h1
    exact poly_sort_antisym P u c1 c2 r hP hr hrad
      ⟨hf1, hf2, le_of_eq harg⟩ ⟨hf2, hf1, le_of_eq harg.symm⟩ hu
  obtain ⟨f, hfim, hfmono⟩ := p22_enum_sorted (α := Set ℂ) hsize.1 hsize.2 hinj
  refine ⟨f, hfim, ?_⟩
  intro j k hj hk hjk hcon
  exact absurd hcon.2.2 (not_le.2 (hfmono j k hj hk hjk))

/-- HOL `POLY_SORT` (counting_spheres.hl:746). Filled (EXPLICIT kit wave).
SF27 linkage: `poly_sort_fn` is now stated over `holArg` (the `[0, 2π)`
cyclic order), which orders facets differently from the principal-value
`Complex.arg` order of THIS conclusion, so `POLY_SORT_LEMMA` (holArg twin)
can no longer feed it; instead the enumeration is built directly over the
`Complex.arg` map, injective on facets by `p22_facet_arg_injOn`. -/
theorem POLY_SORT (P : Set ℂ) (n : ℕ) (s : Set (Set ℂ)) (r : ℝ) (u : ℂ)
    (hs : s = {c : Set ℂ | facetOfC c P}) (hP : polyhedronC P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) (hu : u ≠ 0)
    (hsize : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → Set ℂ, s = f '' Set.Icc 1 n ∧ ∀ j k : ℕ, j ∈ Set.Icc 1 n →
      k ∈ Set.Icc 1 n → j < k →
      Complex.arg (facet_rep_a P (f j) / u) <
        Complex.arg (facet_rep_a P (f k) / u) := by
  have hinj := p22_facet_arg_injOn P u s hs hP hu
  obtain ⟨f, hfim, hfmono⟩ := p22_enum_sorted (α := Set ℂ) hsize.1 hsize.2 hinj
  exact ⟨f, hfim, hfmono⟩

/-- HOL `POLY_SORT_BIJ` (counting_spheres.hl:795). Filled (EXPLICIT kit wave).
SF27 linkage check: consumes only `POLY_SORT`'s (unchanged, still proved)
statement; proof unchanged. -/
theorem POLY_SORT_BIJ (P : Set ℂ) (n : ℕ) (s : Set (Set ℂ)) (r : ℝ) (u : ℂ)
    (hs : s = {c : Set ℂ | facetOfC c P}) (hP : polyhedronC P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) (hu : u ≠ 0)
    (hsize : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → Set ℂ, s = f '' Set.Icc 1 n ∧ Set.BijOn f (Set.Icc 1 n) s ∧
      ∀ j k : ℕ, j ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → j < k →
      Complex.arg (facet_rep_a P (f j) / u) <
        Complex.arg (facet_rep_a P (f k) / u) := by
  obtain ⟨f, hfim, hfstrict⟩ := POLY_SORT P n s r u hs hP hr hrad hu hsize
  have hfmem : ∀ k ∈ Set.Icc 1 n, f k ∈ s := by
    intro k hk
    have h1 : f k ∈ f '' Set.Icc 1 n := ⟨k, hk, rfl⟩
    rw [← hfim] at h1
    exact h1
  refine ⟨f, hfim, ⟨?_, ?_, ?_⟩, hfstrict⟩
  · intro k hk
    exact hfmem k hk
  · intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hlt := hfstrict a b ha hb h
      rw [hab] at hlt
      exact lt_irrefl _ hlt
    · have hlt := hfstrict b a hb ha h
      rw [hab.symm] at hlt
      exact lt_irrefl _ hlt
  · intro c hc
    have h1 : c ∈ f '' Set.Icc 1 n := by rw [← hfim]; exact hc
    obtain ⟨k, hk, rfl⟩ := h1
    exact ⟨k, hk, rfl⟩

/-- HOL `facet_rep_nz` (counting_spheres.hl:817). -/
theorem facet_rep_nz (P c : Set ℂ) (hP : polyhedronC P) (hc : facetOfC c P) :
    facet_rep_a P c ≠ 0 := by
  have h := facet_rep_props P c hP hc
  intro h0
  rw [h0] at h
  exact absurd h.1 (by simp)


/-! ## SF30 bisector refill kit (branch-safe `holArg` linkage, 2026-10-08)

`bisector_point_exists` is refilled WITHOUT any `arg`-order to `holArg`-order
transfer: `holArg` is not monotone in `Complex.arg` (the `(-π, 0)` branch maps
reversely onto `(π, 2π)`, so only injectivity holds).  Instead, the refill
consumes the minimality hypothesis directly as a `holArg` inequality and only
touches `holArg` through the exact polar representation `p22_holArg_cos_sin`
(valid on both branches), with angle uniqueness from `p22_cos_sin_eq`. -/

/-- SF30 kit: real part of the unit ray `cos ψ + I * sin ψ`. -/
private theorem p22_cosI_sin_re (ψ : ℝ) :
    (Real.cos ψ + Complex.I * Real.sin ψ).re = Real.cos ψ := by
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- SF30 kit: imaginary part of the unit ray `cos ψ + I * sin ψ`. -/
private theorem p22_cosI_sin_im (ψ : ℝ) :
    (Real.cos ψ + Complex.I * Real.sin ψ).im = Real.sin ψ := by
  rw [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, Complex.ofReal_re, one_mul, zero_add, zero_add]

/-- SF30 kit: real part of the unit ray times a vector. -/
private theorem p22_cosI_sin_mul_re (ψ : ℝ) (w : ℂ) :
    ((Real.cos ψ + Complex.I * Real.sin ψ) * w).re
      = Real.cos ψ * w.re - Real.sin ψ * w.im := by
  rw [Complex.mul_re, p22_cosI_sin_re, p22_cosI_sin_im]

/-- SF30 kit: imaginary part of the unit ray times a vector. -/
private theorem p22_cosI_sin_mul_im (ψ : ℝ) (w : ℂ) :
    ((Real.cos ψ + Complex.I * Real.sin ψ) * w).im
      = Real.cos ψ * w.im + Real.sin ψ * w.re := by
  rw [Complex.mul_im, p22_cosI_sin_re, p22_cosI_sin_im]

/-- SF30 kit: `holArg` is nonnegative. -/
private theorem p22_holArg_nonneg (z : ℂ) : 0 ≤ holArg z := by
  rw [show holArg z =
      if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi from rfl]
  split
  · assumption
  · rename_i h
    have h1 : Complex.arg z < 0 := not_le.mp h
    have h2 := Complex.neg_pi_lt_arg z
    linarith

/-- SF30 kit: `holArg` is below `2π`. -/
private theorem p22_holArg_lt_two_pi (z : ℂ) : holArg z < 2 * Real.pi := by
  rw [show holArg z =
      if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi from rfl]
  split
  · have h1 := Complex.arg_le_pi z
    have h2 : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith
  · rename_i h
    have h1 : Complex.arg z < 0 := not_le.mp h
    linarith

/-- SF30 kit: an angle in `[0, 2π)` is determined by its `cos` and `sin`. -/
private theorem p22_cos_sin_eq (θ θ' : ℝ) (h1 : 0 ≤ θ) (h2 : θ < 2 * Real.pi)
    (h1' : 0 ≤ θ') (h2' : θ' < 2 * Real.pi)
    (hc : Real.cos θ = Real.cos θ') (hs : Real.sin θ = Real.sin θ') : θ = θ' := by
  have hpy : Real.cos θ' * Real.cos θ' + Real.sin θ' * Real.sin θ' = 1 := by
    have h := Real.sin_sq_add_cos_sq θ'
    rw [pow_two, pow_two] at h
    linarith
  have hc1 : Real.cos (θ - θ') = 1 := by
    rw [Real.cos_sub, hc, hs]
    exact hpy
  have hb1 : -(2 * Real.pi) < θ - θ' := by linarith [h1, h2', Real.pi_pos]
  have hb2 : θ - θ' < 2 * Real.pi := by linarith [h2, h1', Real.pi_pos]
  have h0 := (Real.cos_eq_one_iff_of_lt_of_lt hb1 hb2).mp hc1
  linarith

/-- SF30 kit: the exact polar representation behind `holArg`, valid on both
branches of the lift — this is what makes every refill computation
branch-safe. -/
private theorem p22_holArg_cos_sin (z : ℂ) (hz : z ≠ 0) :
    ‖z‖ • (Real.cos (holArg z) + Complex.I * Real.sin (holArg z)) = z := by
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hkey : ∀ α : ℝ, α = Complex.arg z ∨ α = Complex.arg z + 2 * Real.pi →
      ‖z‖ * Real.cos α = z.re ∧ ‖z‖ * Real.sin α = z.im := by
    intro α hor
    rcases hor with hα | hα
    · constructor
      · rw [hα, Complex.cos_arg hz]
        field_simp
      · rw [hα, Complex.sin_arg z]
        field_simp
    · constructor
      · rw [hα, show Real.cos (Complex.arg z + 2 * Real.pi)
            = Real.cos (Complex.arg z) from Real.cos_periodic _, Complex.cos_arg hz]
        field_simp
      · rw [hα, show Real.sin (Complex.arg z + 2 * Real.pi)
            = Real.sin (Complex.arg z) from Real.sin_periodic _, Complex.sin_arg z]
        field_simp
  rcases le_or_gt 0 (Complex.arg z) with h | h
  · have h1 := hkey (holArg z) (Or.inl (if_pos h))
    refine Complex.ext ?_ ?_
    · rw [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, p22_cosI_sin_re]
      exact h1.1
    · rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, p22_cosI_sin_im]
      exact h1.2
  · have h1 := hkey (holArg z) (Or.inr (if_neg (not_le.mpr h)))
    refine Complex.ext ?_ ?_
    · rw [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, p22_cosI_sin_re]
      exact h1.1
    · rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, p22_cosI_sin_im]
      exact h1.2

/-- HOL `bisector_point_exists` (counting_spheres.hl:825). GIANT.
SF30 statement-fix (same defect class as SF22/SF27, minesweep report §3): the
four `Complex.arg`s of the specification are lifted to `holArg` (range
`[0, 2π)`, the faithful HOL `Arg`).  Over the principal range `(-π, π]` the
`hpsi`/`hmin` data express a different facet configuration (the `(-π, 0) ↦
(π, 2π)` branch reversal), so the HOL proof is not portable to the frozen
statement; the statement is restated over `holArg`.
Refill (holArg non-monotonicity discipline): no step transfers an `arg` order
into a `holArg` order — `hmin` is consumed directly as a `holArg` inequality,
and `holArg` enters only through the exact representation
`z = ‖z‖ • (cos (holArg z) + I * sin (holArg z))` (`p22_holArg_cos_sin`,
branch-safe) with uniqueness `p22_cos_sin_eq`.  The `P v` arm applies
`POLYHEDRON_MEMBER` directly; the HOL proof routes it through `insert_v`,
whose core is exactly the per-facet `dot2` bound inlined here (so this refill
does not depend on the still-open `insert_v`). -/
theorem bisector_point_exists (P c c' : Set ℂ) (r : ℝ) :
    ∃ v : ℂ, ∀ psi : ℝ, polyhedronC P → facetOfC c P → facetOfC c' P → 0 < r →
      (∀ p : ℂ, ‖p‖ < r → p ∈ P) →
      psi = holArg (facet_rep_a P c' / facet_rep_a P c) / 2 →
      (∀ c'' : Set ℂ, facetOfC c'' P →
        holArg (facet_rep_a P c'' / facet_rep_a P c) < 2 * psi → c'' = c) →
      psi < Real.pi / 2 → c' ≠ c →
      v ∈ P ∧ ‖v‖ = r / Real.cos psi ∧
      holArg (v / facet_rep_a P c) = psi ∧
      holArg (facet_rep_a P c' / v) = psi := by
  set a : ℂ := facet_rep_a P c with hac
  set a' : ℂ := facet_rep_a P c' with hac'
  refine ⟨(r / Real.cos (holArg (a' / a) / 2)) •
      ((Real.cos (holArg (a' / a) / 2) + Complex.I * Real.sin (holArg (a' / a) / 2)) * a),
    ?_⟩
  intro psi hP hc hc' hr hrad hpsi hmin hlt hne
  obtain rfl : psi = holArg (a' / a) / 2 := hpsi
  set psi : ℝ := holArg (a' / a) / 2 with hpsidef
  -- facet representation facts
  have hprc := facet_rep_props P c hP hc
  have hprc' := facet_rep_props P c' hP hc'
  have hn1 : ‖a‖ = 1 := hprc.1
  have hn1' : ‖a'‖ = 1 := hprc'.1
  have hac0 : a ≠ 0 := by
    intro h0
    rw [h0] at hn1
    exact absurd hn1 (by simp)
  have hac0' : a' ≠ 0 := by
    intro h0
    rw [h0] at hn1'
    exact absurd hn1' (by simp)
  -- angle bookkeeping
  have hnn : 0 ≤ psi := div_nonneg (p22_holArg_nonneg _) (by norm_num)
  have hlt2pi : psi < 2 * Real.pi := by linarith [hlt, Real.pi_pos]
  have hcos : 0 < Real.cos psi :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hnn, Real.pi_pos], hlt⟩
  set t : ℝ := r / Real.cos psi with htdef
  set u : ℂ := Real.cos psi + Complex.I * Real.sin psi with hudef
  have ht0 : 0 < t := div_pos hr hcos
  have htnz : t ≠ 0 := ne_of_gt ht0
  have htc : (t : ℂ) ≠ 0 := by simpa using htnz
  have hu1 : ‖u‖ = 1 := by
    have hsq : ‖u‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hudef, p22_cosI_sin_re, p22_cosI_sin_im]
      have h := Real.sin_sq_add_cos_sq psi
      rw [pow_two, pow_two] at h
      linarith
    have hnn2 : 0 ≤ ‖u‖ := norm_nonneg _
    rcases sq_eq_one_iff.mp hsq with h1 | h1
    · exact h1
    · exact absurd h1 (by linarith)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu1]; norm_num)
  -- the witness point and its norm
  set v : ℂ := t • (u * a) with hvdef
  have hvt : ‖v‖ = t := by
    rw [hvdef, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, norm_mul, hu1, hn1]
    norm_num
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hvt
    exact absurd hvt.symm (ne_of_gt ht0)
  -- polar form of a'/a and the double-angle square
  have hzu : ‖a' / a‖ = 1 := by
    rw [norm_div, hn1', hn1]
    norm_num
  have hzne : a' / a ≠ 0 := div_ne_zero hac0' hac0
  have hzrep := p22_holArg_cos_sin (a' / a) hzne
  rw [hzu, one_smul] at hzrep
  have h2psi : holArg (a' / a) = 2 * psi := by rw [hpsidef]; ring
  rw [h2psi] at hzrep
  have hu2 : u * u = Real.cos (2 * psi) + Complex.I * Real.sin (2 * psi) := by
    refine Complex.ext ?_ ?_
    · rw [p22_cosI_sin_re, hudef, Complex.mul_re, p22_cosI_sin_re, p22_cosI_sin_im,
        Real.cos_two_mul']
      ring
    · rw [p22_cosI_sin_im, hudef, Complex.mul_im, p22_cosI_sin_re, p22_cosI_sin_im,
        Real.sin_two_mul]
      ring
  have hzsq : a' / a = u * u := by rw [hu2]; exact hzrep.symm
  -- (1) `holArg (v / a) = psi`: v / a lies on the positive psi ray
  have hva : v / a = t • u := by
    rw [hvdef, Complex.real_smul, mul_div_assoc, mul_comm u a,
      mul_div_cancel_left₀ u hac0, ← Complex.real_smul]
  have hvna : ‖v / a‖ = t := by
    rw [hva, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hu1]
    norm_num
  have hre1 : (v / a).re = t * Real.cos psi := by
    have h1 := congrArg Complex.re hva
    rw [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hudef, p22_cosI_sin_re] at h1
    exact h1
  have him1 : (v / a).im = t * Real.sin psi := by
    have h1 := congrArg Complex.im hva
    rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, hudef, p22_cosI_sin_im] at h1
    exact h1
  have hArg1 : holArg (v / a) = psi := by
    have hdva : v / a ≠ 0 := div_ne_zero hv0 hac0
    have hrep := p22_holArg_cos_sin (v / a) hdva
    have hr1 := congrArg Complex.re hrep
    have hi1 := congrArg Complex.im hrep
    rw [hvna, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hre1] at hr1
    rw [hvna, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, him1] at hi1
    have hc1 : Real.cos (holArg (v / a)) = Real.cos psi := by
      have h := mul_left_cancel₀ htnz hr1
      rw [p22_cosI_sin_re] at h
      exact h
    have hs1 : Real.sin (holArg (v / a)) = Real.sin psi := by
      have h := mul_left_cancel₀ htnz hi1
      rw [p22_cosI_sin_im] at h
      exact h
    exact p22_cos_sin_eq _ _ (p22_holArg_nonneg _) (p22_holArg_lt_two_pi _) hnn hlt2pi hc1 hs1
  -- (2) `holArg (a' / v) = psi`: a' / v is the reciprocal-scaled psi ray
  have hmul : (t : ℂ) * (a' / v) = u := by
    have hv' : v = (t : ℂ) * (u * a) := by rw [hvdef, Complex.real_smul]
    rw [hv', mul_div_assoc' _ _ _, mul_div_mul_left _ _ htc]
    rw [show a' / (u * a) = (a' / a) / u from by field_simp]
    rw [hzsq, mul_div_cancel_left₀ u hu0]
  have hvna' : ‖a' / v‖ * t = 1 := by
    have h1 := congrArg norm hmul
    rw [norm_mul, hu1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0] at h1
    calc ‖a' / v‖ * t = t * ‖a' / v‖ := mul_comm _ _
      _ = 1 := h1
  have hre2 : (a' / v).re * t = Real.cos psi := by
    have h1 := congrArg Complex.re hmul
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hudef, p22_cosI_sin_re, mul_comm t (a' / v).re] at h1
    exact h1
  have him2 : (a' / v).im * t = Real.sin psi := by
    have h1 := congrArg Complex.im hmul
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hudef, p22_cosI_sin_im, mul_comm t (a' / v).im] at h1
    exact h1
  have hArg2 : holArg (a' / v) = psi := by
    have hdv : a' / v ≠ 0 := div_ne_zero hac0' hv0
    have hrep := p22_holArg_cos_sin (a' / v) hdv
    have hr2 := congrArg Complex.re hrep
    rw [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hr2
    have hi2 := congrArg Complex.im hrep
    rw [Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] at hi2
    -- hr2 : ‖a'/v‖ * Real.cos (holArg (a'/v)) = (a'/v).re
    have hr3 : Real.cos (holArg (a' / v)) = Real.cos psi := by
      have h3 := congrArg (fun r : ℝ => r * t) hr2
      rw [mul_right_comm, hvna', one_mul, hre2, p22_cosI_sin_re] at h3
      exact h3
    have hi3 : Real.sin (holArg (a' / v)) = Real.sin psi := by
      have h3 := congrArg (fun r : ℝ => r * t) hi2
      rw [mul_right_comm, hvna', one_mul, him2, p22_cosI_sin_im] at h3
      exact h3
    exact p22_cos_sin_eq _ _ (p22_holArg_nonneg _) (p22_holArg_lt_two_pi _) hnn hlt2pi hr3 hi3
  refine ⟨?_, hvt.trans htdef, hArg1, hArg2⟩
  -- (3) `v ∈ P`: POLYHEDRON_MEMBER with the per-facet dot2 bound
  -- (the core of HOL `insert_v`, inlined here)
  refine POLYHEDRON_MEMBER P r v hP hr hrad fun c'' hc'' => ?_
  have hpr2 := facet_rep_props P c'' hP hc''
  have hb2 : r ≤ facet_rep_b P c'' := hpr2.2.1 r hr hrad
  set a2 : ℂ := facet_rep_a P c'' with ha2def
  have hn2 : ‖a2‖ = 1 := hpr2.1
  have ha20 : a2 ≠ 0 := by
    intro h0
    rw [h0] at hn2
    exact absurd hn2 (by simp)
  set z : ℂ := a2 / a with hzdef
  have hz1 : ‖z‖ = 1 := by
    rw [hzdef, norm_div, hn2, hn1]
    norm_num
  have hz0 : z ≠ 0 := div_ne_zero ha20 hac0
  have hzrep := p22_holArg_cos_sin z hz0
  rw [hz1, one_smul] at hzrep
  have hzre : z.re = Real.cos (holArg z) := by
    have h := congrArg Complex.re hzrep
    rw [p22_cosI_sin_re] at h
    exact h.symm
  have hzim : z.im = Real.sin (holArg z) := by
    have h := congrArg Complex.im hzrep
    rw [p22_cosI_sin_im] at h
    exact h.symm
  have hns1 : Complex.normSq a = 1 := by rw [← Complex.sq_norm, hn1]; norm_num
  have hdiv_re : z.re = a2.re * a.re + a2.im * a.im := by
    rw [hzdef, Complex.div_re, hns1]
    simp
  have hdiv_im : z.im = a2.im * a.re - a2.re * a.im := by
    rw [hzdef, Complex.div_im, hns1]
    simp
  have hure : (u * a).re = Real.cos psi * a.re - Real.sin psi * a.im :=
    p22_cosI_sin_mul_re psi a
  have huim : (u * a).im = Real.cos psi * a.im + Real.sin psi * a.re :=
    p22_cosI_sin_mul_im psi a
  have hdot : dot2 a2 v = t * Real.cos (holArg z - psi) := by
    calc dot2 a2 v
        = t * dot2 a2 (u * a) := by rw [hvdef]; exact p22_dot2_smul_right _ _ _
      _ = t * (a2.re * (u * a).re + a2.im * (u * a).im) := by rw [dot2_expand]
      _ = t * (Real.cos psi * (a2.re * a.re + a2.im * a.im)
            + Real.sin psi * (a2.im * a.re - a2.re * a.im)) := by
          rw [hure, huim]
          ring
      _ = t * Real.cos (holArg z - psi) := by
          rw [← hdiv_re, ← hdiv_im, hzre, hzim, Real.cos_sub]
          ring
  rcases eq_or_ne c'' c with heq2 | hne2
  · -- the reference facet: z = a / a = 1, angle 0
    have ha2a : a2 = a := by
      rw [ha2def, heq2]
    have hz1' : z = 1 := by
      rw [hzdef, ha2a, div_self hac0]
    have hhol1 : holArg z = 0 := by
      rw [hz1']
      rw [show holArg (1 : ℂ) =
          if 0 ≤ Complex.arg (1 : ℂ) then Complex.arg (1 : ℂ)
            else Complex.arg (1 : ℂ) + 2 * Real.pi from rfl]
      rw [Complex.arg_one]
      simp
    rw [hdot, hhol1, show (0 : ℝ) - psi = -psi from by ring, Real.cos_neg, htdef,
      div_mul_cancel₀ r (ne_of_gt hcos)]
    exact hb2
  · -- c'' ≠ c: the minimality hypothesis pins holArg z ≥ 2ψ, then eus_cos
    have hge : 2 * psi ≤ holArg z := by
      rcases lt_or_ge (holArg z) (2 * psi) with h | h
      · exact absurd (hmin c'' hc'' h) hne2
      · exact h
    rw [hdot]
    refine le_trans (mul_le_mul_of_nonneg_left
      (eus_cos (holArg z - psi) psi hnn (by linarith)
        (by linarith [p22_holArg_lt_two_pi z])) (le_of_lt ht0)) ?_
    rw [htdef, div_mul_cancel₀ r (ne_of_gt hcos)]
    exact hb2

/-- HOL `bisector_point` (new_specification, counting_spheres.hl:943).
SF30 linkage: the underlying existence theorem is now stated over `holArg`
(range `[0, 2π)`, the faithful HOL `Arg`); the chosen point is unchanged in
kind. -/
noncomputable def bisector_point (P c c' : Set ℂ) (r : ℝ) : ℂ :=
  Classical.choose (bisector_point_exists P c c' r)

/-- Unfolding of the `bisector_point` specification.
SF30 linkage: the `Complex.arg`s are lifted to `holArg` along with
`bisector_point_exists`. -/
theorem bisector_point_props (P c c' : Set ℂ) (r : ℝ) (psi : ℝ)
    (hP : polyhedronC P) (hc : facetOfC c P) (hc' : facetOfC c' P) (hr : 0 < r)
    (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P)
    (hpsi : psi = holArg (facet_rep_a P c' / facet_rep_a P c) / 2)
    (hmin : ∀ c'' : Set ℂ, facetOfC c'' P →
      holArg (facet_rep_a P c'' / facet_rep_a P c) < 2 * psi → c'' = c)
    (hlt : psi < Real.pi / 2) (hne : c' ≠ c) :
    bisector_point P c c' r ∈ P ∧ ‖bisector_point P c c' r‖ = r / Real.cos psi ∧
      holArg (bisector_point P c c' r / facet_rep_a P c) = psi ∧
      holArg (facet_rep_a P c' / bisector_point P c c' r) = psi :=
  Classical.choose_spec (bisector_point_exists P c c' r)
    psi hP hc hc' hr hrad hpsi hmin hlt hne

end Kepler.Text
