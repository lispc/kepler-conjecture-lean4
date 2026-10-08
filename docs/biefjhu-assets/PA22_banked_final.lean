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
  sorry -- DEF-FIX: refill per counting_spheres.hl:825 §3a

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

/-! ## UKBRPFE numeric kit (PA22c wave): Taylor/asin bounds for the
`regular_spherical_polygon_area` gap `2π - 2k·asn(cos 0.797·sin(π/k))`.
STATUS: fully consumed (PA22d wave): base `k = 3` (`p22_ukb_base3` /
`p22_ukb3`), `k ∈ {4..11}` finite cases (`p22_ukb_base4..11`) and `k ≥ 12`
directly (`p22_ukb_hi`, no derivative machinery needed); `UKBRPFE_explicit`
closed - no NEEDS left in this chain. -/

private theorem p22_pi_lb : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2

private theorem p22_pi_ub : Real.pi < 3.15 := Real.pi_lt_d2

/- ## sin high-order bound: alternating Taylor upper bound -/
/-- `cos t ≤ 1 - t²/2 + t⁴/24` for `0 ≤ t ≤ 4`. -/
private theorem p22_cos_le_taylor4 {t : ℝ} (ht : 0 ≤ t) (ht4 : t ≤ 4) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  rcases lt_or_eq_of_le ht with ht0 | rfl
  · have h2 := Real.cos_two_mul_eq_one_sub (t / 2)
    rw [show (2:ℝ) * (t / 2) = t from by ring] at h2
    have h16 : t ^ 2 ≤ 16 := by nlinarith
    have hage : 0 ≤ t / 2 - t ^ 3 / 48 := by
      have h316 : t ^ 3 ≤ 16 * t := by nlinarith [h16, ht]
      nlinarith
    have hsin : t / 2 - t ^ 3 / 48 ≤ Real.sin (t / 2) := by
      have h3 := Real.sin_gt_sub_cube (x := t / 2) (by linarith)
      have hrw : (t / 2) ^ 3 / 6 = t ^ 3 / 48 := by ring
      rw [hrw] at h3
      linarith
    have hspos : 0 ≤ Real.sin (t / 2) := by linarith
    have hss : 0 ≤ Real.sin (t / 2) + (t / 2 - t ^ 3 / 48) := by linarith
    have hsa : 0 ≤ Real.sin (t / 2) - (t / 2 - t ^ 3 / 48) := by linarith
    have hsq : (t / 2 - t ^ 3 / 48) ^ 2 ≤ Real.sin (t / 2) ^ 2 := by
      nlinarith [hss, hsa]
    have hexpl : 2 * (t / 2 - t ^ 3 / 48) ^ 2
        = t ^ 2 / 2 - t ^ 4 / 24 + t ^ 6 / 1152 := by ring
    have ht6 : (0:ℝ) ≤ t ^ 6 := by positivity
    have h2a : t ^ 2 / 2 - t ^ 4 / 24 ≤ 2 * (t / 2 - t ^ 3 / 48) ^ 2 := by
      rw [hexpl]; linarith
    rw [h2]
    linarith [hsq, h2a]
  · norm_num [Real.cos_zero]

/-- `sin y ≤ y - y³/6 + y⁵/120` for `0 ≤ y ≤ 4` (alternating Taylor upper bound). -/
private theorem p22_sin_le_taylor5 {y : ℝ} (hy : 0 ≤ y) (hy4 : y ≤ 4) :
    Real.sin y ≤ y - y ^ 3 / 6 + y ^ 5 / 120 := by
  set h : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t with hh
  have hf : (fun r : ℝ => r - r ^ 3 / 6 + r ^ 5 / 120 - Real.sin r)
      = fun r => (r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) - Real.sin r := by
    funext r; ring
  have hd : ∀ t : ℝ, deriv h t = 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t := by
    intro t
    rw [hh, hf]
    have dF : DifferentiableAt ℝ
        (fun r : ℝ => r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) t := by
      fun_prop
    have hrest : deriv
        (fun r : ℝ => (r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) - Real.sin r) t
        = deriv (fun r : ℝ => r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) t
          - deriv Real.sin t :=
      deriv_fun_sub dF (Real.differentiable_sin t)
    have hid1 : deriv (fun r : ℝ => r) t = 1 := by simp [deriv_id'']
    have d1 : DifferentiableAt ℝ (fun r : ℝ => r) t := by fun_prop
    have d23 : DifferentiableAt ℝ (fun r : ℝ => (-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5) t := by
      fun_prop
    have d3 : DifferentiableAt ℝ (fun r : ℝ => (-1 / 6) * r ^ 3) t := by fun_prop
    have d4 : DifferentiableAt ℝ (fun r : ℝ => (1 / 120) * r ^ 5) t := by fun_prop
    have hadd1 : deriv (fun r : ℝ => r + ((-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5)) t
        = deriv (fun r : ℝ => r) t
          + deriv (fun r : ℝ => (-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5) t :=
      deriv_fun_add d1 d23
    have hadd2 : deriv (fun r : ℝ => (-1 / 6) * r ^ 3 + (1 / 120) * r ^ 5) t
        = deriv (fun r : ℝ => (-1 / 6) * r ^ 3) t
          + deriv (fun r : ℝ => (1 / 120) * r ^ 5) t :=
      deriv_fun_add d3 d4
    have hcm1 : deriv (fun r : ℝ => (-1 / 6) * r ^ 3) t
        = (-1 / 6) * deriv (fun r : ℝ => r ^ 3) t :=
      congrFun (deriv_const_mul_field' (-1 / 6)) t
    have hcm2 : deriv (fun r : ℝ => (1 / 120) * r ^ 5) t
        = (1 / 120) * deriv (fun r : ℝ => r ^ 5) t :=
      congrFun (deriv_const_mul_field' (1 / 120)) t
    have hp3 : deriv (fun r : ℝ => r ^ 3) t = 3 * t ^ 2 := deriv_pow_field (n := 3) (x := t)
    have hp5 : deriv (fun r : ℝ => r ^ 5) t = 5 * t ^ 4 := deriv_pow_field (n := 5) (x := t)
    have hsin1 : deriv Real.sin t = Real.cos t :=
      (Real.hasDerivAt_sin t).deriv
    rw [hrest, hadd1, hadd2, hid1, hcm1, hcm2, hp3, hp5, hsin1]
    ring
  have hdiff : Differentiable ℝ h := by fun_prop
  have key : ∀ s : ℝ, 0 ≤ s → 0 ≤ 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s := by
    intro s hs
    rcases le_or_gt s 4 with hle4 | hge4
    · have hc := p22_cos_le_taylor4 hs hle4
      linarith
    · have hs2pos : (0:ℝ) ≤ s ^ 2 := by nlinarith
      have hsub : 0 ≤ s ^ 2 - 12 := by nlinarith [hge4]
      have hs4 : (0:ℝ) ≤ s ^ 4 / 24 - s ^ 2 / 2 := by
        have he : s ^ 4 / 24 - s ^ 2 / 2 = s ^ 2 * (s ^ 2 - 12) / 24 := by ring
        rw [he]
        exact div_nonneg (mul_nonneg hs2pos hsub) (by norm_num)
      linarith [Real.cos_le_one s, hs4]
  have hge : ∀ t : ℝ, 0 ≤ deriv h t := by
    intro t
    rw [hd t]
    rcases le_or_gt t 0 with hneg | hnonneg
    · have h2 := hd (-t)
      rw [show (-t:ℝ) ^ 2 = t ^ 2 from by ring, show (-t:ℝ) ^ 4 = t ^ 4 from by ring,
        Real.cos_neg] at h2
      have hk := key (-t) (by linarith)
      rw [show (-t:ℝ) ^ 2 = t ^ 2 from by ring, show (-t:ℝ) ^ 4 = t ^ 4 from by ring,
        Real.cos_neg] at hk
      exact hk
    · exact key t (le_of_lt hnonneg)
  have hmono : Monotone h := monotone_of_deriv_nonneg hdiff hge
  have h0 : h 0 = 0 := by
    rw [hh]; norm_num [Real.sin_zero]
  have hle : h 0 ≤ h y := hmono (by nlinarith)
  rw [h0] at hle
  have hle2 : 0 ≤ y - y ^ 3 / 6 + y ^ 5 / 120 - Real.sin y := hle
  linarith

/- ## cos 0.797 numeric window -/
/-- `cos 0.797 ≤ 0.6991`, via half angle + `sin_gt_sub_cube`. -/
private theorem p22_cc_le : Real.cos 0.797 ≤ 6991 / 10000 := by
  have h := Real.cos_two_mul_eq_one_sub ((0.797:ℝ) / 2)
  rw [show (2:ℝ) * (0.797 / 2) = 0.797 from by ring] at h
  have hsin : (3879:ℝ) / 10000 < Real.sin (0.797 / 2) := by
    have h3 := Real.sin_gt_sub_cube (x := (0.797 / 2)) (by norm_num)
    norm_num at h3 ⊢
    linarith
  rw [h]
  nlinarith

/-- `0.65 ≤ cos 0.797`, via `one_sub_sq_div_two_le_cos`. -/
private theorem p22_cc_lb : (65:ℝ) / 100 ≤ Real.cos 0.797 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := (0.797:ℝ))
  norm_num at h ⊢
  linarith

/- ## arcsin upper bounds -/
/-- `arcsin v ≤ v / √(1 - v²)` for `0 ≤ v < 1` (tan dominates arcsin). -/
private theorem p22_asn_le_tan {v : ℝ} (hv : 0 ≤ v) (hv1 : v < 1) :
    asn v ≤ v / Real.sqrt (1 - v ^ 2) := by
  show Real.arcsin v ≤ v / Real.sqrt (1 - v ^ 2)
  rcases eq_or_lt_of_le hv with rfl | hv0
  · simp
  · have ha1 : 0 < Real.arcsin v := Real.arcsin_pos.mpr hv0
    have ha2 : Real.arcsin v < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hv1
    have hlt := Real.lt_tan ha1 ha2
    have htan : Real.tan (Real.arcsin v) = v / Real.sqrt (1 - v ^ 2) := by
      rw [Real.tan_eq_sin_div_cos, Real.sin_arcsin (by linarith) (by linarith),
        Real.cos_arcsin]
    linarith

/-- arcsin upper bound with cubic correction:
`arcsin w ≤ w + (w³/3) · (√(1-w²)⁻¹ / (1 + √(1-w²)))` for `0 ≤ w < 1`
(via `1/√(1-t²) - 1 = t²/(√(1-t²)(1+√(1-t²)))` on `[0,w]` and monotone integrals). -/
private theorem p22_asn_le_add {w : ℝ} (hw : 0 ≤ w) (hw1 : w < 1) :
    asn w ≤ w + (Real.sqrt (1 - w ^ 2))⁻¹ / (1 + Real.sqrt (1 - w ^ 2)) * (w ^ 3 / 3) := by
  show Real.arcsin w ≤ _
  set s := Real.sqrt (1 - w ^ 2) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc (0:ℝ) w) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2))
      (Set.uIcc (0:ℝ) w) :=
    ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) (by
        intro t ht
        rw [Set.uIcc_of_le hw] at ht
        obtain ⟨ht0, htw⟩ := ht
        have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
        simpa using ne_of_gt (Real.sqrt_pos.mpr hp))
  -- hint: arcsin as an integral of its derivative
  have hint : ∫ t in (0:ℝ)..w, 1 / Real.sqrt (1 - t ^ 2) = asn w := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) w, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t :=
      fun t ht => by
        rw [Set.uIcc_of_le hw] at ht
        obtain ⟨ht0, htw⟩ := ht
        exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
    simp [asn, Real.arcsin_zero]
  -- integrand bound: 1/√(1-t²) ≤ 1 + (s⁻¹/(1+s))·t²  on [0,w]
  have hdiff : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) w →
      1 / Real.sqrt (1 - t ^ 2) ≤ 1 + (s⁻¹ / (1 + s)) * t ^ 2 := by
    intro t ht
    obtain ⟨ht0, htw⟩ := ht
    have ht1 : t < 1 := lt_of_le_of_lt htw hw1
    have hpos : 0 < 1 - t ^ 2 := by nlinarith
    have hX : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr hpos
    have hge : s ≤ Real.sqrt (1 - t ^ 2) := by
      apply Real.sqrt_le_sqrt
      have htw1 : t * t ≤ t * w := mul_le_mul_of_nonneg_left htw ht0
      have htw2 : t * w ≤ w * w := mul_le_mul_of_nonneg_right htw hw
      linarith [htw1, htw2]
    have hXsq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith)
    have hinv1 : (Real.sqrt (1 - t ^ 2))⁻¹ ≤ s⁻¹ :=
      (inv_le_inv₀ hX hspos).mpr hge
    have hp2 : (0:ℝ) < 1 + Real.sqrt (1 - t ^ 2) := by linarith [hpos]
    have hsb : (0:ℝ) < 1 + s := by positivity
    have hinv2 : ((1:ℝ) + Real.sqrt (1 - t ^ 2))⁻¹ ≤ (1 + s)⁻¹ :=
      (inv_le_inv₀ hp2 hsb).mpr (by linarith [hge])
    have hden : s * (1 + s) ≤ Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)) := by
      calc s * (1 + s) ≤ Real.sqrt (1 - t ^ 2) * (1 + s) :=
            mul_le_mul_of_nonneg_right hge (by linarith)
        _ ≤ Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)) :=
            mul_le_mul_of_nonneg_left (by linarith [hge]) (le_of_lt hX)
    have hdenpos : (0:ℝ) < Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)) := by
      positivity
    have hstep : (1:ℝ) / (Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)))
        ≤ s⁻¹ / (1 + s) := by
      have hpp : (0:ℝ) < s * (1 + s) := mul_pos hspos (by linarith)
      have h2 : (1:ℝ) / (Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)))
          ≤ (1:ℝ) / (s * (1 + s)) := one_div_le_one_div_of_le hpp hden
      have h3 : (1:ℝ) / (s * (1 + s)) = s⁻¹ / (1 + s) := by field_simp
      rw [← h3]
      exact h2
    have hXne : Real.sqrt (1 - t ^ 2) ≠ 0 := ne_of_gt hX
    have hsplit : 1 / Real.sqrt (1 - t ^ 2) - 1
        = (1 - Real.sqrt (1 - t ^ 2)) / Real.sqrt (1 - t ^ 2) := by
      rw [eq_div_iff hXne, sub_mul, div_mul_cancel₀ _ hXne]
      ring
    have hrat : (1:ℝ) - Real.sqrt (1 - t ^ 2)
        = t ^ 2 / (1 + Real.sqrt (1 - t ^ 2)) := by
      have hne : (1:ℝ) + Real.sqrt (1 - t ^ 2) ≠ 0 := by positivity
      rw [eq_div_iff hne]
      nlinarith [hXsq]
    have hmain : 1 / Real.sqrt (1 - t ^ 2) - 1 ≤ (s⁻¹ / (1 + s)) * t ^ 2 := by
      rw [hsplit, hrat]
      have hd : t ^ 2 / (1 + Real.sqrt (1 - t ^ 2)) / Real.sqrt (1 - t ^ 2)
          = t ^ 2 * (1 / (Real.sqrt (1 - t ^ 2) * (1 + Real.sqrt (1 - t ^ 2)))) := by
        field_simp
      rw [hd, mul_comm (s⁻¹ / (1 + s)) (t ^ 2)]
      exact mul_le_mul_of_nonneg_left hstep (sq_nonneg t)
    linarith [hmain]
  -- integrate
  have hI1 : IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2)) MeasureTheory.volume (0:ℝ) w :=
    hcon.intervalIntegrable
  have hc1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.uIcc (0:ℝ) w))
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ 2) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun t : ℝ => t ^ 2) (Set.uIcc (0:ℝ) w))
  have hI2 : IntervalIntegrable (fun t : ℝ => (s⁻¹ / (1 + s)) * t ^ 2) MeasureTheory.volume (0:ℝ) w :=
    hbase.const_mul (s⁻¹ / (1 + s))
  have hI12 : IntervalIntegrable (fun t : ℝ => 1 + (s⁻¹ / (1 + s)) * t ^ 2)
      MeasureTheory.volume (0:ℝ) w := by simpa using hc1.add hI2
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hI1 hI12 hdiff
  have hpow : ∫ t in (0:ℝ)..w, 1 + (s⁻¹ / (1 + s)) * t ^ 2
      = w + (s⁻¹ / (1 + s)) * (w ^ 3 / 3) := by
    rw [intervalIntegral.integral_add hc1 hI2, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [hint] at hmono
  rw [hpow] at hmono
  exact hmono

/- ## UKBRPFE exemplar: the k = 3 base case -/
/-- Numeric core of `UKBRPFE_explicit` at `k = 3`:
`2.097 - 0.0331 * 3 ≤ 2π - 6 * asn (cos 0.797 * sin (π/3))`. -/
private theorem p22_ukb_base3 : (2.097 - 0.0331 * 3 : ℝ)
    ≤ 2 * Real.pi - 2 * 3 * asn (Real.cos 0.797 * Real.sin (Real.pi / 3)) := by
  have hsin3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have hsqrt3 : Real.sqrt 3 / 2 ≤ 7 / 8 := by
    have h1 : Real.sqrt 3 ≤ 7 / 4 := by
      rw [Real.sqrt_le_iff]
      norm_num
    linarith
  set v := Real.cos 0.797 * Real.sin (Real.pi / 3) with hvdef
  have ccle7 : Real.cos 0.797 ≤ 7 / 10 := le_trans p22_cc_le (by norm_num)
  have hsinle : Real.sin (Real.pi / 3) ≤ 7 / 8 := by rw [hsin3]; linarith [hsqrt3]
  have hpos1 : (0:ℝ) ≤ Real.cos 0.797 := by linarith [p22_cc_lb]
  have hpos2 : (0:ℝ) ≤ Real.sin (Real.pi / 3) := by rw [hsin3]; positivity
  have hstep : Real.cos 0.797 * Real.sin (Real.pi / 3) ≤ 49 / 80 := by
    have h1 : Real.cos 0.797 * Real.sin (Real.pi / 3)
        ≤ (7:ℝ) / 10 * Real.sin (Real.pi / 3) := mul_le_mul_of_nonneg_right ccle7 hpos2
    have h2 : (7:ℝ) / 10 * Real.sin (Real.pi / 3) ≤ (7:ℝ) / 10 * (7 / 8) :=
      mul_le_mul_of_nonneg_left hsinle (by positivity)
    have h3 : (7:ℝ) / 10 * (7 / 8) = 49 / 80 := by norm_num
    linarith [h1, h2, h3]
  have hv80 : v ≤ 49 / 80 := by rw [hvdef]; exact hstep
  have hv0 : 0 ≤ v := by rw [hvdef]; exact mul_nonneg hpos1 hpos2
  have hv1 : v < 1 := by
    have h1 : (49:ℝ) / 80 < 1 := by norm_num
    linarith
  have hv2m : v * v ≤ (49 / 80) * (49 / 80) := by
    have ha : v * v ≤ v * (49 / 80) := mul_le_mul_of_nonneg_left hv80 hv0
    have hb : v * (49 / 80) ≤ (49 / 80) * (49 / 80) :=
      mul_le_mul_of_nonneg_right hv80 (by positivity)
    nlinarith [ha, hb]
  have h492' : ((49:ℝ) / 80) * ((49:ℝ) / 80) = 2401 / 6400 := by norm_num
  have hv2le : (v:ℝ) * v ≤ 2401 / 6400 := by linarith [hv2m, h492']
  have hs : (79:ℝ) / 100 ≤ Real.sqrt (1 - v ^ 2) := by
    have h792 : ((79:ℝ)/100) ^ 2 = 6241 / 10000 := by norm_num
    have h79eq : ((79:ℝ)/100) = Real.sqrt (((79:ℝ)/100) ^ 2) := by
      rw [Real.sqrt_sq (show (0:ℝ) ≤ 79 / 100 by norm_num)]
    rw [h79eq, show v ^ 2 = v * v from by ring]
    exact Real.sqrt_le_sqrt (by linarith [h792, hv2m, h492'])
  have hsinvp : (0:ℝ) < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hv3 : v * (v * v) ≤ (49 / 80) * ((49 / 80) * (49 / 80)) := by
    have ha : v * (v * v) ≤ (49 / 80) * (v * v) :=
      mul_le_mul_of_nonneg_right hv80 (mul_nonneg hv0 hv0)
    have hb : (49 / 80) * (v * v) ≤ (49 / 80) * ((49 / 80) * (49 / 80)) :=
      mul_le_mul_of_nonneg_left hv2m (by positivity)
    exact le_trans ha hb
  have hv3pos : (0:ℝ) ≤ v * (v * v) :=
    mul_nonneg hv0 (mul_nonneg hv0 hv0)
  have h493 : (49:ℝ) / 80 * (2401 / 6400) = 117649 / 512000 := by norm_num
  have hK : (Real.sqrt (1 - v ^ 2))⁻¹ / (1 + Real.sqrt (1 - v ^ 2)) ≤ 5 / 7 := by
    have hipos : (0:ℝ) < 1 + Real.sqrt (1 - v ^ 2) := by linarith
    have h79s : (79:ℝ) / 100 ≤ Real.sqrt (1 - v ^ 2) := hs
    have ha : (Real.sqrt (1 - v ^ 2))⁻¹ ≤ ((79:ℝ) / 100)⁻¹ :=
      (inv_le_inv₀ hsinvp (by norm_num)).mpr h79s
    have hb : (1 + Real.sqrt (1 - v ^ 2))⁻¹ ≤ ((179:ℝ) / 100)⁻¹ :=
      (inv_le_inv₀ hipos (by norm_num)).mpr (by linarith)
    calc (Real.sqrt (1 - v ^ 2))⁻¹ / (1 + Real.sqrt (1 - v ^ 2))
        = (Real.sqrt (1 - v ^ 2))⁻¹ * (1 + Real.sqrt (1 - v ^ 2))⁻¹ := by ring
      _ ≤ ((79:ℝ) / 100)⁻¹ * ((179:ℝ) / 100)⁻¹ := mul_le_mul ha hb (by positivity)
          (by positivity)
      _ ≤ 5 / 7 := by norm_num
  have hub := p22_asn_le_add hv0 hv1
  have hdiv : v * (v * v) / 3 ≤ (49 / 80) * ((49 / 80) * (49 / 80)) / 3 :=
    mul_le_mul_of_nonneg_right hv3 (by positivity)
  have hbound : v + (Real.sqrt (1 - v ^ 2))⁻¹ / (1 + Real.sqrt (1 - v ^ 2)) * (v ^ 3 / 3)
      ≤ 49 / 80 + (5 / 7) * ((49 / 80) ^ 3 / 3) := by
    have hprod : (Real.sqrt (1 - v ^ 2))⁻¹ / (1 + Real.sqrt (1 - v ^ 2)) * (v ^ 3 / 3)
        ≤ (5 / 7) * ((49 / 80) ^ 3 / 3) := by
      rw [show v ^ 3 = v * (v * v) from by ring]
      refine le_trans (mul_le_mul_of_nonneg_right hK
        (div_nonneg hv3pos (by norm_num))) ?_
      rw [← show (49:ℝ) / 80 * ((49:ℝ) / 80 * ((49:ℝ) / 80)) = (49 / 80) ^ 3 from by ring]
      exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
    exact add_le_add hv80 hprod
  have hub3 : asn v ≤ 6700 / 10000 := by
    have hnum : (49:ℝ) / 80 + (5 / 7) * ((49 / 80) ^ 3 / 3) ≤ 6700 / 10000 := by norm_num
    linarith [hub, hbound, hnum]
  have hpi : (3.14:ℝ) * 2 ≤ 2 * Real.pi := by
    linarith [p22_pi_lb]
  linarith [hub3, hpi]

/-- The UKBRPFE base case at `k = 3`, in the shape of the theorem. -/
private theorem p22_ukb3 : (0.591 - 0.0331 * 3 + 0.506 * lfun 1 + 1 : ℝ)
    ≤ max 0 (regularSphericalPolygonAreaP22 (Real.cos 0.797) 3) := by
  have hlf : (0.506 * lfun 1 : ℝ) = 0.506 := by
    have h1 : lfun (1:ℝ) = 1 := by norm_num [lfun, h0]
    rw [h1]
    norm_num
  have harea : regularSphericalPolygonAreaP22 (Real.cos 0.797) 3
      = 2 * Real.pi - 2 * 3 * asn (Real.cos 0.797 * Real.sin (Real.pi / 3)) := rfl
  have hub3 := p22_ukb_base3
  have hgoal : (0.591:ℝ) - 0.0331 * 3 + 0.506 + 1 = 2.097 - 0.0331 * 3 := by norm_num
  rw [hlf, hgoal, harea]
  refine le_trans hub3 (le_max_right _ _)

/-! ## UKBRPFE fill-in wave (PA22d).  Erratum-aware route (see NEEDS at
`UKBRPFE_explicit`): (a) `k ∈ {4..11}` finite cases by the base3 template
(`p22_asn_le_add` + `p22_sin_le_taylor5`, per-`k` rational windows, margins
≥ 0.079 at k = 6); (b) `k ≥ 12` a direct bound from `sin y ≤ y` + the same
`asn` window with `v ≤ 2.205/k` (margin ≈ 0.145 at k = 12) - no derivative
machinery needed after all.  Numeric windows machine-checked against exact
rational arithmetic at fill time; true-gap margins: k = 6 worst finite case
≈ 0.079, hi-case ≈ 0.145 at k = 12. -/

/-- `a / c ≤ b / c` for `0 < c` (pinned helper; the bundled name varies
across Mathlib versions). -/
private theorem p22_div_le_div_right {a b c : ℝ} (hc : 0 < c) (hab : a ≤ b) :
    a / c ≤ b / c := by
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hc.le)

/-- `a / c ≤ b / c` for a natural divisor `c > 0`. -/
private theorem p22_div_le_div_nat_right {a b : ℝ} {c : ℕ} (hc : (0:ℝ) < c) (hab : a ≤ b) :
    a / c ≤ b / c := by
  have e1 : a / c = (c:ℝ)⁻¹ * a := by field_simp
  have e2 : b / c = (c:ℝ)⁻¹ * b := by field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hc.le)

/-- `a / d ≤ a / c` for naturals `0 < c ≤ d` (larger divisor, smaller
quotient). -/
private theorem p22_div_le_div_nat_left {a : ℝ} {c d : ℕ} (ha : 0 ≤ a) (hc : (0:ℝ) < (c:ℝ))
    (hcd : c ≤ d) : a / d ≤ a / c := by
  have hd : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hc (by exact_mod_cast hcd)
  have hinv : (d:ℝ)⁻¹ ≤ (c:ℝ)⁻¹ := (inv_le_inv₀ hd hc).mpr (by exact_mod_cast hcd)
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right hinv ha

/-- `a / d ≤ a / c` for reals `0 < c ≤ d`. -/
private theorem p22_div_le_div_real_left {a c d : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hcd : c ≤ d) : a / d ≤ a / c := by
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  have hinv : d⁻¹ ≤ c⁻¹ := (inv_le_inv₀ hd hc).mpr hcd
  rw [div_eq_inv_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right hinv ha

/-- Shared assembly for the UKBRPFE gap: given `v ≤ Vt`, `0 < s ≤ √(1 - v²)`
and the rational window check
`2k·(Vt + s⁻¹/(1+s)·Vt³/3) ≤ 4.183 + 0.0331k`, close
`2.097 - 0.0331k ≤ 2π - 2k·asn v` (the `UKBRPFE_explicit` shape before the
`max 0` / `lfun 1` decoration). -/
private theorem p22_ukb_gen (k : ℕ) (v Vt s : ℝ)
    (hv : v = Real.cos 0.797 * Real.sin (Real.pi / k))
    (hvV : v ≤ Vt) (hv0 : 0 ≤ v) (hV0 : 0 ≤ Vt) (hV1 : Vt < 1)
    (hs : s ≤ Real.sqrt (1 - v ^ 2)) (hs0 : 0 < s)
    (hnum : (2:ℝ) * k * (Vt + s⁻¹ / (1 + s) * (Vt ^ 3 / 3)) ≤ 4.183 + 0.0331 * k) :
    (2.097 - 0.0331 * k : ℝ) ≤ 2 * Real.pi - 2 * k * asn v := by
  have hv1 : v < 1 := lt_of_le_of_lt hvV hV1
  have hub := p22_asn_le_add hv0 hv1
  have hv2lt : v ^ 2 < 1 := by
    have h : v * v ≤ v * 1 := mul_le_mul_of_nonneg_left hv1.le hv0
    calc v ^ 2 = v * v := by ring
      _ ≤ v * 1 := h
      _ = v := by ring
      _ < 1 := hv1
  have hRpos : 0 < Real.sqrt (1 - v ^ 2) := Real.sqrt_pos.mpr (by linarith [hv2lt])
  have hR : (Real.sqrt (1 - v ^ 2))⁻¹ / (1 + Real.sqrt (1 - v ^ 2)) ≤ s⁻¹ / (1 + s) := by
    have h1 : (Real.sqrt (1 - v ^ 2))⁻¹ ≤ s⁻¹ := (inv_le_inv₀ hRpos hs0).mpr hs
    have h2 : (1 + Real.sqrt (1 - v ^ 2))⁻¹ ≤ (1 + s)⁻¹ :=
      (inv_le_inv₀ (by linarith [hRpos]) (by linarith [hs0])).mpr (by linarith)
    calc (Real.sqrt (1 - v ^ 2))⁻¹ / (1 + Real.sqrt (1 - v ^ 2))
        = (Real.sqrt (1 - v ^ 2))⁻¹ * (1 + Real.sqrt (1 - v ^ 2))⁻¹ := by ring
      _ ≤ s⁻¹ * (1 + s)⁻¹ :=
          mul_le_mul h1 h2 (inv_nonneg.mpr (by linarith [hRpos]))
            (inv_nonneg.mpr (by linarith [hs0]))
      _ = s⁻¹ / (1 + s) := by ring
  have hv3 : v ^ 3 ≤ Vt ^ 3 := pow_le_pow_left₀ hv0 hvV 3
  have hcpos : 0 ≤ s⁻¹ / (1 + s) := div_nonneg (inv_nonneg.mpr hs0.le) (by linarith)
  have hv3ge : (0:ℝ) ≤ v ^ 3 := by
    calc (0:ℝ) ≤ v * (v * v) := mul_nonneg hv0 (mul_nonneg hv0 hv0)
      _ = v ^ 3 := by ring
  have hv3pos : 0 ≤ v ^ 3 / 3 := div_nonneg hv3ge (by norm_num)
  have hbound : v + (Real.sqrt (1 - v ^ 2))⁻¹ / (1 + Real.sqrt (1 - v ^ 2)) * (v ^ 3 / 3)
      ≤ Vt + s⁻¹ / (1 + s) * (Vt ^ 3 / 3) := by
    refine add_le_add hvV ?_
    calc (Real.sqrt (1 - v ^ 2))⁻¹ / (1 + Real.sqrt (1 - v ^ 2)) * (v ^ 3 / 3)
        ≤ s⁻¹ / (1 + s) * (v ^ 3 / 3) := mul_le_mul_of_nonneg_right hR hv3pos
      _ ≤ s⁻¹ / (1 + s) * (Vt ^ 3 / 3) :=
          mul_le_mul_of_nonneg_left (p22_div_le_div_right (by norm_num) hv3) hcpos
  have hkpos : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
  have hmul : 0 ≤ (2:ℝ) * k := mul_nonneg (by norm_num) hkpos
  have h1 : (2:ℝ) * k * asn v ≤ 4.183 + 0.0331 * k := by
    calc (2:ℝ) * k * asn v
        ≤ (2:ℝ) * k
            * (v + (Real.sqrt (1 - v ^ 2))⁻¹ / (1 + Real.sqrt (1 - v ^ 2)) * (v ^ 3 / 3)) :=
          mul_le_mul_of_nonneg_left hub hmul
      _ ≤ (2:ℝ) * k * (Vt + s⁻¹ / (1 + s) * (Vt ^ 3 / 3)) :=
          mul_le_mul_of_nonneg_left hbound hmul
      _ ≤ 4.183 + 0.0331 * k := hnum
  have hpi : (6.28:ℝ) ≤ 2 * Real.pi := by linarith [p22_pi_lb]
  linarith

/-- Finite-`k` preparation: with `s` a rational lower bound for `√(1 - Vt²)`,
`Vt := 0.6991·T(π/k)`, `T y = y - y³/6 + y⁵/120` the Taylor-5/rational window
of `v = cos 0.797·sin(π/k)` (using `π ∈ (3.14, 3.15)` termwise), produce
`v ≤ Vt`, `0 ≤ v` and `s ≤ √(1 - v²)`. -/
private theorem p22_ukb_pre (k : ℕ) (s : ℝ) (hk4 : 4 ≤ k) (hs0 : 0 < s)
    (hsle : s ^ 2 ≤ 1 - ((6991:ℝ) / 10000 * ((3.15:ℝ) / k
      - ((3.14:ℝ) / k) ^ 3 / 6 + ((3.15:ℝ) / k) ^ 5 / 120)) ^ 2) :
    Real.cos 0.797 * Real.sin (Real.pi / k)
      ≤ (6991:ℝ) / 10000 * ((3.15:ℝ) / k
          - ((3.14:ℝ) / k) ^ 3 / 6 + ((3.15:ℝ) / k) ^ 5 / 120)
      ∧ 0 ≤ Real.cos 0.797 * Real.sin (Real.pi / k)
      ∧ s ≤ Real.sqrt (1 - (Real.cos 0.797 * Real.sin (Real.pi / k)) ^ 2) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℕ) < 4) hk4
  have hy0 : 0 ≤ Real.pi / k := div_nonneg Real.pi_pos.le hkpos.le
  have hyU : Real.pi / k ≤ (3.15:ℝ) / k :=
    p22_div_le_div_nat_right hkpos (le_of_lt p22_pi_ub)
  have hyL : (3.14:ℝ) / k ≤ Real.pi / k :=
    p22_div_le_div_nat_right hkpos (le_of_lt p22_pi_lb)
  have hy4 : Real.pi / k ≤ 4 := by
    have h1 : (3.15:ℝ) / k ≤ (3.15:ℝ) / 4 :=
      p22_div_le_div_nat_left (by norm_num : (0:ℝ) ≤ 3.15) (by norm_num : (0:ℝ) < 4) hk4
    linarith
  have hsin : Real.sin (Real.pi / k)
      ≤ Real.pi / k - (Real.pi / k) ^ 3 / 6 + (Real.pi / k) ^ 5 / 120 :=
    p22_sin_le_taylor5 hy0 hy4
  have h30 : 0 ≤ (3.14:ℝ) / k := div_nonneg (by norm_num) hkpos.le
  have hy3L : ((3.14:ℝ) / k) ^ 3 ≤ (Real.pi / k) ^ 3 := pow_le_pow_left₀ h30 hyL 3
  have hy5U : (Real.pi / k) ^ 5 ≤ ((3.15:ℝ) / k) ^ 5 := pow_le_pow_left₀ hy0 hyU 5
  have hT : Real.pi / k - (Real.pi / k) ^ 3 / 6 + (Real.pi / k) ^ 5 / 120
      ≤ (3.15:ℝ) / k - ((3.14:ℝ) / k) ^ 3 / 6 + ((3.15:ℝ) / k) ^ 5 / 120 := by
    linarith
  have hsin0 : 0 ≤ Real.sin (Real.pi / k) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi hy0 ?_
    have h3 : Real.pi / k ≤ (3.15:ℝ) / 4 :=
      le_trans hyU (p22_div_le_div_nat_left (by norm_num : (0:ℝ) ≤ 3.15)
        (by norm_num : (0:ℝ) < 4) hk4)
    exact le_trans h3 (by linarith [p22_pi_lb])
  have hV : Real.cos 0.797 * Real.sin (Real.pi / k)
      ≤ (6991:ℝ) / 10000 * ((3.15:ℝ) / k
          - ((3.14:ℝ) / k) ^ 3 / 6 + ((3.15:ℝ) / k) ^ 5 / 120) := by
    calc Real.cos 0.797 * Real.sin (Real.pi / k)
        ≤ (6991:ℝ) / 10000 * Real.sin (Real.pi / k) :=
          mul_le_mul_of_nonneg_right p22_cc_le hsin0
      _ ≤ (6991:ℝ) / 10000
            * (Real.pi / k - (Real.pi / k) ^ 3 / 6 + (Real.pi / k) ^ 5 / 120) :=
          mul_le_mul_of_nonneg_left hsin (by norm_num)
      _ ≤ (6991:ℝ) / 10000
            * ((3.15:ℝ) / k - ((3.14:ℝ) / k) ^ 3 / 6 + ((3.15:ℝ) / k) ^ 5 / 120) :=
          mul_le_mul_of_nonneg_left hT (by norm_num)
  have hv0 : 0 ≤ Real.cos 0.797 * Real.sin (Real.pi / k) :=
    mul_nonneg (by linarith [p22_cc_lb]) hsin0
  refine ⟨hV, hv0, ?_⟩
  have hv2 : (Real.cos 0.797 * Real.sin (Real.pi / k)) ^ 2
      ≤ ((6991:ℝ) / 10000 * ((3.15:ℝ) / k
          - ((3.14:ℝ) / k) ^ 3 / 6 + ((3.15:ℝ) / k) ^ 5 / 120)) ^ 2 :=
    pow_le_pow_left₀ hv0 hV 2
  have hss : s ^ 2 ≤ 1 - (Real.cos 0.797 * Real.sin (Real.pi / k)) ^ 2 := by
    linarith [hsle, hv2]
  calc s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs0.le).symm
    _ ≤ Real.sqrt (1 - (Real.cos 0.797 * Real.sin (Real.pi / k)) ^ 2) :=
        Real.sqrt_le_sqrt hss

/-- `k ≥ 12` case: `sin y ≤ y` suffices (no Taylor), `v ≤ 2.205/k ≤ 2.205/12`,
uniform window `s = 0.98`; margin ≈ 0.145 at `k = 12`, growing in `k`. -/
private theorem p22_ukb_hi (k : ℕ) (hk : 12 ≤ k) :
    (2.097 - 0.0331 * k : ℝ) ≤
      2 * Real.pi - 2 * k * asn (Real.cos 0.797 * Real.sin (Real.pi / k)) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℕ) < 12) hk
  have hk12 : (12:ℝ) ≤ k := by exact_mod_cast hk
  have hy0 : 0 ≤ Real.pi / k := div_nonneg Real.pi_pos.le hkpos.le
  have hyU : Real.pi / k ≤ (3.15:ℝ) / k :=
    p22_div_le_div_nat_right hkpos (le_of_lt p22_pi_ub)
  have hy4 : Real.pi / k ≤ 4 := by
    have h1 : Real.pi / k ≤ (3.15:ℝ) / 12 := le_trans hyU
      (p22_div_le_div_nat_left (by norm_num : (0:ℝ) ≤ 3.15) (by norm_num : (0:ℝ) < 12) hk)
    linarith
  have hsinle : Real.sin (Real.pi / k) ≤ Real.pi / k := by
    have hT := p22_sin_le_taylor5 hy0 hy4
    have hy2 : (Real.pi / k) ^ 2 ≤ 16 := by nlinarith [hy4, hy0]
    have hy3 : (0:ℝ) ≤ (Real.pi / k) ^ 3 := by nlinarith [hy0]
    have hy5 : (Real.pi / k) ^ 5 ≤ 16 * (Real.pi / k) ^ 3 := by
      calc (Real.pi / k) ^ 5 = (Real.pi / k) ^ 3 * (Real.pi / k) ^ 2 := by ring
        _ ≤ (Real.pi / k) ^ 3 * 16 := mul_le_mul_of_nonneg_left hy2 hy3
        _ = 16 * (Real.pi / k) ^ 3 := by ring
    linarith
  have hsin0 : 0 ≤ Real.sin (Real.pi / k) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi hy0 ?_
    have h3 : Real.pi / k ≤ (3.15:ℝ) / 12 := le_trans hyU
      (p22_div_le_div_nat_left (by norm_num : (0:ℝ) ≤ 3.15) (by norm_num : (0:ℝ) < 12) hk)
    exact le_trans h3 (by linarith [p22_pi_lb])
  have hv0 : 0 ≤ Real.cos 0.797 * Real.sin (Real.pi / k) :=
    mul_nonneg (by linarith [p22_cc_lb]) hsin0
  have hvA : Real.cos 0.797 * Real.sin (Real.pi / k) ≤ (7:ℝ) / 10 * 3.15 / k := by
    have hcc : Real.cos 0.797 ≤ 7 / 10 := le_trans p22_cc_le (by norm_num)
    calc Real.cos 0.797 * Real.sin (Real.pi / k)
        ≤ (7:ℝ) / 10 * Real.sin (Real.pi / k) :=
          mul_le_mul_of_nonneg_right hcc hsin0
      _ ≤ (7:ℝ) / 10 * (Real.pi / k) :=
          mul_le_mul_of_nonneg_left hsinle (by norm_num)
      _ ≤ (7:ℝ) / 10 * ((3.15:ℝ) / k) :=
          mul_le_mul_of_nonneg_left hyU (by norm_num)
      _ = (7:ℝ) / 10 * 3.15 / k := by ring
  have hv2 : (Real.cos 0.797 * Real.sin (Real.pi / k)) ^ 2
      ≤ ((7:ℝ) / 10 * 3.15 / 12) ^ 2 := by
    refine pow_le_pow_left₀ hv0 ?_ 2
    exact le_trans hvA
      (p22_div_le_div_nat_left (by norm_num : (0:ℝ) ≤ (7:ℝ) / 10 * 3.15)
        (by norm_num : (0:ℝ) < 12) hk)
  have hsq : ((49:ℝ) / 50) ^ 2
      ≤ 1 - (Real.cos 0.797 * Real.sin (Real.pi / k)) ^ 2 := by
    have hnum : ((49:ℝ) / 50) ^ 2 ≤ 1 - ((7:ℝ) / 10 * 3.15 / 12) ^ 2 := by norm_num
    linarith [hnum, hv2]
  have hsQ : (49:ℝ) / 50 ≤
      Real.sqrt (1 - (Real.cos 0.797 * Real.sin (Real.pi / k)) ^ 2) := by
    calc (49:ℝ) / 50 = Real.sqrt (((49:ℝ) / 50) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (1 - (Real.cos 0.797 * Real.sin (Real.pi / k)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
  have hV0 : 0 ≤ (7:ℝ) / 10 * 3.15 / k := div_nonneg (by norm_num) hkpos.le
  have hV1 : (7:ℝ) / 10 * 3.15 / k < 1 :=
    (div_lt_one hkpos).mpr
      (lt_of_lt_of_le (by norm_num : (7:ℝ) / 10 * 3.15 < 12) hk12)
  refine p22_ukb_gen k (Real.cos 0.797 * Real.sin (Real.pi / k))
    ((7:ℝ) / 10 * 3.15 / k) (49 / 50) rfl hvA hv0 hV0 hV1 hsQ (by norm_num) ?_
  · have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
    have hsplit : (2:ℝ) * k * ((7:ℝ) / 10 * 3.15 / k
        + (49 / 50)⁻¹ / (1 + 49 / 50) * (((7:ℝ) / 10 * 3.15 / k) ^ 3 / 3))
        = 2 * ((7:ℝ) / 10 * 3.15)
          + (49 / 50)⁻¹ / (1 + 49 / 50)
            * (2 * ((7:ℝ) / 10 * 3.15) ^ 3 / (3 * (k:ℝ) ^ 2)) := by
      field_simp
    have hk2 : (144:ℝ) ≤ (k:ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 12) hk12 2
      norm_num at h
      linarith
    have hbound2 : (49 / 50)⁻¹ / (1 + 49 / 50)
            * (2 * ((7:ℝ) / 10 * 3.15) ^ 3 / (3 * (k:ℝ) ^ 2))
        ≤ (49 / 50)⁻¹ / (1 + 49 / 50)
            * (2 * ((7:ℝ) / 10 * 3.15) ^ 3 / (3 * 144)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact p22_div_le_div_real_left (by positivity) (by positivity)
        (by linarith [hk2] : (3:ℝ) * 144 ≤ 3 * (k:ℝ) ^ 2)
    rw [hsplit]
    have hfin : (2:ℝ) * ((7:ℝ) / 10 * 3.15)
        + (49 / 50)⁻¹ / (1 + 49 / 50) * (2 * ((7:ℝ) / 10 * 3.15) ^ 3 / (3 * 144))
        ≤ 4.183 + 0.0331 * 12 := by norm_num
    have hlin : ((0.0331:ℝ) * ((12:ℕ):ℝ) ≤ (0.0331:ℝ) * (k:ℝ)) := by
      linarith [hk12]
    linarith

/-! ## finite cases `k = 4, ..., 11` (base3 template, per-k windows) -/

private theorem p22_ukb_base4 : (2.097 - 0.0331 * 4 : ℝ)
    ≤ 2 * Real.pi - 2 * 4 * asn (Real.cos 0.797 * Real.sin (Real.pi / 4)) := by
  have hpre := p22_ukb_pre 4 ((43:ℝ) / 50) (by norm_num) (by norm_num) (by norm_num)
  refine p22_ukb_gen 4 (Real.cos 0.797 * Real.sin (Real.pi / 4))
    ((6991:ℝ) / 10000 * ((3.15:ℝ) / 4 - ((3.14:ℝ) / 4) ^ 3 / 6 + ((3.15:ℝ) / 4) ^ 5 / 120))
    ((43:ℝ) / 50) rfl hpre.1 hpre.2.1 (by norm_num) (by norm_num) hpre.2.2 (by norm_num) ?_
  norm_num

private theorem p22_ukb_base5 : (2.097 - 0.0331 * 5 : ℝ)
    ≤ 2 * Real.pi - 2 * 5 * asn (Real.cos 0.797 * Real.sin (Real.pi / 5)) := by
  have hpre := p22_ukb_pre 5 ((91:ℝ) / 100) (by norm_num) (by norm_num) (by norm_num)
  refine p22_ukb_gen 5 (Real.cos 0.797 * Real.sin (Real.pi / 5))
    ((6991:ℝ) / 10000 * ((3.15:ℝ) / 5 - ((3.14:ℝ) / 5) ^ 3 / 6 + ((3.15:ℝ) / 5) ^ 5 / 120))
    ((91:ℝ) / 100) rfl hpre.1 hpre.2.1 (by norm_num) (by norm_num) hpre.2.2 (by norm_num) ?_
  norm_num

private theorem p22_ukb_base6 : (2.097 - 0.0331 * 6 : ℝ)
    ≤ 2 * Real.pi - 2 * 6 * asn (Real.cos 0.797 * Real.sin (Real.pi / 6)) := by
  have hpre := p22_ukb_pre 6 ((93:ℝ) / 100) (by norm_num) (by norm_num) (by norm_num)
  refine p22_ukb_gen 6 (Real.cos 0.797 * Real.sin (Real.pi / 6))
    ((6991:ℝ) / 10000 * ((3.15:ℝ) / 6 - ((3.14:ℝ) / 6) ^ 3 / 6 + ((3.15:ℝ) / 6) ^ 5 / 120))
    ((93:ℝ) / 100) rfl hpre.1 hpre.2.1 (by norm_num) (by norm_num) hpre.2.2 (by norm_num) ?_
  norm_num

private theorem p22_ukb_base7 : (2.097 - 0.0331 * 7 : ℝ)
    ≤ 2 * Real.pi - 2 * 7 * asn (Real.cos 0.797 * Real.sin (Real.pi / 7)) := by
  have hpre := p22_ukb_pre 7 ((19:ℝ) / 20) (by norm_num) (by norm_num) (by norm_num)
  refine p22_ukb_gen 7 (Real.cos 0.797 * Real.sin (Real.pi / 7))
    ((6991:ℝ) / 10000 * ((3.15:ℝ) / 7 - ((3.14:ℝ) / 7) ^ 3 / 6 + ((3.15:ℝ) / 7) ^ 5 / 120))
    ((19:ℝ) / 20) rfl hpre.1 hpre.2.1 (by norm_num) (by norm_num) hpre.2.2 (by norm_num) ?_
  norm_num

private theorem p22_ukb_base8 : (2.097 - 0.0331 * 8 : ℝ)
    ≤ 2 * Real.pi - 2 * 8 * asn (Real.cos 0.797 * Real.sin (Real.pi / 8)) := by
  have hpre := p22_ukb_pre 8 ((24:ℝ) / 25) (by norm_num) (by norm_num) (by norm_num)
  refine p22_ukb_gen 8 (Real.cos 0.797 * Real.sin (Real.pi / 8))
    ((6991:ℝ) / 10000 * ((3.15:ℝ) / 8 - ((3.14:ℝ) / 8) ^ 3 / 6 + ((3.15:ℝ) / 8) ^ 5 / 120))
    ((24:ℝ) / 25) rfl hpre.1 hpre.2.1 (by norm_num) (by norm_num) hpre.2.2 (by norm_num) ?_
  norm_num

private theorem p22_ukb_base9 : (2.097 - 0.0331 * 9 : ℝ)
    ≤ 2 * Real.pi - 2 * 9 * asn (Real.cos 0.797 * Real.sin (Real.pi / 9)) := by
  have hpre := p22_ukb_pre 9 ((97:ℝ) / 100) (by norm_num) (by norm_num) (by norm_num)
  refine p22_ukb_gen 9 (Real.cos 0.797 * Real.sin (Real.pi / 9))
    ((6991:ℝ) / 10000 * ((3.15:ℝ) / 9 - ((3.14:ℝ) / 9) ^ 3 / 6 + ((3.15:ℝ) / 9) ^ 5 / 120))
    ((97:ℝ) / 100) rfl hpre.1 hpre.2.1 (by norm_num) (by norm_num) hpre.2.2 (by norm_num) ?_
  norm_num

private theorem p22_ukb_base10 : (2.097 - 0.0331 * 10 : ℝ)
    ≤ 2 * Real.pi - 2 * 10 * asn (Real.cos 0.797 * Real.sin (Real.pi / 10)) := by
  have hpre := p22_ukb_pre 10 ((97:ℝ) / 100) (by norm_num) (by norm_num) (by norm_num)
  refine p22_ukb_gen 10 (Real.cos 0.797 * Real.sin (Real.pi / 10))
    ((6991:ℝ) / 10000 * ((3.15:ℝ) / 10 - ((3.14:ℝ) / 10) ^ 3 / 6 + ((3.15:ℝ) / 10) ^ 5 / 120))
    ((97:ℝ) / 100) rfl hpre.1 hpre.2.1 (by norm_num) (by norm_num) hpre.2.2 (by norm_num) ?_
  norm_num

private theorem p22_ukb_base11 : (2.097 - 0.0331 * 11 : ℝ)
    ≤ 2 * Real.pi - 2 * 11 * asn (Real.cos 0.797 * Real.sin (Real.pi / 11)) := by
  have hpre := p22_ukb_pre 11 ((49:ℝ) / 50) (by norm_num) (by norm_num) (by norm_num)
  refine p22_ukb_gen 11 (Real.cos 0.797 * Real.sin (Real.pi / 11))
    ((6991:ℝ) / 10000 * ((3.15:ℝ) / 11 - ((3.14:ℝ) / 11) ^ 3 / 6 + ((3.15:ℝ) / 11) ^ 5 / 120))
    ((49:ℝ) / 50) rfl hpre.1 hpre.2.1 (by norm_num) (by norm_num) hpre.2.2 (by norm_num) ?_
  norm_num


/-! ## BIEFJHU numeric kit (PA22f wave): algebraic h-reduction + polynomial `asn` majorants. -/

/-- auxiliary: `T h` = the spherical-cap cosine parameter of `BIEFJHU_explicit`. -/
private noncomputable def p22_bjf_T (h : ℝ) : ℝ :=
  h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2

private theorem p22_bjf_T1 : p22_bjf_T 1 = sqrt3 / 2 := by
  unfold p22_bjf_T sqrt3
  have h34 : (1:ℝ) - (1/2)^2 = 3/4 := by norm_num
  rw [h34, Real.sqrt_div (x := (3:ℝ)) (by norm_num)]
  ring

private theorem p22_bjf_Tdiff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    p22_bjf_T b - p22_bjf_T a
      = (b - a) * (sqrt3 / 4)
        - (Real.sqrt (1 - (a / 2) ^ 2) - Real.sqrt (1 - (b / 2) ^ 2)) / 2 := by
  unfold p22_bjf_T sqrt3
  ring

/-- cos-representation: `T h = cos(π/3 - arcsin(h/2))`. -/
private theorem p22_bjf_Tcos (h : ℝ) (hh : 0 ≤ h) (h1 : h ≤ 2) :
    p22_bjf_T h = Real.cos (Real.pi / 3 - Real.arcsin (h / 2)) := by
  unfold p22_bjf_T sqrt3
  rw [Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three,
    Real.cos_arcsin, Real.sin_arcsin (by linarith) (by linarith)]
  ring

/-- `T` is increasing on `[1, h0]`. -/
private theorem p22_bjf_Tmono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ h0) :
    p22_bjf_T a ≤ p22_bjf_T b := by
  have ha0 : (0:ℝ) ≤ a := le_trans (by norm_num) ha
  have hb0 : (0:ℝ) ≤ b := le_trans ha0 hab
  have hab2 : a / 2 ≤ b / 2 := by linarith
  have h126 : (h0:ℝ) = 126 / 100 := by norm_num [h0]
  have hble : (b:ℝ) ≤ 126 / 100 := by
    have h126b : (h0:ℝ) = 126 / 100 := h126
    have hb2 : (b:ℝ) ≤ h0 := hb
    rw [h126b] at hb2
    exact hb2
  have hsqrt3ge : (433:ℝ)/250 ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hrange : ∀ x : ℝ, 1 ≤ x → x ≤ h0 →
      0 ≤ Real.pi / 3 - Real.arcsin (x / 2)
      ∧ Real.pi / 3 - Real.arcsin (x / 2) ≤ Real.pi := by
    intro x hx1 hxh
    have hxi : (x:ℝ) ≤ 126 / 100 := by
      have h126x : (h0:ℝ) = 126 / 100 := h126
      have hx2 : (x:ℝ) ≤ h0 := hxh
      rw [h126x] at hx2
      exact hx2
    have hx2 : x / 2 ≤ Real.sqrt 3 / 2 := by
      have h1 : (x:ℝ)/2 ≤ 63 / 100 := by linarith
      have h2 : (433:ℝ)/500 ≤ Real.sqrt 3 / 2 := by linarith [hsqrt3ge]
      linarith
    have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
    have hpi32 : Real.pi / 3 ≤ Real.pi / 2 := by linarith
    have hasin : Real.arcsin (x / 2) ≤ Real.pi / 3 := by
      refine le_trans (Real.arcsin_le_arcsin hx2) ?_
      have h3 : Real.arcsin (Real.sin (Real.pi / 3)) = Real.pi / 3 :=
        Real.arcsin_sin (by linarith) (by linarith)
      rw [Real.sin_pi_div_three] at h3
      rw [h3]
    constructor
    · have h4 : (0:ℝ) ≤ Real.arcsin (x / 2) := Real.arcsin_nonneg.mpr (by linarith)
      linarith [hasin, h4]
    · have h4b : (0:ℝ) ≤ Real.arcsin (x / 2) := Real.arcsin_nonneg.mpr (by linarith)
      have h5 : Real.arcsin (x / 2) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
      linarith [h5, h4b, Real.pi_pos]
  have hxeq : p22_bjf_T a = Real.cos (Real.pi / 3 - Real.arcsin (a / 2)) :=
    p22_bjf_Tcos a ha0 (by linarith [h126, hble])
  have hbeq : p22_bjf_T b = Real.cos (Real.pi / 3 - Real.arcsin (b / 2)) :=
    p22_bjf_Tcos b hb0 (by linarith [h126, hble])
  rw [hxeq, hbeq]
  refine Real.cos_le_cos_of_nonneg_of_le_pi ?_ ?_ ?_
  · exact (hrange b (le_trans ha hab) hb).1
  · exact (hrange a ha (le_trans hab hb)).2
  · have h1 : Real.arcsin (a / 2) ≤ Real.arcsin (b / 2) := Real.arcsin_le_arcsin hab2
    linarith

/-- sqrt-subtraction identity used by the chord bounds. -/
private theorem p22_bjf_sqrtAB (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hpos : 0 < Real.sqrt x + Real.sqrt y) :
    Real.sqrt x - Real.sqrt y = (x - y) / (Real.sqrt x + Real.sqrt y) := by
  have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
  have h2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy
  rw [eq_div_iff (ne_of_gt hpos)]
  nlinarith [h1, h2]

/-- quadratic majorant: `asn w ≤ w+w³/6+w⁵/10` for `w² ≤ 17/64`. -/
private theorem p22_bjf_asn_quad {w : ℝ} (hw : 0 ≤ w) (hwu : w ^ 2 ≤ 17 / 64) :
    asn w ≤ w + w ^ 3 / 6 + w ^ 5 / 10 := by
  show Real.arcsin w ≤ _
  have hdom : ∀ t ∈ Set.Icc (0:ℝ) w,
      1 / Real.sqrt (1 - t ^ 2) ≤ 1 + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) := by
    intro t ht
    obtain ⟨ht0, htw⟩ := ht
    have hu : t ^ 2 ≤ (17:ℝ) / 64 := by nlinarith
    have hu0 : (0:ℝ) ≤ t ^ 2 := sq_nonneg t
    have hQ : 0 < 1 - t ^ 2 := by nlinarith
    have hu2 : t ^ 4 ≤ ((17:ℝ)/64) ^ 2 := by nlinarith
    have hu3 : t ^ 6 ≤ ((17:ℝ)/64) ^ 3 := by nlinarith
    have hcert : 1 - 3 * t ^ 2 - t ^ 4 - t ^ 6 ≥ 0 := by linarith
    have hkey : (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2 * (1 - t ^ 2) ≥ 1 := by
      have hex : (1 + (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4) ^ 2 * (1 - t ^ 2)
          = 1 + t ^ 4 * (1 - 3 * t ^ 2 - t ^ 4 - t ^ 6) / 4 := by ring
      rw [hex]
      exact le_add_of_nonneg_right
        (div_nonneg (mul_nonneg (by nlinarith [hu0]) hcert) (by norm_num : (0:ℝ) ≤ 4))
    exact (div_le_iff₀ hQ).mpr (by nlinarith [hkey, hP, hge])
  have hcpol : ContinuousOn (fun t : ℝ => 1 - t ^ 2) (Set.uIcc (0:ℝ) w) := by fun_prop
  have hcon : ContinuousOn (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2))
      (Set.uIcc (0:ℝ) w) := by
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_sqrt.comp_continuousOn hcpol) ?_
    intro t ht
    rw [Set.uIcc_of_le hw] at ht
    obtain ⟨ht0, htw⟩ := ht
    have hp : (0:ℝ) < 1 - t ^ 2 := by nlinarith
    simpa using ne_of_gt (Real.sqrt_pos.mpr hp)
  have hint : ∫ t in (0:ℝ)..w, 1 / Real.sqrt (1 - t ^ 2) = asn w := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) w, HasDerivAt asn (1 / Real.sqrt (1 - t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le hw] at ht
      obtain ⟨ht0, htw⟩ := ht
      exact Real.hasDerivAt_arcsin (x := t) (by nlinarith) (by nlinarith)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcon.intervalIntegrable]
    simp [asn, Real.arcsin_zero]
  have hbase : IntervalIntegrable (fun t : ℝ => t ^ 2) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun t : ℝ => t ^ 2) (Set.uIcc (0:ℝ) w))
  have hbase4 : IntervalIntegrable (fun t : ℝ => t ^ 4) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun t : ℝ => t ^ 4) (Set.uIcc (0:ℝ) w))
  have hc1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume (0:ℝ) w :=
    ContinuousOn.intervalIntegrable (by
      fun_prop : ContinuousOn (fun _ : ℝ => (1:ℝ)) (Set.uIcc (0:ℝ) w))
  have hI2 : IntervalIntegrable (fun t : ℝ =>
      (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)) MeasureTheory.volume (0:ℝ) w :=
    hc1.add ((hbase.const_mul (1/2)).add (hbase4.const_mul (1/2)))
  have hmono := intervalIntegral.integral_mono_on (by nlinarith) hcon.intervalIntegrable
    hI2 hdom
  have hpow : ∫ t in (0:ℝ)..w, (1:ℝ) + ((1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)
      = w + w ^ 3 / 6 + w ^ 5 / 10 := by
    rw [intervalIntegral.integral_add hc1
      (show IntervalIntegrable (fun t : ℝ => (1:ℝ)/2 * t ^ 2 + (1:ℝ)/2 * t ^ 4)
        MeasureTheory.volume (0:ℝ) w from (hbase.const_mul (1/2)).add (hbase4.const_mul (1/2))),
      intervalIntegral.integral_add (hbase.const_mul (1/2)) (hbase4.const_mul (1/2)),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
    ring
  rw [hint] at hmono
  rw [hpow] at hmono
  exact hmono

/-- HOL `BIEFJHU_explicit` (counting_spheres.hl:965). GIANT.
Scout note (PA22d, 不强攻): the UKBRPFE chain above does NOT lift to the
`h ∈ [1, h0]` radius here - the `asn` window `s` degrades with `h` and the
`max 0` clipping needs its own treatment.  Next wave keeps this `sorry`.
Scout upgrade (PA22e, 预研产出, NEEDS route design for the owning wave):
(a) `h`-reduction kills the degradation concern: `th h = h*sqrt3/4 +
    sqrt(1-(h/2)^2)/2` is increasing on `[1, h0]` (`th' h = sqrt3/4 -
    h/(4*sqrt(1-(h/2)^2)) >= 0 iff h^2 <= 12/7`; `h0^2 = 1.5876 < 12/7`),
    while `0.591 - 0.0331*k + 0.506*lfun h` is largest at `h = 1`
    (`lfun h <= 1` there).  So it suffices to prove the one-parameter window
    `1.097 - 0.0331*k <= max 0 (2π - 2k*asn(√3/2 * sin(π/k)))` for `k ≥ 3`.
    The `max 0` clip never binds: the area decreases to its k→∞ limit
    `2π(1 - √3/2) ≈ 0.8418 > 0` (min over `k ≥ 3` at `h = 1`).
(b) True-gap margins at `h = 1` (float scout): k=3 0.1971, k=4 0.0461,
    k=5 0.0110 (worst), k=6 0.0108, k=7 0.0249, then growing; `k ≥ 34` is
    trivial since the LHS `0.591 - 0.0331*k + 0.506*lfun h < 0`.
(c) Window choice per k (asn-unit budgets `margin/(2k·√(1-w²))`):
    the `p22_asn_le_add` cubic chord window works at k = 3 (overshoot
    0.0299 <= budget 0.0497) and k = 6 (0.00097 <= 0.000998) but FAILS at
    k = 4 (0.00739 > 0.00729) and k = 5 (0.00242 > 0.00110).  Prescription:
    for k >= 5 use the quadratic majorant `asn w <= w + w^3/6 + w^5/10`,
    valid while `3u + u^2 + u^3 <= 1` for `u = w^2` (window `u <= 17/64`
    covers `w <= 0.5091`; certificate `(1+u/2+u^2/2)^2*(1-u)-1 =
    u^2*(1-3u-u^2-u^3)/4 >= 0`, exact `11/4096` at `u = 1/4`); overshoot
    0.00037 <= budget at k = 5.  For k = 4 split the chord interval at `w/2`
    (overshoot drops ~4x) or use the alternating `arcsin` series (term ratio
    `w^2*(2n+1)/(2n+2) < 1`, decreasing terms on the whole window).  -/
theorem BIEFJHU_explicit (h : ℝ) (k : ℕ) (hpa : packIneqDefAP22)
    (hh : 1 ≤ h ∧ h ≤ h0) (hk : 3 ≤ k) :
    (0.591 - 0.0331 * k + 0.506 * lfun h) ≤
      max 0 (regularSphericalPolygonAreaP22
        (h * sqrt3 / 4 + Real.sqrt (1 - (h / 2) ^ 2) / 2) k) := by
  sorry

/-- HOL `UKBRPFE_explicit` (counting_spheres.hl:999). Filled (PA22d wave).
Erratum record (kept for the log): the gap function
`g x := 2π - 2x·asn(cos 0.797·sin(π/x)) - 2.097 + 0.0331x` is NOT monotone on
`[3,∞)` (it dips until x ≈ 9.3; min gap ≈ 0.137 at k = 9) - the PA22b plan
"k ≥ 7 monotone extension" was wrong.  Route taken: (a) `k ∈ {4..11}` finite
cases by the base3 template, one rational window per `k`
(`p22_ukb_base4..p22_ukb_base11`); (b) `k ≥ 12` closed directly without the
planned derivative machinery: `sin y ≤ y` + `p22_asn_le_add` with
`v ≤ 2.205/k ≤ 2.205/12` and window `s = 0.98` (`p22_ukb_hi`; margin ≈ 0.145
at k = 12, growing in `k`). -/
theorem UKBRPFE_explicit (k : ℕ) (hpa : packIneqDefAP22) (hk : 3 ≤ k) :
    (0.591 - 0.0331 * k + 0.506 * lfun 1 + 1) ≤
      max 0 (regularSphericalPolygonAreaP22 (Real.cos 0.797) k) := by
  have hlf : (0.506 * lfun 1 : ℝ) = 0.506 := by
    have h1 : lfun (1:ℝ) = 1 := by norm_num [lfun, h0]
    rw [h1]; norm_num
  rcases Nat.lt_or_ge k 12 with h12 | hge
  · interval_cases k
    · exact p22_ukb3
    · rw [hlf,
        show regularSphericalPolygonAreaP22 (Real.cos 0.797) 4
          = 2 * Real.pi - 2 * 4 * asn (Real.cos 0.797 * Real.sin (Real.pi / 4)) from rfl]
      have hnum : (0.591:ℝ) - 0.0331 * ((4:ℕ):ℝ) + 0.506 + 1 = 2.097 - 0.0331 * 4 := by
        norm_num
      rw [hnum]
      exact le_trans p22_ukb_base4 (le_max_right _ _)
    · rw [hlf,
        show regularSphericalPolygonAreaP22 (Real.cos 0.797) 5
          = 2 * Real.pi - 2 * 5 * asn (Real.cos 0.797 * Real.sin (Real.pi / 5)) from rfl]
      have hnum : (0.591:ℝ) - 0.0331 * ((5:ℕ):ℝ) + 0.506 + 1 = 2.097 - 0.0331 * 5 := by
        norm_num
      rw [hnum]
      exact le_trans p22_ukb_base5 (le_max_right _ _)
    · rw [hlf,
        show regularSphericalPolygonAreaP22 (Real.cos 0.797) 6
          = 2 * Real.pi - 2 * 6 * asn (Real.cos 0.797 * Real.sin (Real.pi / 6)) from rfl]
      have hnum : (0.591:ℝ) - 0.0331 * ((6:ℕ):ℝ) + 0.506 + 1 = 2.097 - 0.0331 * 6 := by
        norm_num
      rw [hnum]
      exact le_trans p22_ukb_base6 (le_max_right _ _)
    · rw [hlf,
        show regularSphericalPolygonAreaP22 (Real.cos 0.797) 7
          = 2 * Real.pi - 2 * 7 * asn (Real.cos 0.797 * Real.sin (Real.pi / 7)) from rfl]
      have hnum : (0.591:ℝ) - 0.0331 * ((7:ℕ):ℝ) + 0.506 + 1 = 2.097 - 0.0331 * 7 := by
        norm_num
      rw [hnum]
      exact le_trans p22_ukb_base7 (le_max_right _ _)
    · rw [hlf,
        show regularSphericalPolygonAreaP22 (Real.cos 0.797) 8
          = 2 * Real.pi - 2 * 8 * asn (Real.cos 0.797 * Real.sin (Real.pi / 8)) from rfl]
      have hnum : (0.591:ℝ) - 0.0331 * ((8:ℕ):ℝ) + 0.506 + 1 = 2.097 - 0.0331 * 8 := by
        norm_num
      rw [hnum]
      exact le_trans p22_ukb_base8 (le_max_right _ _)
    · rw [hlf,
        show regularSphericalPolygonAreaP22 (Real.cos 0.797) 9
          = 2 * Real.pi - 2 * 9 * asn (Real.cos 0.797 * Real.sin (Real.pi / 9)) from rfl]
      have hnum : (0.591:ℝ) - 0.0331 * ((9:ℕ):ℝ) + 0.506 + 1 = 2.097 - 0.0331 * 9 := by
        norm_num
      rw [hnum]
      exact le_trans p22_ukb_base9 (le_max_right _ _)
    · rw [hlf,
        show regularSphericalPolygonAreaP22 (Real.cos 0.797) 10
          = 2 * Real.pi - 2 * 10 * asn (Real.cos 0.797 * Real.sin (Real.pi / 10)) from rfl]
      have hnum : (0.591:ℝ) - 0.0331 * ((10:ℕ):ℝ) + 0.506 + 1 = 2.097 - 0.0331 * 10 := by
        norm_num
      rw [hnum]
      exact le_trans p22_ukb_base10 (le_max_right _ _)
    · rw [hlf,
        show regularSphericalPolygonAreaP22 (Real.cos 0.797) 11
          = 2 * Real.pi - 2 * 11 * asn (Real.cos 0.797 * Real.sin (Real.pi / 11)) from rfl]
      have hnum : (0.591:ℝ) - 0.0331 * ((11:ℕ):ℝ) + 0.506 + 1 = 2.097 - 0.0331 * 11 := by
        norm_num
      rw [hnum]
      exact le_trans p22_ukb_base11 (le_max_right _ _)
  · rw [hlf,
      show (0.591:ℝ) - 0.0331 * k + 0.506 + 1 = 2.097 - 0.0331 * k from by linarith,
      show regularSphericalPolygonAreaP22 (Real.cos 0.797) k
        = 2 * Real.pi - 2 * k * asn (Real.cos 0.797 * Real.sin (Real.pi / k)) from rfl]
    exact le_trans (p22_ukb_hi k hge) (le_max_right _ _)


/-- HOL `DLWCHEM_sum` (counting_spheres.hl:1020). Filled (PA22e wave).
Per-term `BIEFJHU_explicit` + `Finset.sum_le_sum`, linear decomposition
`∑ (0.591 - 0.0331·k i + 0.506·lfun (h i)) = 0.591·n - 0.0331·∑k + 0.506·∑lfun`,
then the counting window `0.3924·n + 6.4692 ≤ 4π` fails at `n ≥ 16` (exact
rational margin `453/2500 = 0.1812` over `4·3.1416`; `Real.pi_lt_d4`).
NEEDS: the proof consumes `BIEFJHU_explicit`, which is still `sorry` - the
`sorryAx` dependency is upstream (per-item numerical wave), not in this sum
layer; closing BIEFJHU closes this theorem for free. -/
theorem DLWCHEM_sum (h : ℕ → ℝ) (k : ℕ → ℕ) (n : ℕ) (hpa : packIneqDefAP22)
    (hn : 12 < n)
    (hik : ∀ i : ℕ, i < n → 3 ≤ k i ∧ 1 ≤ h i ∧ h i ≤ h0)
    (hksum : ∑ i ∈ Finset.range n, k i ≤ 6 * n - 12)
    (hasum : ∑ i ∈ Finset.range n,
        max 0 (regularSphericalPolygonAreaP22
          (h i * sqrt3 / 4 + Real.sqrt (1 - (h i / 2) ^ 2) / 2) (k i)) ≤ 4 * Real.pi)
    (hlsum : 12 < ∑ i ∈ Finset.range n, lfun (h i)) : n < 16 := by
  by_contra hge
  have hn16 : 16 ≤ n := by omega
  have hnc : ((16:ℝ)) ≤ (n : ℝ) := by exact_mod_cast hn16
  -- per-term BIEFJHU
  have hterm : ∀ i ∈ Finset.range n, (0.591 - 0.0331 * (k i : ℝ) + 0.506 * lfun (h i)) ≤
      max 0 (regularSphericalPolygonAreaP22
        (h i * sqrt3 / 4 + Real.sqrt (1 - (h i / 2) ^ 2) / 2) (k i)) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    exact BIEFJHU_explicit (h i) (k i) hpa ⟨(hik i hin).2.1, (hik i hin).2.2⟩ (hik i hin).1
  have hsumle := Finset.sum_le_sum hterm
  -- decompose the linear-in-(k, lfun) sum
  have hsplit : ∑ i ∈ Finset.range n, (0.591 - 0.0331 * (k i : ℝ) + 0.506 * lfun (h i))
      = (0.591:ℝ) * n - 0.0331 * ((∑ i ∈ Finset.range n, k i : ℕ) : ℝ)
        + 0.506 * (∑ i ∈ Finset.range n, lfun (h i)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum (s := Finset.range n) (f := fun i => (k i : ℝ)) (a := (0.0331:ℝ)),
      ← Finset.mul_sum (s := Finset.range n) (f := fun i => lfun (h i)) (a := (0.506:ℝ)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Nat.cast_sum]
    ring
  have hka : ((∑ i ∈ Finset.range n, k i : ℕ) : ℝ) ≤ (6:ℝ) * n - 12 := by
    have h12 : (12:ℕ) ≤ 6 * n := by omega
    have h2 : ((∑ i ∈ Finset.range n, k i : ℕ) : ℝ) ≤ ((6 * n - 12 : ℕ) : ℝ) := by
      exact_mod_cast hksum
    rw [Nat.cast_sub h12, Nat.cast_mul] at h2
    simpa only [Nat.cast_ofNat] using h2
  have hkey : (0.591:ℝ) * n - 0.0331 * (6 * n - 12) + 0.506 * 12 ≤ 4 * Real.pi := by
    linarith
  have hmono : (0.591:ℝ) * 16 - 0.0331 * (6 * 16 - 12)
      ≤ 0.591 * n - 0.0331 * (6 * n - 12) := by linarith
  have hnum : (0.591:ℝ) * 16 - 0.0331 * (6 * 16 - 12) + 0.506 * 12 = 12.7476 := by norm_num
  have hpi : (4:ℝ) * Real.pi < 12.5664 := by
    have h := Real.pi_lt_d4
    linarith
  linarith

/-- HOL `XULJEPR_sum` (counting_spheres.hl:1052). Filled (PA22e wave).  Same
route as `DLWCHEM_sum` with the range split `range n = {0} ∪ Icc 1 (n-1)`
(`Finset.sum_range_add` + `Finset.sum_Ico_eq_sum_range`), `UKBRPFE_explicit`
at `i = 0` (the `+1` flat-sphere credit) and `BIEFJHU_explicit` on
`[1, n-1]`; the counting window `1 + 0.3924·n + 6.4692 ≤ 4π` already fails at
`n ≥ 13` (exact rational margin `1/250 = 0.004` over `4·3.1416`).
NEEDS: `sorryAx` dependency is the upstream `BIEFJHU_explicit` only
(`UKBRPFE_explicit` is closed); closing BIEFJHU closes this theorem for
free. -/
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
  have hn0 : 0 < n := by omega
  -- (a) the linear decomposition of the range-n sum (same as DLWCHEM)
  have hsplit : ∑ i ∈ Finset.range n, (0.591 - 0.0331 * (k i : ℝ) + 0.506 * lfun (h i))
      = (0.591:ℝ) * n - 0.0331 * ((∑ i ∈ Finset.range n, k i : ℕ) : ℝ)
        + 0.506 * (∑ i ∈ Finset.range n, lfun (h i)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum (s := Finset.range n) (f := fun i => (k i : ℝ)) (a := (0.0331:ℝ)),
      ← Finset.mul_sum (s := Finset.range n) (f := fun i => lfun (h i)) (a := (0.506:ℝ)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Nat.cast_sum]
    ring
  -- (b) split the range-n sum at 0: {0} ∪ [1, n-1]
  have hsplit2 : ∑ i ∈ Finset.range n, (0.591 - 0.0331 * (k i : ℝ) + 0.506 * lfun (h i))
      = (0.591 - 0.0331 * (k 0 : ℝ) + 0.506 * lfun (h 0)) +
        ∑ i ∈ Finset.Icc 1 (n - 1), (0.591 - 0.0331 * (k i : ℝ) + 0.506 * lfun (h i)) := by
    have hIcc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hrw : Finset.range n = Finset.range (1 + (n - 1)) := by congr 1; omega
    rw [hrw, Finset.sum_range_add, Finset.sum_range_one,
      ← Finset.sum_Ico_eq_sum_range
        (f := fun i => (0.591 - 0.0331 * (k i : ℝ) + 0.506 * lfun (h i))) 1 n, hIcc]
  -- (c) i = 0 term via UKBRPFE (flat radius, + 1 credit)
  have hk0 : 3 ≤ k 0 := (hik 0 hn0).1
  have hgt0 : (1:ℝ) + (0.591 - 0.0331 * (k 0 : ℝ) + 0.506 * lfun (h 0))
      ≤ max 0 (regularSphericalPolygonAreaP22 (Real.cos 0.797) (k 0)) := by
    rw [h0eq]; linarith [UKBRPFE_explicit (k 0) hpa hk0]
  -- (d) i in [1, n-1] terms via BIEFJHU
  have htermI : ∀ i ∈ Finset.Icc 1 (n - 1), (0.591 - 0.0331 * (k i : ℝ) + 0.506 * lfun (h i))
      ≤ max 0 (regularSphericalPolygonAreaP22
        (h i * sqrt3 / 4 + Real.sqrt (1 - (h i / 2) ^ 2) / 2) (k i)) := by
    intro i hi
    obtain ⟨_, hi2⟩ := Finset.mem_Icc.mp hi
    have hin : i < n := by omega
    exact BIEFJHU_explicit (h i) (k i) hpa ⟨(hik i hin).2.1, (hik i hin).2.2⟩ (hik i hin).1
  have hsumI := Finset.sum_le_sum htermI
  -- (e) combine
  have hcomb : (1:ℝ) + ∑ i ∈ Finset.range n, (0.591 - 0.0331 * (k i : ℝ) + 0.506 * lfun (h i))
      ≤ max 0 (regularSphericalPolygonAreaP22 (Real.cos 0.797) (k 0))
        + ∑ i ∈ Finset.Icc 1 (n - 1), max 0 (regularSphericalPolygonAreaP22
          (h i * sqrt3 / 4 + Real.sqrt (1 - (h i / 2) ^ 2) / 2) (k i)) := by
    rw [hsplit2]; linarith
  -- (f) counting arithmetic: n >= 13 forces 1 + 0.3924n + 6.4692 <= 4pi, false
  have hka : ((∑ i ∈ Finset.range n, k i : ℕ) : ℝ) ≤ (6:ℝ) * n - 12 := by
    have h12 : (12:ℕ) ≤ 6 * n := by omega
    have h2 : ((∑ i ∈ Finset.range n, k i : ℕ) : ℝ) ≤ ((6 * n - 12 : ℕ) : ℝ) := by
      exact_mod_cast hksum
    rw [Nat.cast_sub h12, Nat.cast_mul] at h2
    simpa only [Nat.cast_ofNat] using h2
  have hkey : (1:ℝ) + 0.591 * n - 0.0331 * (6 * n - 12) + 0.506 * 12 ≤ 4 * Real.pi := by
    linarith
  have hn13 : ((13:ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast (show ((13:ℕ)) ≤ n by omega)
  have hmono : (0.591:ℝ) * 13 - 0.0331 * (6 * 13 - 12)
      ≤ 0.591 * n - 0.0331 * (6 * n - 12) := by linarith
  have hnum : (1:ℝ) + 0.591 * 13 - 0.0331 * (6 * 13 - 12) + 0.506 * 12 = 12.5704 := by
    norm_num
  have hpi : (4:ℝ) * Real.pi < 12.5664 := by
    have h := Real.pi_lt_d4
    linarith
  linarith

/-- HOL `REAL_CONVEX_ON_SECOND_SECANT` (counting_spheres.hl:1099). Filled via
Lagrange MVT twice: `f'' ≥ 0` makes `f'` monotone on the interval (MVT on
`f'`), and MVT on `f` itself turns the secant slope into `f' c` at an
intermediate point `c`, which the monotonicity compares with `f' y`. -/
theorem REAL_CONVEX_ON_SECOND_SECANT (f f' f'' : ℝ → ℝ) (s : Set ℝ)
    (hi : isRealIntervalP22 s) (hs : ¬ ∃ a : ℝ, s = {a})
    (hd1 : ∀ x : ℝ, x ∈ s → HasDerivWithinAt f (f' x) s x)
    (hd2 : ∀ x : ℝ, x ∈ s → HasDerivWithinAt f' (f'' x) s x)
    (hnn : ∀ x : ℝ, x ∈ s → 0 ≤ f'' x) :
    ∀ x y : ℝ, x ∈ s → y ∈ s → f y - f x ≤ f' y * (y - x) := by
  obtain ⟨a, b, hseq⟩ := hi
  rcases lt_trichotomy a b with hab | hab | hab
  · -- the non-degenerate interval case
    have hdiff : ∀ z : ℝ, z ∈ Set.Ioo a b → HasDerivAt f (f' z) z := by
      intro z hz
      refine (hd1 z (by rw [hseq]; exact Set.mem_Icc.mpr ⟨hz.1.le, hz.2.le⟩)).hasDerivAt ?_
      rw [hseq, mem_nhds_iff]
      exact ⟨Set.Ioo a b, Ioo_subset_Icc_self, isOpen_Ioo, hz⟩
    have hdiff' : ∀ z : ℝ, z ∈ Set.Ioo a b → HasDerivAt f' (f'' z) z := by
      intro z hz
      refine (hd2 z (by rw [hseq]; exact Set.mem_Icc.mpr ⟨hz.1.le, hz.2.le⟩)).hasDerivAt ?_
      rw [hseq, mem_nhds_iff]
      exact ⟨Set.Ioo a b, Ioo_subset_Icc_self, isOpen_Ioo, hz⟩
    have hsubmem : ∀ {u v : ℝ}, u ∈ s → v ∈ s → Set.Icc u v ⊆ s := by
      intro u v hu hv z hz
      have hu' : u ∈ Set.Icc a b := by rw [← hseq]; exact hu
      have hv' : v ∈ Set.Icc a b := by rw [← hseq]; exact hv
      rw [hseq]
      exact Icc_subset_Icc hu'.1 hv'.2 hz
    have hcont : ∀ u v : ℝ, u ∈ s → v ∈ s → ContinuousOn f (Set.Icc u v) := by
      intro u v hu hv w hw
      exact ((hd1 w (hsubmem hu hv hw)).mono (hsubmem hu hv)).continuousWithinAt
    have hcont' : ∀ u v : ℝ, u ∈ s → v ∈ s → ContinuousOn f' (Set.Icc u v) := by
      intro u v hu hv w hw
      exact ((hd2 w (hsubmem hu hv hw)).mono (hsubmem hu hv)).continuousWithinAt
    have hdOn : ∀ u v : ℝ, u ∈ s → v ∈ s → DifferentiableOn ℝ f (Set.Ioo u v) := by
      intro u v hu hv z hz
      have hu' : u ∈ Set.Icc a b := by rw [← hseq]; exact hu
      have hv' : v ∈ Set.Icc a b := by rw [← hseq]; exact hv
      have hz' : z ∈ Set.Ioo a b :=
        Set.mem_Ioo.mpr ⟨by linarith [hu'.1, hz.1], by linarith [hz.2, hv'.2]⟩
      exact ((hdiff z hz').differentiableAt).differentiableWithinAt
    have hdOn' : ∀ u v : ℝ, u ∈ s → v ∈ s → DifferentiableOn ℝ f' (Set.Ioo u v) := by
      intro u v hu hv z hz
      have hu' : u ∈ Set.Icc a b := by rw [← hseq]; exact hu
      have hv' : v ∈ Set.Icc a b := by rw [← hseq]; exact hv
      have hz' : z ∈ Set.Ioo a b :=
        Set.mem_Ioo.mpr ⟨by linarith [hu'.1, hz.1], by linarith [hz.2, hv'.2]⟩
      exact ((hdiff' z hz').differentiableAt).differentiableWithinAt
    have hmono : ∀ u v : ℝ, u ∈ s → v ∈ s → u ≤ v → f' u ≤ f' v := by
      intro u v hu hv huv
      rcases lt_or_eq_of_le huv with hlt | heq
      · obtain ⟨c, hcmem, hc⟩ := exists_deriv_eq_slope f' hlt (hcont' u v hu hv)
          (hdOn' u v hu hv)
        have hu' : u ∈ Set.Icc a b := by rw [← hseq]; exact hu
        have hv' : v ∈ Set.Icc a b := by rw [← hseq]; exact hv
        have hcs : c ∈ s := hsubmem hu hv (Set.mem_Icc.mpr ⟨hcmem.1.le, hcmem.2.le⟩)
        have hcab : c ∈ Set.Ioo a b :=
          Set.mem_Ioo.mpr ⟨by linarith [hu'.1, hcmem.1], by linarith [hcmem.2, hv'.2]⟩
        have hdeq : f'' c = (f' v - f' u) / (v - u) := by
          rw [← HasDerivAt.deriv (hdiff' c hcab)]
          exact hc
        have h2 : 0 ≤ f'' c * (v - u) := mul_nonneg (hnn c hcs) (by linarith)
        rw [hdeq, div_mul_cancel₀ (f' v - f' u) (by linarith)] at h2
        linarith
      · exact heq ▸ le_refl _
    intro x y hx hy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · obtain ⟨c, hcmem, hc⟩ := exists_deriv_eq_slope f hlt (hcont x y hx hy)
        (hdOn x y hx hy)
      have hx' : x ∈ Set.Icc a b := by rw [← hseq]; exact hx
      have hy' : y ∈ Set.Icc a b := by rw [← hseq]; exact hy
      have hcab : c ∈ Set.Ioo a b :=
        Set.mem_Ioo.mpr ⟨by linarith [hx'.1, hcmem.1], by linarith [hcmem.2, hy'.2]⟩
      have hdeq : f' c = (f y - f x) / (y - x) := by
        rw [← HasDerivAt.deriv (hdiff c hcab)]
        exact hc
      have hle : f' c ≤ f' y :=
        hmono c y (hsubmem hx hy (Set.mem_Icc.mpr ⟨hcmem.1.le, hcmem.2.le⟩)) hy
          (le_of_lt (by linarith [hcmem.2]))
      rw [hdeq, div_le_iff₀ (by linarith)] at hle
      exact hle
    · rw [heq]; simp
    · obtain ⟨c, hcmem, hc⟩ := exists_deriv_eq_slope f hgt (hcont y x hy hx)
        (hdOn y x hy hx)
      have hy' : y ∈ Set.Icc a b := by rw [← hseq]; exact hy
      have hx' : x ∈ Set.Icc a b := by rw [← hseq]; exact hx
      have hcab : c ∈ Set.Ioo a b :=
        Set.mem_Ioo.mpr ⟨by linarith [hy'.1, hcmem.1], by linarith [hcmem.2, hx'.2]⟩
      have hdeq : f' c = (f x - f y) / (x - y) := by
        rw [← HasDerivAt.deriv (hdiff c hcab)]
        exact hc
      have hge : f' y ≤ f' c :=
        hmono y c hy (hsubmem hy hx (Set.mem_Icc.mpr ⟨hcmem.1.le, hcmem.2.le⟩))
          (le_of_lt (by linarith [hcmem.1]))
      rw [hdeq, le_div_iff₀ (by linarith)] at hge
      linarith [show f' y * (y - x) = -(f' y * (x - y)) from by ring]
  · -- `a = b` makes `s` a singleton
    exact absurd ⟨a, by rw [hseq, ← hab, Set.Icc_self]⟩ hs
  · -- `b < a` makes `s` empty
    intro x y hx hy
    rw [hseq] at hx
    have hempty : Set.Icc a b = ∅ := by
      refine Set.ext (fun z => ⟨fun h => ?_, fun h => absurd h (Set.notMem_empty z)⟩)
      exact absurd (le_trans h.1 h.2) (by linarith)
    rw [hempty] at hx
    exact absurd hx (by simp)

/-- Derivative of `sin y * t` (chain-rule helper for the `g`-function kit). -/
private theorem p22_g_sin_mul (t : ℝ) (x : ℝ) :
    HasDerivAt (fun y => Real.sin y * t) (Real.cos x * t) x :=
  (Real.hasDerivAt_sin x).mul_const t

/-- First derivative of `x - asn(sin x · t)`. -/
private theorem p22_g_deriv1 (t : ℝ) (x : ℝ) (h1 : Real.sin x * t ≠ -1)
    (h2 : Real.sin x * t ≠ 1) :
    HasDerivAt (fun y => y - asn (Real.sin y * t))
      (1 - t * Real.cos x / Real.sqrt (1 - (Real.sin x * t) ^ 2)) x := by
  have harc := (Real.hasDerivAt_arcsin h1 h2).comp x (p22_g_sin_mul t x)
  refine (hasDerivAt_id x).sub (harc.congr_deriv ?_)
  ring

/-- Second derivative of `x - asn(sin x · t)`, in normalized form. -/
private theorem p22_g_deriv2 (t : ℝ) (x : ℝ) (hx : |Real.sin x * t| < 1) :
    HasDerivAt (fun y => 1 - t * Real.cos y / Real.sqrt (1 - (Real.sin y * t) ^ 2))
      (t * (1 - t ^ 2) * Real.sin x *
        ((Real.sqrt (1 - (Real.sin x * t) ^ 2)) ^ 3)⁻¹) x := by
  have hApos : 0 < 1 - (Real.sin x * t) ^ 2 := by
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
    nlinarith [hlo, hhi]
  have hAnz : (1:ℝ) - (Real.sin x * t) ^ 2 ≠ 0 := ne_of_gt hApos
  have hA : HasDerivAt (fun y => 1 - (Real.sin y * t) ^ 2)
      (0 - 2 * (Real.sin x * t) ^ (2 - 1) * (Real.cos x * t)) x :=
    (hasDerivAt_const (c := (1:ℝ)) (x := x)).sub ((p22_g_sin_mul t x).pow 2)
  have hS : HasDerivAt (fun y => (Real.sqrt (1 - (Real.sin y * t) ^ 2))⁻¹)
      (-(1 / (2 * Real.sqrt (1 - (Real.sin x * t) ^ 2)) *
          (0 - 2 * (Real.sin x * t) ^ (2 - 1) * (Real.cos x * t))) /
        ((Real.sqrt (1 - (Real.sin x * t) ^ 2)) ^ 2)) x :=
    HasDerivAt.inv ((Real.hasDerivAt_sqrt hAnz).comp x hA)
      (ne_of_gt (Real.sqrt_pos.mpr hApos))
  have hc : HasDerivAt (fun y => t * Real.cos y)
      (0 * Real.cos x + t * (-Real.sin x)) x :=
    (hasDerivAt_const (c := t) (x := x)).mul (Real.hasDerivAt_cos x)
  have hmul := hc.mul hS
  exact ((hasDerivAt_const (c := (1:ℝ)) (x := x)).sub hmul).congr_deriv (by
    have hSin2 : t ^ 2 * Real.sin x ^ 2 = (Real.sin x * t) ^ 2 := by ring
    have hApos' : 0 < 1 - t ^ 2 * Real.sin x ^ 2 := by rw [hSin2]; exact hApos
    have hSq : (Real.sqrt (1 - t ^ 2 * Real.sin x ^ 2)) ^ 2 = 1 - t ^ 2 * Real.sin x ^ 2 :=
      Real.sq_sqrt (le_of_lt hApos')
    have hS0 : Real.sqrt (1 - t ^ 2 * Real.sin x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hApos')
    have hc2 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq x]
    field_simp [hSq, hS0]
    rw [hSq]
    ring_nf
    rw [hc2]
    ring)

/-- HOL `asn_sin_t''_alt` (counting_spheres.hl:1122, Calc_derivative form).
GIANT. -/
theorem asn_sin_t_sec_alt (x t alpha : ℝ) (h1 : |Real.sin x * t| < 1)
    (h2 : Real.cos alpha = Real.sin x * t) :
    derivedFormP22 (fun x => 1 - (Real.cos x * t) * (Real.sqrt (1 - (Real.sin x * t) ^ 2))⁻¹)
      (fun x => t * (1 - t ^ 2) * Real.sin x * (|Real.sin alpha| ^ 3)⁻¹) x
      (Set.Icc 0 Real.pi) := by
  unfold derivedFormP22
  have habs : |Real.sin alpha| = Real.sqrt (1 - (Real.sin x * t) ^ 2) := by
    have hsq : (|Real.sin alpha|) ^ 2 = 1 - (Real.sin x * t) ^ 2 := by
      rw [sq_abs (Real.sin alpha), ← h2]
      linarith [Real.sin_sq_add_cos_sq alpha]
    rw [← hsq]
    exact (Real.sqrt_sq (abs_nonneg (Real.sin alpha))).symm
  rw [habs]
  refine (p22_g_deriv2 t x h1).hasDerivWithinAt.congr (fun y _ => by ring) (by ring)
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

/-- HOL `g_convex` (counting_spheres.hl:1173). Filled via the explicit derivative
pair `(f', f'')` with `f'' x = t(1-t²) sin x (1-t²sin²x)^{-3/2} ≥ 0` on `[0,π]`. -/
theorem g_convex (t : ℝ) (ht : 0 < t ∧ t < 1) :
    ∃ s : Set ℝ, ∃ f' f'' : ℝ → ℝ,
      s = Set.Icc 0 Real.pi ∧ isRealIntervalP22 s ∧ ¬ ∃ a : ℝ, s = {a} ∧
      (∀ x : ℝ, x ∈ s → HasDerivWithinAt (fun x => x - asn (Real.sin x * t)) (f' x) s x) ∧
      (∀ x : ℝ, x ∈ s → HasDerivWithinAt f' (f'' x) s x) ∧
      (∀ x : ℝ, x ∈ s → 0 ≤ f'' x) := by
  refine ⟨Set.Icc 0 Real.pi,
    fun x => 1 - t * Real.cos x / Real.sqrt (1 - (Real.sin x * t) ^ 2),
    fun x => t * (1 - t ^ 2) * Real.sin x *
      ((Real.sqrt (1 - (Real.sin x * t) ^ 2)) ^ 3)⁻¹,
    rfl, ⟨0, Real.pi, rfl⟩, ?_⟩
  -- the ¬-conjunct absorbs the three HasDerivWithinAt/≤ clauses by precedence
  rintro ⟨a, ha⟩
  have h0 : (0:ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_refl _, Real.pi_pos.le⟩
  have hpi : (Real.pi:ℝ) ∈ Set.Icc 0 Real.pi := ⟨Real.pi_pos.le, le_refl _⟩
  rw [ha.1, Set.mem_singleton_iff] at h0 hpi
  exact Real.pi_ne_zero (hpi.trans h0.symm)

/-- HOL `GOTCJAH_convex_sum` (counting_spheres.hl:1230). Filled: Jensen for
`g = x - asn(sin x · t)` on `[0,π]` (convex by `f'' ≥ 0`). -/
theorem GOTCJAH_convex_sum (n : ℕ) (t : ℝ) (bet : ℕ → ℝ) (u : ℝ) (hn : 0 < n)
    (hu1 : u ≤ n * Real.pi) (hu2 : 0 ≤ u) (ht : 0 < t ∧ t < 1)
    (hsum : ∑ i ∈ Finset.range n, bet i = u)
    (hb : ∀ i : ℕ, i < n → 0 ≤ bet i ∧ bet i ≤ Real.pi) :
    u - n * asn (Real.sin (u / n) * t) ≤
      ∑ i ∈ Finset.range n, (bet i - asn (Real.sin (bet i) * t)) := by
  classical
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  -- `g` is convex on [0,π]: second derivative `t(1-t²) sin x · (1-t²sin²x)^{-3/2} ≥ 0`
  have habs : ∀ y : ℝ, |Real.sin y * t| < 1 := fun y => by
    rw [abs_mul, abs_of_pos ht.1]
    calc |Real.sin y| * t ≤ 1 * t :=
          mul_le_mul_of_nonneg_right (Real.abs_sin_le_one y) (le_of_lt ht.1)
      _ < 1 := by linarith
  have hqne : ∀ y : ℝ, Real.sin y * t ≠ -1 ∧ Real.sin y * t ≠ 1 := fun y => by
    have hb := habs y
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hc] at hb; simp at hb
    · rw [hc] at hb; simp at hb
  have hD : Convex ℝ (Set.Icc 0 Real.pi) := convex_Icc 0 Real.pi
  have hcont1 : Continuous (fun x => asn (Real.sin x * t)) :=
    Real.continuous_arcsin.comp ((Real.continuous_sin).mul continuous_const)
  have hf : ContinuousOn (fun x => x - asn (Real.sin x * t)) (Set.Icc 0 Real.pi) :=
    (Continuous.sub continuous_id hcont1).continuousOn
  have hcv : ConvexOn ℝ (Set.Icc 0 Real.pi) (fun x => x - asn (Real.sin x * t)) :=
    convexOn_of_hasDerivWithinAt2_nonneg hD hf
      (fun _ _ => (p22_g_deriv1 t _ (hqne _).1 (hqne _).2).hasDerivWithinAt)
      (fun _ _ => (p22_g_deriv2 t _ (habs _)).hasDerivWithinAt)
      (fun x hx => by
        have hxI : x ∈ Set.Icc (0:ℝ) Real.pi := interior_subset hx
        have h1 : 0 ≤ t := le_of_lt ht.1
        have h2 : 0 ≤ 1 - t ^ 2 := by
          have hte : t ^ 2 ≤ t := by nlinarith [ht.1, ht.2]
          nlinarith
        have h3 : 0 ≤ Real.sin x := Real.sin_nonneg_of_mem_Icc hxI
        have h4 : 0 < 1 - (Real.sin x * t) ^ 2 := by
          obtain ⟨hlo, hhi⟩ := abs_lt.mp (habs x)
          nlinarith [hlo, hhi]
        exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3)
          (inv_nonneg.mpr (le_of_lt (pow_pos (Real.sqrt_pos.mpr h4) 3))))
  have hun : u / n ∈ Set.Icc 0 Real.pi := by
    rw [Set.mem_Icc]
    constructor
    · exact div_nonneg hu2 (le_of_lt (by positivity))
    · rw [div_le_iff₀ (by positivity), mul_comm Real.pi (n:ℝ)]
      exact hu1
  have hw0 : ∀ i ∈ Finset.range n, (0:ℝ) ≤ 1 / n := fun i _ =>
    div_nonneg zero_le_one (le_of_lt (by positivity))
  have hw1 : ∑ i ∈ Finset.range n, ((1:ℝ) / n) = 1 := by
    rw [← Finset.sum_div, Finset.sum_const, Finset.card_range, Nat.smul_one_eq_cast,
      div_self (by positivity)]
  have hmem : ∀ i ∈ Finset.range n, bet i ∈ Set.Icc 0 Real.pi := fun i hi =>
    Set.mem_Icc.mpr (hb i (Finset.mem_range.mp hi))
  have key := hcv.map_sum_le hw0 hw1 hmem
  have hL : ∑ i ∈ Finset.range n, ((1:ℝ)/n) • bet i = u / n := by
    have h1 : ∀ i ∈ Finset.range n, ((1:ℝ)/n) • bet i = (1:ℝ)/n * bet i := fun i _ => rfl
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hsum]
    field_simp
  rw [hL] at key
  have key' : (fun x => x - asn (Real.sin x * t)) (u / n)
      ≤ (1:ℝ)/n * ∑ i ∈ Finset.range n, (bet i - asn (Real.sin (bet i) * t)) := by
    have h2 : ∀ i ∈ Finset.range n, ((1:ℝ)/n) • (bet i - asn (Real.sin (bet i) * t))
        = (1:ℝ)/n * (bet i - asn (Real.sin (bet i) * t)) := fun i _ => rfl
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum] at key
    exact key
  have hfinal := mul_le_mul_of_nonneg_left key'
      (le_of_lt (show (0:ℝ) < n from by positivity))
  rw [← mul_assoc, mul_one_div_cancel hn0, one_mul] at hfinal
  have e1 : (n:ℝ) * ((fun x => x - asn (Real.sin x * t)) (u / n))
      = u - n * asn (Real.sin (u / n) * t) := by
    rw [mul_sub, mul_div_cancel₀ _ hn0]
  rw [← e1]
  exact hfinal

/-- Linearity of `⬝ᵥ` in the left argument. -/
theorem dotV_smul_left (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) := by
  show ((t • a : V3).ofLp) ⬝ᵥ b.ofLp = t * (a.ofLp ⬝ᵥ b.ofLp)
  rw [WithLp.ofLp_smul, smul_dotProduct, smul_eq_mul]

/-- Linearity of `⬝ᵥ` in the right argument. -/
theorem dotV_smul_right (a : V3) (t : ℝ) (b : V3) : a ⬝ᵥ (t • b) = t * (a ⬝ᵥ b) := by
  show a.ofLp ⬝ᵥ ((t • b : V3).ofLp) = t * (a.ofLp ⬝ᵥ b.ofLp)
  rw [WithLp.ofLp_smul, dotProduct_smul, smul_eq_mul]

/-- Additivity of `⬝ᵥ` in the left argument. -/
theorem dotV_add_left (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c := by
  show ((a + b : V3).ofLp) ⬝ᵥ c.ofLp = a.ofLp ⬝ᵥ c.ofLp + b.ofLp ⬝ᵥ c.ofLp
  rw [WithLp.ofLp_add, add_dotProduct]

/-- Additivity of `⬝ᵥ` in the right argument. -/
theorem dotV_add_right (a b c : V3) : a ⬝ᵥ (b + c) = a ⬝ᵥ b + a ⬝ᵥ c := by
  show a.ofLp ⬝ᵥ ((b + c : V3).ofLp) = a.ofLp ⬝ᵥ b.ofLp + a.ofLp ⬝ᵥ c.ofLp
  rw [WithLp.ofLp_add, dotProduct_add]

/-- Subtraction in the left argument of `⬝ᵥ`. -/
theorem dotV_sub_left (a b c : V3) : (a - b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c := by
  show ((a - b : V3).ofLp) ⬝ᵥ c.ofLp = a.ofLp ⬝ᵥ c.ofLp - b.ofLp ⬝ᵥ c.ofLp
  rw [WithLp.ofLp_sub, sub_dotProduct]

/-- Subtraction in the right argument of `⬝ᵥ`. -/
theorem dotV_sub_right (a b c : V3) : a ⬝ᵥ (b - c) = a ⬝ᵥ b - a ⬝ᵥ c := by
  show a.ofLp ⬝ᵥ ((b - c : V3).ofLp) = a.ofLp ⬝ᵥ b.ofLp - a.ofLp ⬝ᵥ c.ofLp
  rw [WithLp.ofLp_sub, dotProduct_sub]

/-- Commutativity of `⬝ᵥ`. -/
theorem dotV_comm (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a := by
  show a.ofLp ⬝ᵥ b.ofLp = b.ofLp ⬝ᵥ a.ofLp
  exact dotProduct_comm a.ofLp b.ofLp

/-- The `V3`-to-`Fin 3 → ℝ` coercion of the zero vector is the zero function. -/
theorem coeV_zero : ((0 : V3) : Fin 3 → ℝ) = 0 := rfl

/-- HOL `dih_dot` (counting_spheres.hl:1272). Filled: the projected edge vectors
are orthogonal, so the dihedral is `arccos 0 = π/2`. -/
theorem dih_dot (u v w : V3) (hu : u ≠ 0) (h1 : (w - u) ⬝ᵥ v = 0)
    (h2 : (w - u) ⬝ᵥ u = 0) : dihV 0 u v w = Real.pi / 2 := by
  have hwu : w ⬝ᵥ u = u ⬝ᵥ u := by
    rw [dotV_sub_left] at h2
    linarith
  have hvw : v ⬝ᵥ w = v ⬝ᵥ u := by
    have h3 : v ⬝ᵥ (w - u) = 0 := by rw [dotV_comm]; exact h1
    rw [dotV_sub_right] at h3
    linarith
  have hnum : ((u.ofLp ⬝ᵥ u.ofLp) • v.ofLp - (v.ofLp ⬝ᵥ u.ofLp) • u.ofLp) ⬝ᵥ
      ((u.ofLp ⬝ᵥ u.ofLp) • w.ofLp - (w.ofLp ⬝ᵥ u.ofLp) • u.ofLp) = 0 := by
    rw [dotProduct_sub, sub_dotProduct, sub_dotProduct,
      smul_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct,
      dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul,
      hwu, hvw, dotProduct_comm u.ofLp w.ofLp, hwu]
    ring
  simp only [dihV, arcV, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_zero,
    WithLp.ofLp_zero, hnum, zero_div]
  exact Real.arccos_zero

/-- HOL `abs_1_prod` (counting_spheres.hl:1295). -/
theorem abs_1_prod (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x * y| ≤ 1 := by
  rw [abs_mul]
  exact le_trans (mul_le_mul hx hy (by norm_num) (by norm_num)) (by norm_num)

private theorem dlinP {p1 p2 q1 q2 : Fin 3 → ℝ} (a1 a2 b1 b2 : ℝ) :
    (a1 • p1 - a2 • p2) ⬝ᵥ (b1 • q1 - b2 • q2)
      = a1 * b1 * (p1 ⬝ᵥ q1) - a1 * b2 * (p1 ⬝ᵥ q2)
        - a2 * b1 * (p2 ⬝ᵥ q1) + a2 * b2 * (p2 ⬝ᵥ q2) := by
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul]
  ring

private theorem sqdist (w : V3) : (dist w 0) ^ 2 = w ⬝ᵥ w := by
  rw [dist_eq_norm, norm_sq_eq_dot]
  simp

private theorem sqeq (w : V3) (t : ℝ) (ht : 0 ≤ t) (h : (dist w 0) ^ 2 = t ^ 2) :
    dist w 0 = t := by
  by_contra hne
  have hdn : 0 ≤ dist w 0 := dist_nonneg
  have h1 : (dist w 0 - t) * (dist w 0 + t) = 0 := by
    have h2 : dist w 0 ^ 2 - t ^ 2 = 0 := by rw [h, sub_self]
    nlinarith
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact hne (by linarith)
  · have h3 : dist w 0 = 0 := by linarith
    have h4 : t = 0 := by linarith
    exact hne (h3.trans h4.symm)

private theorem collinear3_132 {x y z : V3} (h : Collinear3 x y z) : Collinear3 x z y := by
  simp only [Collinear3] at h ⊢
  rw [show ({x, z, y} : Set V3) = ({x, y, z} : Set V3) from by
    ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
  exact h

private theorem mem_line_of_col {v w : V3} (hv : v ≠ 0) (hcol : Collinear3 0 v w) :
    w ∈ (affineSpan ℝ ({0, v} : Set V3) : Set V3) := by
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := (0:V3)) (w := v) (w1 := w) hv).mp hcol
  refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨c, ?_⟩
  rw [AffineMap.lineMap_apply]
  simp only [vadd_eq_add, vsub_eq_sub, sub_zero, add_zero]
  simp only [sub_zero] at hc
  rw [hc]

/-- HOL `sloc2_ortho` (counting_spheres.hl:1306). GIANT. Filled: right
spherical-triangle identity `cos alp = sin bet * t`.  With Gram scalars
`A := va⬝ᵥva`, `B := vb⬝ᵥvb`, `C := vc⬝ᵥvc`, `x := vb⬝ᵥvc`, `y := va⬝ᵥvc`,
`z := va⬝ᵥvb` and the projections onto axis-orthogonal complements
(`X := A•vb - z•va` etc.), the right angle `dihV 0 vc va vb = π/2` gives
`C*z = x*y`; the six dot/norm expansions and positivity of `A*C - y²`,
`B*C - x²`, `A*B*C² - x²*y²` (scaled norms of nonzero projections,
nonzeroness from `¬ Coplanar` via `coplanar_triple`/`collinear3_iff_smul`)
yield the values of `cos alp`, `sin bet`, `t`; the endgame assembles through
the squared route `(cos alp)² = x²*(A*C - y²)/(A*B*C² - x²*y²)
= (1 - q_b²) * t²` with explicit `div_mul_div_comm` / cross-multiplication
chains (`field_simp` on the sqrt-heavy assembly goals mis-clears
denominators and is avoided) plus the sign `0 ≤ cos alp * (sin bet * t)`
(both factors carry the sign of `x`).  Statements frozen; do not restate. -/
theorem sloc2_ortho (va vb vc : V3)
    (hcp : ¬ Coplanar ({0, va, vb, vc} : Set V3))
    (h : dihV 0 vc va vb = Real.pi / 2) :
    let bet := dihV 0 vb vc va
    let alp := dihV 0 va vb vc
    let t := Real.cos (arcV 0 vb vc)
    Real.cos alp = Real.sin bet * t := by
  show Real.cos (dihV 0 va vb vc)
      = Real.sin (dihV 0 vb vc va) * Real.cos (arcV 0 vb vc)
  -- ## nondegeneracy
  have hv0 : va ≠ 0 := by
    intro he
    apply hcp
    rw [show ({0, va, vb, vc} : Set V3) = {0, vb, vc} from by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [he]; tauto]
    exact coplanar_triple 0 vb vc
  have hw0 : vb ≠ 0 := by
    intro he
    apply hcp
    rw [show ({0, va, vb, vc} : Set V3) = {0, va, vc} from by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [he]; tauto]
    exact coplanar_triple 0 va vc
  have hu0 : vc ≠ 0 := by
    intro he
    apply hcp
    rw [show ({0, va, vb, vc} : Set V3) = {0, va, vb} from by
      ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; rw [he]; tauto]
    exact coplanar_triple 0 va vb
  have n1 : ¬ Collinear3 0 va vb := by
    intro hcol
    apply hcp
    refine ⟨(0:V3), va, vc, ?_⟩
    have hmem := mem_line_of_col hv0 hcol
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · exact (affineSpan_mono ℝ (by
        intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto)) hmem
    · exact mem_affineSpan ℝ (by simp)
  have n2 : ¬ Collinear3 0 va vc := by
    intro hcol
    apply hcp
    refine ⟨(0:V3), va, vb, ?_⟩
    have hmem := mem_line_of_col hv0 hcol
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · exact (affineSpan_mono ℝ (by
        intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto)) hmem
  have n1' : ¬ Collinear3 0 vb va := fun hcol => n1 (collinear3_132 hcol)
  have n2' : ¬ Collinear3 0 vc va := fun hcol => n2 (collinear3_132 hcol)
  have n3 : ¬ Collinear3 0 vb vc := by
    intro hcol
    apply hcp
    refine ⟨(0:V3), va, vb, ?_⟩
    have hmem := mem_line_of_col hw0 hcol
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · exact (affineSpan_mono ℝ (by
        intro q hq; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢; tauto)) hmem
  have n3' : ¬ Collinear3 0 vc vb := fun hcol => n3 (collinear3_132 hcol)
  -- ## Cauchy-Schwarz
  have qbnd : ∀ u v : V3, u ≠ 0 → v ≠ 0 →
      -1 ≤ (u ⬝ᵥ v) / (dist u 0 * dist v 0) ∧
        (u ⬝ᵥ v) / (dist u 0 * dist v 0) ≤ 1 := by
    intro u v hu hv
    have hd1 : dist u 0 = ‖u‖ := by rw [dist_eq_norm, sub_zero]
    have hd2 : dist v 0 = ‖v‖ := by rw [dist_eq_norm, sub_zero]
    have hle : |u ⬝ᵥ v| ≤ ‖u‖ * ‖v‖ := by
      rw [← Kepler.Geom.inner_eq_dot]
      exact abs_real_inner_le_norm u v
    have h1 : |(u ⬝ᵥ v) / (dist u 0 * dist v 0)| ≤ 1 := by
      rw [abs_div, hd1, hd2, abs_mul, abs_of_nonneg (norm_nonneg u),
        abs_of_nonneg (norm_nonneg v)]
      exact div_le_one (by positivity) |>.mpr hle
    exact abs_le.mp h1
  -- ## dihedral unfolding
  have keyd : ∀ w1 w2 w3 : V3, dihV 0 w1 w2 w3 =
      Real.arccos ((((w1 ⬝ᵥ w1) • w2 - (w2 ⬝ᵥ w1) • w1 : V3) ⬝ᵥ
          ((w1 ⬝ᵥ w1) • w3 - (w3 ⬝ᵥ w1) • w1 : V3)) /
        (dist ((w1 ⬝ᵥ w1) • w2 - (w2 ⬝ᵥ w1) • w1) 0 *
          dist ((w1 ⬝ᵥ w1) • w3 - (w3 ⬝ᵥ w1) • w1) 0)) := by
    intro w1 w2 w3
    simp only [dihV, arcV, sub_zero, WithLp.ofLp_zero]
  -- ## Gram scalars
  set A := va ⬝ᵥ va with hAdef
  set B := vb ⬝ᵥ vb with hBdef
  set C := vc ⬝ᵥ vc with hCdef
  set x := vb ⬝ᵥ vc with hxdef
  set y := va ⬝ᵥ vc with hydef
  set z := va ⬝ᵥ vb with hzdef
  have hApos : 0 < A := by
    rw [hAdef]
    have h1 : ‖va‖ ^ 2 = va ⬝ᵥ va := norm_sq_eq_dot va
    have h3 : ‖va‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    rw [← h1]; exact sq_pos_of_ne_zero h3
  have hBpos : 0 < B := by
    rw [hBdef]
    have h1 : ‖vb‖ ^ 2 = vb ⬝ᵥ vb := norm_sq_eq_dot vb
    have h3 : ‖vb‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    rw [← h1]; exact sq_pos_of_ne_zero h3
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : ‖vc‖ ^ 2 = vc ⬝ᵥ vc := norm_sq_eq_dot vc
    have h3 : ‖vc‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    rw [← h1]; exact sq_pos_of_ne_zero h3
  -- ## projections
  set X := A • vb - z • va with hXdef
  set Y := A • vc - y • va with hYdef
  set U := B • vc - x • vb with hUdef
  set V := B • va - z • vb with hVdef
  have hXne : X ≠ 0 := by
    intro hXz
    apply n1
    rw [hXdef, sub_eq_zero] at hXz
    refine (collinear3_iff_smul (v := (0:V3)) (w := va) (w1 := vb) hv0).mpr ⟨z / A, ?_⟩
    simp only [sub_zero]
    rw [← inv_smul_smul₀ (a := A) hApos.ne' vb, hXz, smul_smul, inv_mul_eq_div]
  have hYne : Y ≠ 0 := by
    intro hYz
    apply n2
    rw [hYdef, sub_eq_zero] at hYz
    refine (collinear3_iff_smul (v := (0:V3)) (w := va) (w1 := vc) hv0).mpr ⟨y / A, ?_⟩
    simp only [sub_zero]
    rw [← inv_smul_smul₀ (a := A) hApos.ne' vc, hYz, smul_smul, inv_mul_eq_div]
  have hUne : U ≠ 0 := by
    intro hUz
    apply n3
    rw [hUdef, sub_eq_zero] at hUz
    refine (collinear3_iff_smul (v := (0:V3)) (w := vb) (w1 := vc) hw0).mpr ⟨x / B, ?_⟩
    simp only [sub_zero]
    rw [← inv_smul_smul₀ (a := B) hBpos.ne' vc, hUz, smul_smul, inv_mul_eq_div]
  have hVne : V ≠ 0 := by
    intro hVz
    apply n1'
    rw [hVdef, sub_eq_zero] at hVz
    refine (collinear3_iff_smul (v := (0:V3)) (w := vb) (w1 := va) hw0).mpr ⟨z / B, ?_⟩
    simp only [sub_zero]
    rw [← inv_smul_smul₀ (a := B) hBpos.ne' va, hVz, smul_smul, inv_mul_eq_div]
  -- ## dot/norm expansions
  have eXY : X ⬝ᵥ Y = A ^ 2 * x - A * y * z := by
    rw [hXdef, hYdef]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul]
    rw [dlinP, ← hxdef, dotV_comm vb va, ← hzdef, ← hydef, ← hAdef]
    ring
  have eX2 : ‖X‖ ^ 2 = A ^ 2 * B - A * z ^ 2 := by
    rw [norm_sq_eq_dot, hXdef]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul]
    rw [dlinP, dotV_comm vb va, ← hzdef, ← hBdef, ← hAdef]
    ring
  have eY2 : ‖Y‖ ^ 2 = A ^ 2 * C - A * y ^ 2 := by
    rw [norm_sq_eq_dot, hYdef]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul]
    rw [dlinP, dotV_comm vc va, ← hydef, ← hCdef, ← hAdef]
    ring
  have eUV : U ⬝ᵥ V = B ^ 2 * y - B * x * z := by
    rw [hUdef, hVdef]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul]
    rw [dlinP, dotV_comm vc va, ← hydef, dotV_comm vc vb, ← hxdef, dotV_comm vb va,
      ← hzdef, ← hBdef]
    ring
  have eU2 : ‖U‖ ^ 2 = B ^ 2 * C - B * x ^ 2 := by
    rw [norm_sq_eq_dot, hUdef]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul]
    rw [dlinP, dotV_comm vc vb, ← hxdef, ← hCdef, ← hBdef]
    ring
  have eV2 : ‖V‖ ^ 2 = B ^ 2 * A - B * z ^ 2 := by
    rw [norm_sq_eq_dot, hVdef]
    simp only [WithLp.ofLp_sub, WithLp.ofLp_smul]
    rw [dlinP, ← hzdef, dotV_comm vb va, ← hzdef, ← hBdef, ← hAdef]
    ring
  -- ## right angle: C * z = x * y
  have hR : C * z = x * y := by
    have hvap : (C • va - y • vc : V3) ≠ 0 := by
      intro hzero
      apply n2'
      refine (collinear3_iff_smul (v := (0:V3)) (w := vc) (w1 := va) hu0).mpr ⟨y / C, ?_⟩
      have h1 : C • va = y • vc := sub_eq_zero.mp hzero
      simp only [sub_zero]
      rw [← inv_smul_smul₀ (a := C) hCpos.ne' va, h1, smul_smul, inv_mul_eq_div]
    have hvbp : (C • vb - x • vc : V3) ≠ 0 := by
      intro hzero
      apply n3'
      refine (collinear3_iff_smul (v := (0:V3)) (w := vc) (w1 := vb) hu0).mpr ⟨x / C, ?_⟩
      have h1 : C • vb = x • vc := sub_eq_zero.mp hzero
      simp only [sub_zero]
      rw [← inv_smul_smul₀ (a := C) hCpos.ne' vb, h1, smul_smul, inv_mul_eq_div]
    have hk := keyd vc va vb
    rw [h, ← hCdef, ← hydef, ← hxdef] at hk
    have hq := qbnd (C • va - y • vc) (C • vb - x • vc) hvap hvbp
    have h1 := Real.cos_arccos hq.1 hq.2
    rw [← hk, Real.cos_pi_div_two] at h1
    -- h1 : 0 = quotient
    have hdd : dist (C • va - y • vc) 0 * dist (C • vb - x • vc) 0 ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · exact dist_ne_zero.mpr hvap
      · exact dist_ne_zero.mpr hvbp
    have h2 : ((C • va - y • vc : V3) ⬝ᵥ (C • vb - x • vc : V3)) = 0 := by
      have h2' := (div_eq_iff hdd).mp h1.symm
      simpa using h2'
    have h3 : ((C • va - y • vc : V3) ⬝ᵥ (C • vb - x • vc : V3))
        = C ^ 2 * z - C * x * y := by
      simp only [WithLp.ofLp_sub, WithLp.ofLp_smul]
      rw [dlinP, dotV_comm vc vb, ← hxdef, ← hydef, ← hzdef, ← hCdef]
      ring
    rw [h3] at h2
    simp only [pow_two] at h2
    have h5 : C * (C * z - x * y) = 0 := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc]
      exact h2
    rcases mul_eq_zero.mp h5 with h0 | h0
    · exact absurd h0 hCpos.ne'
    · linarith
  -- ## derived positivity
  have hz' : z = x * y / C := (eq_div_iff hCpos.ne').mpr (by rw [mul_comm]; exact hR)
  have hP0 : 0 < A * C - y ^ 2 := by
    have h1 : ‖Y‖ ^ 2 = A * (A * C - y ^ 2) := by rw [eY2]; ring
    have h3 : ‖Y‖ ≠ 0 := norm_ne_zero_iff.mpr hYne
    have h2 : 0 < ‖Y‖ ^ 2 := sq_pos_of_ne_zero h3
    rw [h1] at h2
    by_contra hcon
    push_neg at hcon
    have h8 : A * (A * C - y ^ 2) ≤ 0 :=
      calc A * (A * C - y ^ 2) ≤ A * 0 := mul_le_mul_of_nonneg_left hcon hApos.le
        _ = 0 := by ring
    linarith
  have hQ0 : 0 < B * C - x ^ 2 := by
    have h1 : ‖U‖ ^ 2 = B * (B * C - x ^ 2) := by rw [eU2]; ring
    have h3 : ‖U‖ ≠ 0 := norm_ne_zero_iff.mpr hUne
    have h2 : 0 < ‖U‖ ^ 2 := sq_pos_of_ne_zero h3
    rw [h1] at h2
    by_contra hcon
    push_neg at hcon
    have h8 : B * (B * C - x ^ 2) ≤ 0 :=
      calc B * (B * C - x ^ 2) ≤ B * 0 := mul_le_mul_of_nonneg_left hcon hBpos.le
        _ = 0 := by ring
    linarith
  have hD0 : 0 < A * B * C ^ 2 - x ^ 2 * y ^ 2 := by
    have h1 : ‖V‖ ^ 2 = B * (A * B * C ^ 2 - x ^ 2 * y ^ 2) / C ^ 2 := by
      rw [eV2, hz', div_pow, mul_pow]
      field_simp
    have h3 : ‖V‖ ≠ 0 := norm_ne_zero_iff.mpr hVne
    have h2 : 0 < ‖V‖ ^ 2 := sq_pos_of_ne_zero h3
    rw [h1] at h2
    have h4 : (0:ℝ) < C ^ 2 := by positivity
    have h5 : 0 < B * (A * B * C ^ 2 - x ^ 2 * y ^ 2) := by
      have h6 := mul_pos h2 h4
      rwa [div_mul_cancel₀ _ h4.ne'] at h6
    by_contra hcon
    push_neg at hcon
    have h7 : B * (A * B * C ^ 2 - x ^ 2 * y ^ 2) ≤ 0 :=
      calc B * (A * B * C ^ 2 - x ^ 2 * y ^ 2)
          ≤ B * 0 := mul_le_mul_of_nonneg_left hcon hBpos.le
        _ = 0 := by ring
    linarith
  -- ## endgame (explicit sqrt terms)
  have hsqP : (Real.sqrt (A * C - y ^ 2)) ^ 2 = A * C - y ^ 2 := Real.sq_sqrt hP0.le
  have hsqD : (Real.sqrt (A * B * C ^ 2 - x ^ 2 * y ^ 2)) ^ 2 =
      A * B * C ^ 2 - x ^ 2 * y ^ 2 := Real.sq_sqrt hD0.le
  have hsqQ : (Real.sqrt (B * C - x ^ 2)) ^ 2 = B * C - x ^ 2 := Real.sq_sqrt hQ0.le
  -- key values
  have k1 : X ⬝ᵥ Y = A * x * (A * C - y ^ 2) / C := by
    rw [eXY, hz']; field_simp
  have k2 : dist X 0 = Real.sqrt A * Real.sqrt (A * B * C ^ 2 - x ^ 2 * y ^ 2) / C := by
    have hnn : 0 ≤ Real.sqrt A * Real.sqrt (A * B * C ^ 2 - x ^ 2 * y ^ 2) / C :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg A)
        (Real.sqrt_nonneg _)) hCpos.le
    apply sqeq _ _ hnn
    rw [sqdist X, ← norm_sq_eq_dot, eX2, hz']
    simp only [div_pow, mul_pow, Real.sq_sqrt hApos.le, hsqD]
    field_simp
  have k3 : dist Y 0 = Real.sqrt A * Real.sqrt (A * C - y ^ 2) := by
    have hnn : 0 ≤ Real.sqrt A * Real.sqrt (A * C - y ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg _)
    apply sqeq _ _ hnn
    rw [sqdist Y, ← norm_sq_eq_dot, eY2]
    simp only [mul_pow, Real.sq_sqrt hApos.le, hsqP]
    ring
  have k4 : U ⬝ᵥ V = B * y * (B * C - x ^ 2) / C := by
    rw [eUV, hz']; field_simp
  have k5 : dist U 0 = Real.sqrt B * Real.sqrt (B * C - x ^ 2) := by
    have hnn : 0 ≤ Real.sqrt B * Real.sqrt (B * C - x ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg B) (Real.sqrt_nonneg _)
    apply sqeq _ _ hnn
    rw [sqdist U, ← norm_sq_eq_dot, eU2]
    simp only [mul_pow, Real.sq_sqrt hBpos.le, hsqQ]
    ring
  have k6 : dist V 0 = Real.sqrt B * Real.sqrt (A * B * C ^ 2 - x ^ 2 * y ^ 2) / C := by
    have hnn : 0 ≤ Real.sqrt B * Real.sqrt (A * B * C ^ 2 - x ^ 2 * y ^ 2) / C :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg B) (Real.sqrt_nonneg _)) hCpos.le
    apply sqeq _ _ hnn
    rw [sqdist V, ← norm_sq_eq_dot, eV2, hz']
    simp only [div_pow, mul_pow, Real.sq_sqrt hBpos.le, hsqD]
    field_simp
  have k7 : dist vb 0 = Real.sqrt B := by
    have hnn : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
    apply sqeq _ _ hnn
    rw [sqdist vb, ← hBdef, Real.sq_sqrt hBpos.le]
  have k8 : dist vc 0 = Real.sqrt C := by
    have hnn : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
    apply sqeq _ _ hnn
    rw [sqdist vc, ← hCdef, Real.sq_sqrt hCpos.le]
  -- the three angle values
  have hca : Real.cos (dihV 0 va vb vc) = (X ⬝ᵥ Y)/(dist X 0 * dist Y 0) := by
    rw [keyd va vb vc, ← hAdef, dotV_comm vb va, ← hzdef, dotV_comm vc va, ← hydef]
    exact Real.cos_arccos (qbnd X Y hXne hYne).1 (qbnd X Y hXne hYne).2
  have hcb : Real.sin (dihV 0 vb vc va) =
      Real.sqrt (1 - ((U ⬝ᵥ V)/(dist U 0 * dist V 0)) ^ 2) := by
    rw [keyd vb vc va, ← hBdef, dotV_comm vc vb, ← hxdef, ← hzdef]
    exact Real.sin_arccos _
  have hct : Real.cos (arcV 0 vb vc) = (vb ⬝ᵥ vc)/(dist vb 0 * dist vc 0) := by
    simp only [arcV, sub_zero, WithLp.ofLp_zero]
    exact Real.cos_arccos (qbnd vb vc hw0 hu0).1 (qbnd vb vc hw0 hu0).2
  -- ## algebra: squared identity + sign
  have hDne : 0 < B * C ^ 2 * A - y ^ 2 * x ^ 2 := by nlinarith [hD0]
  have hDne' : (B * C ^ 2 * A - y ^ 2 * x ^ 2) ≠ 0 := hDne.ne'
  have hqbr : ((U ⬝ᵥ V)/(dist U 0 * dist V 0)) ^ 2
      = y ^ 2 * (B * C - x ^ 2) / (A * B * C ^ 2 - x ^ 2 * y ^ 2) := by
    rw [k4, k5, k6]
    have h2 : (Real.sqrt (A * B * C ^ 2 - x ^ 2 * y ^ 2)) ^ 2
        = A * B * C ^ 2 - x ^ 2 * y ^ 2 := hsqD
    have h3 : (Real.sqrt (B * C - x ^ 2)) ^ 2 = B * C - x ^ 2 := hsqQ
    have hB4 : (Real.sqrt B) ^ 4 = B ^ 2 := by
      rw [show (Real.sqrt B) ^ 4 = (Real.sqrt B) ^ (2 + 2) from by norm_num,
        pow_add, Real.sq_sqrt hBpos.le]
      ring
    simp only [div_pow, mul_pow, h2, h3]
    field_simp [hD0.ne']
    rw [hB4]
    ring
  have htv : Real.cos (arcV 0 vb vc) = x / (Real.sqrt B * Real.sqrt C) := by
    rw [hct, k7, k8, ← hxdef]
  have hX : dist X 0 ^ 2 = A * (A * B * C ^ 2 - x ^ 2 * y ^ 2) / C ^ 2 := by
    rw [sqdist X, ← norm_sq_eq_dot, eX2, hz', div_pow, mul_pow]
    field_simp [hCpos.ne']
  have hY : dist Y 0 ^ 2 = A * (A * C - y ^ 2) := by
    rw [sqdist Y, ← norm_sq_eq_dot, eY2]
    ring
  have hdXY : (dist X 0 * dist Y 0) ^ 2
      = (A * (A * B * C ^ 2 - x ^ 2 * y ^ 2) / C ^ 2) * (A * (A * C - y ^ 2)) := by
    rw [mul_pow, hX, hY]
  have hsg : 0 ≤ Real.cos (dihV 0 va vb vc) * (x / (Real.sqrt B * Real.sqrt C)) := by
    have heq : Real.cos (dihV 0 va vb vc) * (x / (Real.sqrt B * Real.sqrt C))
        = x * x * (A * (A * C - y ^ 2))
          / (C * (dist X 0 * dist Y 0) * (Real.sqrt B * Real.sqrt C)) := by
      rw [hca, k1, k2, k3]
      field_simp [hsqD, hsqP]
    rw [heq]
    exact div_nonneg (mul_nonneg (mul_self_nonneg x)
      (mul_nonneg hApos.le hP0.le)) (by positivity)
  -- ## algebra: squared identity + sign (explicit division chains, no field_simp
  -- on the assembly goals)
  -- 1 − q_b² = B * C * (A * C − y²) / D
  have hqbr2 : 1 - ((U ⬝ᵥ V)/(dist U 0 * dist V 0)) ^ 2
      = B * C * (A * C - y ^ 2) / (A * B * C ^ 2 - x ^ 2 * y ^ 2) := by
    rw [hqbr, one_sub_div hD0.ne']
    ring
  have hnneg : 0 ≤ 1 - ((U ⬝ᵥ V)/(dist U 0 * dist V 0)) ^ 2 := by
    rw [hqbr2]
    exact div_nonneg (mul_nonneg (mul_nonneg hBpos.le hCpos.le) hP0.le) hD0.le
  have hsinSq : (Real.sin (dihV 0 vb vc va)) ^ 2
      = 1 - ((U ⬝ᵥ V)/(dist U 0 * dist V 0)) ^ 2 := by
    rw [hcb, Real.sq_sqrt hnneg]
  have ht2 : (x / (Real.sqrt B * Real.sqrt C)) ^ 2 = x ^ 2 / (B * C) := by
    rw [div_pow, mul_pow, Real.sq_sqrt hBpos.le, Real.sq_sqrt hCpos.le]
  -- cross-multiplication for ℝ (the CommGroup `div_eq_div_iff_mul_eq_mul` does
  -- not unify with ℝ's DivisionRing `Div` instance)
  have divcross : ∀ {a b c d : ℝ}, b ≠ 0 → d ≠ 0 → a * d = c * b → a / b = c / d := by
    intro a b c d hb hd h
    refine mul_right_cancel₀ (mul_ne_zero hb hd) ?_
    rw [div_mul_eq_mul_div, mul_comm b d, ← mul_assoc, mul_div_cancel_right₀ _ hb,
      ← mul_assoc, div_mul_cancel₀ _ hd, h]
  have hR2 : (1 - ((U ⬝ᵥ V)/(dist U 0 * dist V 0)) ^ 2)
      * (x / (Real.sqrt B * Real.sqrt C)) ^ 2
      = x ^ 2 * (A * C - y ^ 2) / (A * B * C ^ 2 - x ^ 2 * y ^ 2) := by
    rw [hqbr2, ht2, div_mul_div_comm]
    exact divcross (by positivity) hD0.ne' (by ring)
  have hCcancel : ∀ w : ℝ, C ^ 2 * (w / C ^ 2) = w := by
    intro w
    rw [mul_comm]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hCpos.ne')
  have hcosval : (Real.cos (dihV 0 va vb vc)) ^ 2
      = x ^ 2 * (A * C - y ^ 2) / (A * B * C ^ 2 - x ^ 2 * y ^ 2) := by
    rw [hca, div_pow, k1, div_pow, hdXY, div_div, ← mul_assoc, hCcancel]
    exact divcross (by positivity) hD0.ne' (by ring)
  -- sign: sin ≥ 0, then squared equality + sign ⟹ equality
  have hsinpos : 0 ≤ Real.sin (dihV 0 vb vc va) := by
    rw [hcb]; exact Real.sqrt_nonneg _
  have eqOfSq : ∀ a b : ℝ, 0 ≤ a * b → a ^ 2 = b ^ 2 → a = b := by
    intro a b hprod hs
    have h1 : (a - b) * (a + b) = 0 := by
      have h2 : a ^ 2 - b ^ 2 = 0 := by rw [hs, sub_self]
      nlinarith
    rcases mul_eq_zero.mp h1 with h | h
    · linarith
    · have hab : a = -b := by linarith
      have hab2 : a * b = -(a * a) := by rw [hab]; ring
      have ha2 : 0 ≤ a * a := mul_self_nonneg a
      have haa : a * a = 0 := by linarith
      have ha0 : a = 0 := mul_self_eq_zero.mp haa
      linarith
  have hb : Real.sin (dihV 0 vb vc va) * Real.cos (arcV 0 vb vc)
      = Real.sin (dihV 0 vb vc va) * (x / (Real.sqrt B * Real.sqrt C)) := by
    rw [htv]
  have hprod : 0 ≤ Real.cos (dihV 0 va vb vc)
      * (Real.sin (dihV 0 vb vc va) * (x / (Real.sqrt B * Real.sqrt C))) := by
    rw [mul_comm (Real.sin (dihV 0 vb vc va)), ← mul_assoc]
    exact mul_nonneg hsg hsinpos
  have hprod2 : 0 ≤ Real.cos (dihV 0 va vb vc)
      * (Real.sin (dihV 0 vb vc va) * Real.cos (arcV 0 vb vc)) := by
    rw [hb]
    exact hprod
  refine eqOfSq (Real.cos (dihV 0 va vb vc))
    (Real.sin (dihV 0 vb vc va) * Real.cos (arcV 0 vb vc)) hprod2 ?_
  rw [mul_pow, htv, hsinSq, hR2]
  exact hcosval

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

/-- HOL `card_packing_ball` (counting_spheres.hl:1418). Filled: take
`n := Nat.ceil ((r + 1) ^ 3)`; finiteness is `Packing.finite_inter_ball` and
the bound volume-counts the unit balls `Metric.ball v 1` over a finset `T`
with `↑T = S` (`Set.Finite.exists_finset_coe`): they are pairwise disjoint
(`Packing.dist_ge_two` + triangle inequality) and all inside
`Metric.ball 0 (r + 1)`, so `MeasureTheory.measure_biUnion_finset` +
`EuclideanSpace.volume_ball_fin_three` give `T.card * (4π/3) ≤ (r+1)³ * (4π/3)`,
and `S.ncard = T.card` (`Set.ncard_coe_finset`). -/
theorem card_packing_ball (r : ℝ) (hr : 0 ≤ r) :
    ∃ n : ℕ, ∀ S : Set V3, Packing S → S ⊆ Metric.ball 0 r →
      S.Finite ∧ S.ncard ≤ n := by
  refine ⟨Nat.ceil ((r + 1) ^ 3), fun S hP hsub => ?_⟩
  have hfin : S.Finite := (hP.finite_inter_ball r).subset (fun v hv => ⟨hv, hsub hv⟩)
  refine ⟨hfin, ?_⟩
  obtain ⟨T, hT⟩ := hfin.exists_finset_coe
  have hmem : ∀ v ∈ T, dist v 0 < r := by
    intro v hv
    have hvS : v ∈ S := by rw [← hT]; exact hv
    exact Metric.mem_ball.mp (hsub hvS)
  have hdisj : (T : Set V3).PairwiseDisjoint (fun v => Metric.ball v 1) := by
    intro u hu v hv hne
    have hdist := hP.dist_ge_two (by rw [← hT]; exact hu) (by rw [← hT]; exact hv) hne
    simp only [Function.onFun]
    rw [disjoint_iff_inter_eq_empty]
    by_contra hne'
    obtain ⟨w, hwu, hwv⟩ := Set.nonempty_iff_ne_empty.mpr hne'
    have : dist u v ≤ dist u w + dist w v := dist_triangle u w v
    rw [Metric.mem_ball] at hwu hwv
    linarith [dist_comm u w ▸ hwu]
  have hsub : (⋃ v ∈ T, Metric.ball v 1) ⊆ Metric.ball 0 (r + 1) := by
    intro w hw
    simp only [mem_iUnion, exists_prop] at hw
    obtain ⟨v, hvT, hwv⟩ := hw
    have hvr := hmem v hvT
    rw [Metric.mem_ball] at hwv ⊢
    calc dist w 0 ≤ dist w v + dist v 0 := dist_triangle w v 0
      _ < 1 + r := by linarith
      _ = r + 1 := by ring
  have hmeas : ∀ v ∈ T, MeasurableSet (Metric.ball v 1) :=
    fun v _ => measurableSet_ball
  have hsum := MeasureTheory.measure_biUnion_finset hdisj hmeas (μ := MeasureTheory.volume)
  have hle := MeasureTheory.measure_mono hsub (μ := MeasureTheory.volume)
  rw [hsum] at hle
  simp only [EuclideanSpace.volume_ball_fin_three] at hle
  simp only [ENNReal.ofReal_one, one_pow, one_mul] at hle
  rw [Finset.sum_const, nsmul_eq_mul] at hle
  have hr1 : (0 : ℝ) ≤ r + 1 := by linarith
  rw [← ENNReal.ofReal_pow hr1, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hcard : (T.card : ℝ) ≤ (r + 1) ^ 3 := by nlinarith [Real.pi_pos]
  have hncard : S.ncard = T.card := by
    rw [← hT]
    exact Set.ncard_coe_finset T
  rw [hncard]
  have h2 : (T.card : ℝ) ≤ (Nat.ceil ((r + 1) ^ 3) : ℝ) := le_trans hcard (Nat.le_ceil _)
  exact_mod_cast h2

/-- HOL `card_packing_annulus` (counting_spheres.hl:1454). Filled: immediate
corollary of `card_packing_ball` at radius `2*h0 + 1`
(`ballAnnulus = closedBall 0 (2*h0) \ ball 0 2 ⊆ Metric.ball 0 (2*h0+1)`,
`h0 = 1.26`). -/
theorem card_packing_annulus :
    ∃ n : ℕ, ∀ S : Set V3, Packing S → S ⊆ ballAnnulus →
      S.Finite ∧ S.ncard ≤ n := by
  obtain ⟨n, hn⟩ := card_packing_ball (2 * h0 + 1) (by norm_num [h0])
  refine ⟨n, fun S hP hsub => hn S hP ?_⟩
  intro v hv
  exact Metric.closedBall_subset_ball (by linarith) (Metric.mem_closedBall.mpr (hsub hv).1)

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
  -- under the `weaklySaturatedP22` stub (= True) the extension `V := W`
  -- already satisfies every conjunct; finiteness is `fat_lemma1`.
  exact ⟨W, hW, hP, trivial, fat_lemma1 W hP hW, le_refl W, hsep⟩

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

/-! ## `pad2d3d_facet` support kit: the linear-image facet transfer
(V3-side mirror + `FACET_OF_LINEAR_IMAGE` ℂ-versions).  The plane `z = 0` is
linearly isomorphic to `ℂ` via `pad2d3dP22`/`dropout3P22`; faces, facet
dimensions and facet counts transport along it.  All items private, consumed
by `pad2d3d_facet`. -/

/-- Equality of `V3` points reduces to component equality. -/
private theorem p22_v3_eq {a b : V3} (h : (a : Fin 3 → ℝ) = (b : Fin 3 → ℝ)) : a = b := by
  rw [← WithLp.toLp_ofLp 2 a, ← WithLp.toLp_ofLp 2 b, h]

/-- `pad2d3dP22` as a linear map `ℂ →ₗ[ℝ] V3`. -/
private def padLin : ℂ →ₗ[ℝ] V3 where
  toFun := pad2d3dP22
  map_add' := by
    intro z w
    refine p22_v3_eq ?_
    funext i
    fin_cases i <;> simp [pad2d3dP22]
  map_smul' := by
    intro t z
    refine p22_v3_eq ?_
    funext i
    fin_cases i <;> simp [pad2d3dP22, Complex.real_smul, Complex.mul_re]

/-- `dropout3P22` as a linear map `V3 →ₗ[ℝ] ℂ`. -/
private def dropLin : V3 →ₗ[ℝ] ℂ where
  toFun := dropout3P22
  map_add' := by
    intro u v
    refine Complex.ext ?_ ?_ <;> simp [dropout3P22]
  map_smul' := by
    intro t u
    refine Complex.ext ?_ ?_ <;> simp [dropout3P22, Complex.real_smul, Complex.mul_re]

private theorem padLin_apply (z : ℂ) : padLin z = pad2d3dP22 z := rfl

private theorem dropLin_apply (v : V3) : dropLin v = dropout3P22 v := rfl

/-- `pad2d3dP22` is injective (left inverse `dropout3P22`). -/
private theorem padLin_inj : Function.Injective padLin := by
  intro u v h
  have h2 : dropout3P22 (padLin u) = dropout3P22 (padLin v) := congrArg dropout3P22 h
  rw [padLin_apply, padLin_apply, dropout_pad2d3d, dropout_pad2d3d] at h2
  exact h2

/-- The `z = 0` plane as a submodule of `V3`. -/
private def planeP22 : Submodule ℝ V3 where
  carrier := {v : V3 | (v : Fin 3 → ℝ) 2 = 0}
  add_mem' := by
    intro u v hu hv
    have h2 : ((u + v : V3) : Fin 3 → ℝ) 2 = (u : Fin 3 → ℝ) 2 + (v : Fin 3 → ℝ) 2 := rfl
    show ((u + v : V3) : Fin 3 → ℝ) 2 = 0
    rw [h2, Set.mem_setOf_eq.mp hu, Set.mem_setOf_eq.mp hv]
    ring
  zero_mem' := rfl
  smul_mem' := by
    intro t v hv
    have h2 : ((t • v : V3) : Fin 3 → ℝ) 2 = t * ((v : Fin 3 → ℝ) 2) := rfl
    show ((t • v : V3) : Fin 3 → ℝ) 2 = 0
    rw [h2, Set.mem_setOf_eq.mp hv]
    ring

private theorem mem_planeP22 {v : V3} : v ∈ planeP22 ↔ (v : Fin 3 → ℝ) 2 = 0 := Iff.rfl

private theorem planeP22_convex : Convex ℝ (planeP22 : Set V3) := Submodule.convex _

/-- `dropout3P22` is injective on the `z = 0` plane. -/
private theorem dropLin_injOn_plane :
    ∀ u ∈ planeP22, ∀ v ∈ planeP22, dropLin u = dropLin v → u = v := by
  intro u hu v hv h
  have h1 : pad2d3dP22 (dropLin u) = pad2d3dP22 (dropLin v) := congrArg _ h
  rw [dropLin_apply, dropLin_apply,
    pad2d3d_dropout u (mem_planeP22.1 hu), pad2d3d_dropout v (mem_planeP22.1 hv)] at h1
  exact h1

/-- Segment images under a linear map. -/
private theorem p22_image_openSegment {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (g : E →ₗ[ℝ] F) (a b : E) :
    g '' openSegment ℝ a b = openSegment ℝ (g a) (g b) := by
  ext x
  simp only [Set.mem_image, openSegment, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨c, d, hc, hd, hcd, rfl⟩, rfl⟩
    exact ⟨c, d, hc, hd, hcd, by rw [map_add, map_smul, map_smul]⟩
  · rintro ⟨c, d, hc, hd, hcd, rfl⟩
    exact ⟨c • a + d • b, ⟨c, d, hc, hd, hcd, rfl⟩, by rw [map_add, map_smul, map_smul]⟩

/-- Face-of bodies transport along a linear map injective on a convex superset. -/
private theorem p22_faceBody_image {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (g : E →ₗ[ℝ] F) (p : Submodule ℝ E) {s t : Set E}
    (hsub : t ⊆ s) (hs : s ⊆ ↑p) (hinj : ∀ u ∈ p, ∀ v ∈ p, g u = g v → u = v)
    (hconv : Convex ℝ t)
    (hseg : ∀ a b x : E, a ∈ s → b ∈ s → x ∈ t → x ∈ openSegment ℝ a b → a ∈ t ∧ b ∈ t) :
    g '' t ⊆ g '' s ∧ Convex ℝ (g '' t) ∧
      ∀ a b x : F, a ∈ g '' s → b ∈ g '' s → x ∈ g '' t →
        x ∈ openSegment ℝ a b → a ∈ g '' t ∧ b ∈ g '' t := by
  have hinjp : Function.Injective (LinearMap.comp g p.subtype) := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    exact Subtype.ext (hinj u hu v hv huv)
  refine ⟨Set.image_mono hsub, ?_, ?_⟩
  · -- convexity of the image
    rw [convex_iff_segment_subset] at hconv ⊢
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    intro x hx
    obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hx
    exact ⟨c • a' + d • b',
      hconv ha' hb' ⟨c, d, hc, hd, hcd, rfl⟩,
      by rw [map_add, map_smul, map_smul]⟩
  · -- the segment condition
    intro a b x ha hb hx hopen
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨x', hx', rfl⟩ := hx
    rw [← p22_image_openSegment] at hopen
    obtain ⟨x'', hx''seg, hx''eq⟩ := hopen
    -- place `x''` in `p` via convexity
    have hx''p : (x'' : E) ∈ p := by
      have h3 : (x'' : E) ∈ segment ℝ (a' : E) (b' : E) :=
        (openSegment_subset_segment (𝕜 := ℝ) a' b') hx''seg
      exact convex_iff_segment_subset.mp (Submodule.convex p) (hs ha') (hs hb') h3
    have hx'p : (x' : E) ∈ p := hs (hsub hx')
    have hxeq : x' = x'' := hinj x' hx'p x'' hx''p hx''eq.symm
    obtain ⟨ha't, hb't⟩ :=
      hseg a' b' x' ha' hb' hx' (by rw [hxeq]; exact hx''seg)
    exact ⟨⟨a', ha't, rfl⟩, ⟨b', hb't, rfl⟩⟩

/-- finrank of the vector span is preserved by a linear map injective on a
superset submodule. -/
private theorem p22_finrank_vectorSpan_image {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (g : E →ₗ[ℝ] F) (p : Submodule ℝ E)
    (hinj : ∀ u ∈ p, ∀ v ∈ p, g u = g v → u = v) {s : Set E} (hs : s ⊆ ↑p) :
    Module.finrank ℝ (vectorSpan ℝ (g '' s)) = Module.finrank ℝ (vectorSpan ℝ s) := by
  have hvseq : vectorSpan ℝ (g '' s) = Submodule.map g (vectorSpan ℝ s) := by
    have h := AffineMap.map_vectorSpan (f := g.toAffineMap) (s := s)
    simp only [LinearMap.coe_toAffineMap, LinearMap.toAffineMap_linear] at h
    exact h.symm
  have hvp : vectorSpan ℝ (p : Set E) ≤ p := by
    rw [vectorSpan_def, Submodule.span_le]
    intro d hd
    obtain ⟨x, hx, y, hy, rfl⟩ := hd
    exact p.sub_mem hx hy
  have hqle : (vectorSpan ℝ s : Submodule ℝ E) ≤ p := (vectorSpan_mono ℝ hs).trans hvp
  have hinjq : Function.Injective (LinearMap.comp g (vectorSpan ℝ s).subtype) := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    exact Subtype.ext (hinj u (hqle hu) v (hqle hv) huv)
  have hrange : Submodule.map g (vectorSpan ℝ s)
      = LinearMap.range (LinearMap.comp g (vectorSpan ℝ s).subtype) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.coe_comp,
      Submodule.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨y, hy⟩; exact ⟨y, y.2, hy⟩
  rw [hvseq, hrange, LinearMap.finrank_range_of_inj hinjq]

/-- `affDim` is preserved by `pad2d3dP22`. -/
private theorem p22_affDim_image_pad (s : Set ℂ) :
    affDim (pad2d3dP22 '' s) = affDimC s := by
  simp only [affDim, affDimC]
  by_cases hse : s = ∅
  · subst hse
    simp
  · have hne : pad2d3dP22 '' s ≠ ∅ := fun hc => hse (Set.image_eq_empty.mp hc)
    simp only [if_neg hne, if_neg hse]
    exact congrArg ((↑) : ℕ → ℤ) (p22_finrank_vectorSpan_image padLin ⊤
      (fun u _hu v _hv h => padLin_inj h) (fun _u _ => Submodule.mem_top))

/-- `affDimC` is preserved by `dropout3P22` on the plane. -/
private theorem p22_affDim_image_drop {s : Set V3} (hs : ∀ u ∈ s, (u : Fin 3 → ℝ) 2 = 0) :
    affDimC (dropout3P22 '' s) = affDim s := by
  simp only [affDim, affDimC]
  by_cases hse : s = ∅
  · subst hse
    simp
  · have hne : dropout3P22 '' s ≠ ∅ := fun hc => hse (Set.image_eq_empty.mp hc)
    simp only [if_neg hne, if_neg hse]
    exact congrArg ((↑) : ℕ → ℤ) (p22_finrank_vectorSpan_image dropLin planeP22
      dropLin_injOn_plane (fun u hu => mem_planeP22.2 (hs u hu)))

/-- `pad2d3dP22 (dropout3P22 '' t) = t` for plane subsets. -/
private theorem p22_pad_drop_image {t : Set V3} (ht : ∀ u ∈ t, (u : Fin 3 → ℝ) 2 = 0) :
    pad2d3dP22 '' (dropout3P22 '' t) = t := by
  ext u
  simp only [Set.mem_image]
  constructor
  · rintro ⟨z, ⟨u', hu', rfl⟩, rfl⟩
    rwa [pad2d3d_dropout u' (ht u' hu')]
  · intro hu
    exact ⟨dropout3P22 u, ⟨u, hu, rfl⟩, pad2d3d_dropout u (ht u hu)⟩

/-- Forward transfer: a `V3` facet of `P` maps to a `ℂ` facet of the dropout
image (`FACET_OF_LINEAR_IMAGE`, V3 → ℂ direction). -/
private theorem p22_facetOfC_of_FacetOf {P c : Set V3}
    (hz : ∀ u ∈ P, (u : Fin 3 → ℝ) 2 = 0) (hfc : FacetOf c P) :
    facetOfC (dropout3P22 '' c) (dropout3P22 '' P) := by
  have hcsub : c ⊆ P := hfc.1.1
  obtain ⟨bsub, bconv, bseg⟩ :=
    p22_faceBody_image dropLin planeP22 hcsub
      (fun u hu => mem_planeP22.2 (hz u hu)) dropLin_injOn_plane hfc.1.2.1 hfc.1.2.2
  refine ⟨⟨bsub, bconv, bseg⟩, ?_, ?_⟩
  · intro hc0
    exact hfc.2.1 (Set.image_eq_empty.mp hc0)
  · rw [p22_affDim_image_drop (fun u hu => hz u (hcsub hu)), p22_affDim_image_drop hz]
    exact hfc.2.2

/-- Backward transfer: a `ℂ` facet of the dropout image lifts to a `V3` facet
of `P` (`FACET_OF_LINEAR_IMAGE`, ℂ → V3 direction). -/
private theorem p22_FacetOf_of_facetOfC {P : Set V3} (hz : ∀ u ∈ P, (u : Fin 3 → ℝ) 2 = 0)
    {d : Set ℂ} (hdf : facetOfC d (dropout3P22 '' P)) :
    FacetOf (pad2d3dP22 '' d) P := by
  have hQpad : pad2d3dP22 '' (dropout3P22 '' P) = P := p22_pad_drop_image hz
  have hdsub : d ⊆ dropout3P22 '' P := hdf.1.1
  obtain ⟨bsub, bconv, bseg⟩ :=
    p22_faceBody_image padLin ⊤ hdsub (fun _ _ => Submodule.mem_top)
      (fun u _hu v _hv h => padLin_inj h) hdf.1.2.1 hdf.1.2.2
  simp only [padLin_apply] at bsub bseg
  rw [hQpad] at bsub bseg
  refine ⟨⟨bsub, bconv, bseg⟩, ?_, ?_⟩
  · have h1 : d.Nonempty := Set.nonempty_iff_ne_empty.mpr hdf.2.1
    have h2 : (pad2d3dP22 '' d).Nonempty := Set.image_nonempty.mpr h1
    exact Set.nonempty_iff_ne_empty.mp h2
  · rw [p22_affDim_image_pad, ← hQpad, p22_affDim_image_pad]
    exact hdf.2.2

/-- HOL `pad2d3d_facet` (counting_spheres.hl:1737). GIANT. -/
theorem pad2d3d_facet (P : Set V3) (n : ℕ) (hP : polyhedron P)
    (hz : ∀ u ∈ P, (u : Fin 3 → ℝ) 2 = 0)
    (hn : ({c : Set V3 | FacetOf c P}).Finite ∧ ({c : Set V3 | FacetOf c P}).ncard = n) :
    ({d : Set ℂ | facetOfC d (dropout3P22 '' P)}).Finite ∧
      ({d : Set ℂ | facetOfC d (dropout3P22 '' P)}).ncard = n := by
  -- The facet family transports along the linear plane-isomorphism
  -- `pad2d3dP22 : ℂ ≃ (z = 0)` / `dropout3P22` (dropout_pad2d3d /
  -- pad2d3d_dropout): the FACET_OF_LINEAR_IMAGE ℂ-versions
  -- `p22_facetOfC_of_FacetOf` / `p22_FacetOf_of_facetOfC` above transfer facets
  -- both ways, so `{d | facetOfC d (dropout3P22 '' P)}` is exactly the image of
  -- the V3 facet family under `c ↦ dropout3P22 '' c` (`BIJECTIONS_HAS_SIZE`
  -- route); injectivity of that map on the plane gives the ncard transport.
  have hseteq : {d : Set ℂ | facetOfC d (dropout3P22 '' P)}
      = (fun c => dropout3P22 '' c) '' {c : Set V3 | FacetOf c P} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hd
      refine ⟨pad2d3dP22 '' d, p22_FacetOf_of_facetOfC hz hd, ?_⟩
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨w, ⟨w₀, hw₀, rfl⟩, rfl⟩
        rw [dropout_pad2d3d]
        exact hw₀
      · intro hz'
        exact ⟨pad2d3dP22 z, ⟨z, hz', rfl⟩, dropout_pad2d3d z⟩
    · rintro ⟨c, hc, rfl⟩
      exact p22_facetOfC_of_FacetOf hz hc
  refine ⟨?_, ?_⟩
  · rw [hseteq]
    exact hn.1.image (fun c => dropout3P22 '' c)
  · rw [hseteq]
    refine (Set.InjOn.ncard_image ?_).trans hn.2
    intro c1 hc1 c2 hc2 heq
    have h1 : pad2d3dP22 '' (dropout3P22 '' c1) = c1 :=
      p22_pad_drop_image (fun u hu => hz u (hc1.1.1 hu))
    have h2 : pad2d3dP22 '' (dropout3P22 '' c2) = c2 :=
      p22_pad_drop_image (fun u hu => hz u (hc2.1.1 hu))
    calc c1 = pad2d3dP22 '' (dropout3P22 '' c1) := h1.symm
      _ = pad2d3dP22 '' (dropout3P22 '' c2) := congrArg (fun S => pad2d3dP22 '' S) heq
      _ = c2 := h2

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

/-- HOL `ARG_INV_ALT` (counting_spheres.hl:1791), restated over `holArg`
(the faithful HOL `Arg`): for nonzero `u x y` with distinct `holArg (x/u)`,
`holArg (y/u)`, the angle from `y` to `x` complements the angle from `x` to
`y` to `2π`. -/
theorem ARG_INV_ALT (u x y : ℂ) (hu : u ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : holArg (x / u) ≠ holArg (y / u)) :
    holArg (x / y) = 2 * Real.pi - holArg (y / x) := by
  have hlu : ∀ z : ℂ, holArg z =
      if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi :=
    fun z => rfl
  have hxy : x / y = (y / x)⁻¹ := by field_simp
  -- the hypothesis forces `arg (y/x) ≠ 0`
  have hargne : Complex.arg (y / x) ≠ 0 := by
    intro h0
    have hzx : 0 ≤ (y / x).re ∧ (y / x).im = 0 := Complex.arg_eq_zero_iff.mp h0
    have hre : 0 < (y / x).re := by
      have hzne : (y / x).re ≠ 0 := by
        intro he
        have hzero : y / x = 0 := Complex.ext (by simpa using he) (by simpa using hzx.2)
        exact div_ne_zero hy hx hzero
      exact lt_of_le_of_ne hzx.1 (Ne.symm hzne)
    have hzre : y / x = ((y / x).re : ℂ) := Complex.ext rfl (by simpa using hzx.2)
    have h1 : x / u = (y / x)⁻¹ * (y / u) := by field_simp
    have h2 : (y / x)⁻¹ = (↑(((y / x).re)⁻¹) : ℂ) := by
      rw [congrArg Inv.inv hzre, ← Complex.ofReal_inv]
    have harg2 : Complex.arg (x / u) = Complex.arg (y / u) := by
      rw [h1, h2, Complex.arg_real_mul (y / u) (inv_pos.mpr hre)]
    exfalso
    have hne : holArg (x / u) = holArg (y / u) := by simp only [hlu, harg2]
    exact h hne
  rcases eq_or_lt_of_le (Complex.arg_le_pi (y / x)) with hπ | hlt
  · -- `arg (y/x) = π`: both sides equal `π`
    have hxarg : Complex.arg (x / y) = Real.pi := by
      rw [hxy, Complex.arg_inv, if_pos hπ]
    have hp : (0:ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    rw [hlu, hlu, hπ, hxarg, if_pos hp]
    ring
  · rw [hlu, hlu, hxy, Complex.arg_inv, if_neg (ne_of_lt hlt)]
    by_cases hge : 0 ≤ Complex.arg (y / x)
    · have hpos : 0 < Complex.arg (y / x) := lt_of_le_of_ne hge (Ne.symm hargne)
      rw [if_pos hge, if_neg (by linarith : ¬ (0:ℝ) ≤ -Complex.arg (y / x))]
      ring
    · have hneg : Complex.arg (y / x) < 0 := not_le.mp hge
      rw [if_pos (by linarith : (0:ℝ) ≤ -Complex.arg (y / x)), if_neg hge]
      ring

/-- HOL `ARG_ORDER` (counting_spheres.hl:1822). GIANT.
SF22 statement-fix (minesweep report §3): the `Complex.arg`s (range
`(-π, π]`) are lifted to `holArg` (range `[0, 2π)`, the Ysskqoy `Arg` kit,
cf. the definition at the top of this file).  The previous `Complex.arg`
version was FALSE — counterexample: `u := 1`, `n := 3`, `h 1 := exp(-I*π/2)`,
`h 2 := exp(I*(π/2-0.1))`, `h 3 := -1`, `h k := h 1` for `k ≥ 4`.  All
hypotheses hold (`arg h1 = -π/2 < arg h2 = π/2 - 0.1 < arg h3 = π`;
`h 4 = h 1`), yet for `(i, j) := (1, 3)`:
`arg (h 2 / h 1) = arg (exp (I*(π-0.1))) = π - 0.1 ≈ 3.0416 >
-π/2 ≈ -1.5708 = arg (exp (I*3π/2)) = arg (h 3 / h 1)`.  Over `holArg` the
hypotheses express the HOL cyclic order and the flyspeck proof applies
(ARG_LE_DIV_SUM: `Arg(z2/z1) = Arg z2 - Arg z1` for `0 ≤ Arg z1 < Arg z2`). -/
theorem ARG_ORDER (u : ℂ) (h : ℕ → ℂ) (n : ℕ) (hu : u ≠ 0)
    (h1 : ∀ i : ℕ, i ∈ Finset.Icc 1 n → h i ≠ 0)
    (h2 : ∀ i j : ℕ, i ∈ Finset.Icc 1 n → j ∈ Finset.Icc 1 n → i < j →
      holArg (h i / u) < holArg (h j / u))
    (h3 : h (n + 1) = h 1) :
    ∀ i j : ℕ, i ∈ Finset.Icc 1 n → j ∈ Finset.Icc 1 n → i ≠ j →
      holArg (h (i + 1) / h i) ≤ holArg (h j / h i) := by
  sorry

/-- HOL `POLYSORT_BIJ2` (counting_spheres.hl:1964). GIANT.
SF27 statement-fix (minesweep report §3): the three `Complex.arg` comparisons
are lifted to `holArg` (range `[0, 2π)`, the faithful HOL `Arg`) — same
defect class as `poly_sort_fn` above: the principal-value order is not the
cyclic order, so the flyspeck sorted-bijection conclusion cannot be phrased
over `Complex.arg`. -/
theorem POLYSORT_BIJ2 (P : Set ℂ) (n : ℕ) (s : Set (Set ℂ)) (r : ℝ) (u : ℂ)
    (hs : s = {c : Set ℂ | facetOfC c P}) (hb : Bornology.IsBounded P) (hP : polyhedronC P)
    (hr : 0 < r) (hrad : ∀ p : ℂ, ‖p‖ < r → p ∈ P) (hu : u ≠ 0)
    (hsize : s.Finite ∧ s.ncard = n) :
    ∃ f : ℕ → Set ℂ, s = f '' Set.Icc 1 n ∧ Set.BijOn f (Set.Icc 1 n) s ∧
      (∀ i k : ℕ, i ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → i ≠ k →
        holArg (facet_rep_a P (f (i + 1)) / facet_rep_a P (f i)) ≤
          holArg (facet_rep_a P (f k) / facet_rep_a P (f i))) ∧
      (∀ i : ℕ, i ∈ Set.Icc 1 n →
        holArg (facet_rep_a P (f (i + 1)) / facet_rep_a P (f i)) < Real.pi) ∧
      f (n + 1) = f 1 ∧
      (∀ j k : ℕ, j ∈ Set.Icc 1 n → k ∈ Set.Icc 1 n → j < k →
        holArg (facet_rep_a P (f j) / u) <
          holArg (facet_rep_a P (f k) / u)) := by
  sorry -- DEF-FIX: refill per counting_spheres.hl:1964 §3a

/-- HOL `EMPTY_NOT_EXISTS_IN` (counting_spheres.hl:2104). -/
theorem EMPTY_NOT_EXISTS_IN {α : Type*} (a : Set α) :
    a = ∅ ↔ ¬ ∃ x : α, x ∈ a := by
  simp [Set.eq_empty_iff_forall_notMem]

/-- HOL `EUSOTYP_simple` (counting_spheres.hl:2112). GIANT.
SF27 statement-fix (minesweep report §3): all `Complex.arg`s are lifted to
`holArg` (range `[0, 2π)`, the faithful HOL `Arg`) — the sorted `g`-walk and
the half-angle hypotheses around the facet cycle need the cyclic `[0, 2π)`
order (`Real.cos` of a half principal arg would not match the HOL `Arg`
values, and the `g`-sort over `(-π, π]` is not the walk order). -/
theorem EUSOTYP_simple (P : Set ℂ) (s : Set (Set ℂ)) (r n : ℕ) (u2 : ℂ)
    (hP : polyhedronC P) (hb : Bornology.IsBounded P) (hs : s = {c : Set ℂ | facetOfC c P})
    (hsize : s.Finite ∧ s.ncard = n) (hr : 0 < r) (hu : u2 ≠ 0)
    (hrad : ∀ p2 : ℂ, ‖p2‖ < r → p2 ∈ P) :
    ∃ g h : ℕ → ℂ,
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → g i ∈ P ∧ ‖g i‖ = r) ∧
      g (n + 1) = g 1 ∧
      (∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j < k →
        holArg (g j / u2) < holArg (g k / u2)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → h i ∈ P ∧
        ‖h i‖ = r / Real.cos (holArg (g (i + 1) / g i) / 2)) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        holArg (h i / g i) = holArg (g (i + 1) / g i) / 2 ∧
        holArg (g (i + 1) / h i) = holArg (g (i + 1) / g i) / 2) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n →
        dot2 (g i) (h i - g i) = 0 ∧ dot2 (g (i + 1)) (h i - g (i + 1)) = 0) ∧
      1 < n ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → g i ≠ 0) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → h i ≠ 0) ∧
      (∀ i : ℕ, i ∈ Finset.Icc 1 n → holArg (g (i + 1) / g i) < Real.pi) := by
  sorry -- DEF-FIX: refill per counting_spheres.hl:2112 §3a

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

/-! ### azim-order toolkit (local helpers for the wedge/sum block below)

`sum4_azim_fan`/`sum5_azim_fan` (TopologyFan) give the three-point addition
formula `azim x v u w2 = azim x v u w1 + azim x v w1 w2` under an order
hypothesis; `azim_compl` (Geom.AzimLemmas) is the complement
`azim z w w2 w1 = 2π - azim z w w1 w2` off the degenerate zero. -/

/-- `¬ Collinear3 x y z` separates the two axis points. -/
private theorem p22_y_ne_x {x y z : V3} (h : ¬ Collinear3 x y z) : y ≠ x := by
  intro hxy
  exact h (by rw [hxy]; exact collinear3_of_eq rfl)

/-- Wedge membership pins `p` between `u` and `u'` in the `azim x y z ·`
order: `p ∈ wedge x y u u'` and the cycle order `azim x y z u ≤ azim x y z u'`
give `azim x y z u < azim x y z p < azim x y z u'`. -/
private theorem p22_wedge_bounds {x y z p u u' : V3} (hxy : y ≠ x)
    (hz : ¬ Collinear3 x y z) (hp : ¬ Collinear3 x y p) (hu : ¬ Collinear3 x y u)
    (hu' : ¬ Collinear3 x y u')
    (hpw : p ∈ wedge x y u u') (hord : azim x y z u ≤ azim x y z u') :
    azim x y z u < azim x y z p ∧ azim x y z p < azim x y z u' := by
  have hdec : azim x y z u' = azim x y z u + azim x y u u' :=
    sum4_azim_fan hxy hz hu hu' hord
  rw [wedge, Set.mem_setOf_eq] at hpw
  obtain ⟨-, hpa, hpb⟩ := hpw
  rcases le_total (azim x y z u) (azim x y z p) with hc | hc
  · have hcp : azim x y z p = azim x y z u + azim x y u p :=
      sum4_azim_fan hxy hz hu hp hc
    exact ⟨by linarith, by linarith⟩
  · exfalso
    have hcp : azim x y z u = azim x y z p + azim x y p u :=
      sum4_azim_fan hxy hz hp hu hc
    have hcu : azim x y p u ≠ 0 := by
      intro h0
      have h := azim_compl hp hu
      rw [if_pos h0] at h
      linarith
    have hcomp : azim x y u p = 2 * Real.pi - azim x y p u := by
      have h := azim_compl hp hu
      rwa [if_neg hcu] at h
    have hlt := azim_lt_two_pi x y z u'
    have hnn := azim_nonneg x y z p
    linarith

/-- Telescope over `Icc 1 m`: the sum of forward differences is the last
value minus the first. -/
private theorem p22_telescope (A : ℕ → ℝ) :
    ∀ m : ℕ, 1 ≤ m → ∑ i ∈ Finset.Icc 1 m, (A (i + 1) - A i) = A (m + 1) - A 1 := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ k ih =>
    intro hm
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have h1 : Finset.Icc 1 1 = {1} := by simp
      rw [h1, Finset.sum_singleton]
    · have hk1 : 1 ≤ k := by omega
      rw [Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ k + 1)
        (fun i => A (i + 1) - A i), ih hk1]
      ring

/-- HOL `AZIM_SUM_LE` (counting_spheres.hl:2430). GIANT. -/
theorem AZIM_SUM_LE (x y z w1 w2 w3 : V3)
    (h1 : ¬ Collinear3 x y z) (h2 : ¬ Collinear3 x y w1) (h3 : ¬ Collinear3 x y w2)
    (h4 : ¬ Collinear3 x y w3)
    (h5 : azim x y z w1 ≤ azim x y z w2) (h6 : azim x y z w2 ≤ azim x y z w3) :
    azim x y w1 w3 = azim x y w1 w2 + azim x y w2 w3 := by
  have hxy : y ≠ x := p22_y_ne_x h1
  have e12 := sum4_azim_fan hxy h1 h2 h3 h5
  have e23 := sum4_azim_fan hxy h1 h3 h4 h6
  have e13 := sum4_azim_fan hxy h1 h2 h4 (h5.trans h6)
  linarith

/-- HOL `AZIM_NN` (counting_spheres.hl:2454). -/
theorem AZIM_NN (x y z u : V3) : 0 ≤ azim x y z u := azim_nonneg x y z u

/-- HOL `AZIM_BASE_SHIFT_LT` (counting_spheres.hl:2463). GIANT. -/
theorem AZIM_BASE_SHIFT_LT (x y z z' w1 w2 w3 : V3)
    (h1 : ¬ Collinear3 x y z) (h2 : ¬ Collinear3 x y z') (h3 : ¬ Collinear3 x y w1)
    (h4 : ¬ Collinear3 x y w2) (h5 : ¬ Collinear3 x y w3)
    (h6 : azim x y z w1 < azim x y z w2) (h7 : azim x y z w2 < azim x y z w3)
    (h8 : azim x y z' w1 < azim x y z' w3) :
    azim x y z' w1 < azim x y z' w2 ∧ azim x y z' w2 < azim x y z' w3 := by
  have hxy : y ≠ x := p22_y_ne_x h1
  have e12 := sum4_azim_fan hxy h1 h3 h4 h6.le
  have e23 := sum4_azim_fan hxy h1 h4 h5 h7.le
  have e13 := sum4_azim_fan hxy h1 h3 h5 (h6.le.trans h7.le)
  have e8 := sum4_azim_fan hxy h2 h3 h5 h8.le
  have hw12 : 0 < azim x y w1 w2 := by linarith
  have hw23 : 0 < azim x y w2 w3 := by linarith
  rcases le_total (azim x y z' w1) (azim x y z' w2) with hc | hc
  · have e' := sum4_azim_fan hxy h2 h3 h4 hc
    refine ⟨by linarith, by linarith⟩
  · exfalso
    have e' := sum4_azim_fan hxy h2 h4 h3 hc
    have hcomp : azim x y w2 w1 = 2 * Real.pi - azim x y w1 w2 := by
      have h := azim_compl h3 h4
      rwa [if_neg (ne_of_gt hw12)] at h
    have hlt := azim_lt_two_pi x y z' w3
    have hnn := azim_nonneg x y z' w2
    linarith

/-- HOL `AZIM_COMP_LT` (counting_spheres.hl:2513). Filled as in HOL:
complement both sides (`azim_compl`, i.e. `AZIM_COMPL_EXT`, proved locally to
avoid the PackingAuto6/PackingAuto7 name clash) and finish by order
arithmetic with `azim_nonneg`/`azim_lt_two_pi`. -/
theorem AZIM_COMP_LT (x y z u v : V3) (h1 : 0 < azim x y z u)
    (h2 : azim x y z u < azim x y z v) : azim x y v z < azim x y u z := by
  have hzu : azim x y z u ≠ 0 := ne_of_gt h1
  have e1 : azim x y v z =
      if azim x y z v = 0 then (0:ℝ) else 2 * Real.pi - azim x y z v := by
    by_cases hc1 : Collinear3 x y z
    · simp [azim, hc1]
    · by_cases hc2 : Collinear3 x y v
      · simp [azim, hc2]
      · exact azim_compl hc1 hc2
  have e2 : azim x y u z =
      if azim x y z u = 0 then (0:ℝ) else 2 * Real.pi - azim x y z u := by
    by_cases hc1 : Collinear3 x y z
    · simp [azim, hc1]
    · by_cases hc2 : Collinear3 x y u
      · simp [azim, hc2]
      · exact azim_compl hc1 hc2
  rw [e1, e2, if_neg hzu]
  by_cases hv0 : azim x y z v = 0
  · rw [if_pos hv0]
    have hnn := azim_nonneg x y z u
    have hlt := azim_lt_two_pi x y z u
    linarith
  · rw [if_neg hv0]
    linarith

/-- HOL `AZIM_COMP_LE` (counting_spheres.hl:2524). Filled as `AZIM_COMP_LT`. -/
theorem AZIM_COMP_LE (x y z u v : V3) (h1 : 0 < azim x y z u)
    (h2 : azim x y z u ≤ azim x y z v) : azim x y v z ≤ azim x y u z := by
  have hzu : azim x y z u ≠ 0 := ne_of_gt h1
  have e1 : azim x y v z =
      if azim x y z v = 0 then (0:ℝ) else 2 * Real.pi - azim x y z v := by
    by_cases hc1 : Collinear3 x y z
    · simp [azim, hc1]
    · by_cases hc2 : Collinear3 x y v
      · simp [azim, hc2]
      · exact azim_compl hc1 hc2
  have e2 : azim x y u z =
      if azim x y z u = 0 then (0:ℝ) else 2 * Real.pi - azim x y z u := by
    by_cases hc1 : Collinear3 x y z
    · simp [azim, hc1]
    · by_cases hc2 : Collinear3 x y u
      · simp [azim, hc2]
      · exact azim_compl hc1 hc2
  rw [e1, e2, if_neg hzu]
  by_cases hv0 : azim x y z v = 0
  · rw [if_pos hv0]
    have hnn := azim_nonneg x y z u
    have hlt := azim_lt_two_pi x y z u
    linarith
  · rw [if_neg hv0]
    linarith

/-- Core of `WEDGE_ORDER_DISJOINT`: for `j < k` the two cyclic wedges are
disjoint.  Interval wedges `[g j, g (j+1))`, `[g k, g (k+1))` are disjoint by
the strict cyclic order; the wrap wedge `wedge (g n) (g 1)` is disjoint from
every interval wedge because its `azim` range is the complement arc. -/
private theorem p22_wedge_disjoint_aux (x y z : V3) (n : ℕ) (g : ℕ → V3)
    (h1 : ¬ Collinear3 x y z)
    (h2 : ∀ i : ℕ, i ∈ Finset.Icc 1 n → ¬ Collinear3 x y (g i))
    (h3 : g (n + 1) = g 1)
    (h4 : ∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j < k →
      azim x y z (g j) < azim x y z (g k))
    {j k : ℕ} (hjk : j < k) (hjn : j ∈ Finset.Icc 1 n) (hkn : k ∈ Finset.Icc 1 n) :
    (wedge x y (g j) (g (j + 1)) ∩ wedge x y (g k) (g (k + 1))) = ∅ := by
  have hxy : y ≠ x := p22_y_ne_x h1
  have hn1 : 1 ≤ n := by
    have hk := Finset.mem_Icc.mp hkn
    omega
  have hjn' := Finset.mem_Icc.mp hjn
  have hkn' := Finset.mem_Icc.mp hkn
  have h1I : (1 : ℕ) ∈ Finset.Icc 1 n := by
    refine Finset.mem_Icc.mpr ?_
    omega
  have hnI : n ∈ Finset.Icc 1 n := by
    refine Finset.mem_Icc.mpr ?_
    omega
  have hmem_j1 : (j + 1 : ℕ) ∈ Finset.Icc 1 n := by
    refine Finset.mem_Icc.mpr ?_
    omega
  have hgj1 : ¬ Collinear3 x y (g (j + 1)) := h2 (j + 1) hmem_j1
  have hgk1 : ¬ Collinear3 x y (g (k + 1)) := by
    rcases Nat.lt_or_ge k n with hk | hk
    · have hmem : (k + 1 : ℕ) ∈ Finset.Icc 1 n := by
        refine Finset.mem_Icc.mpr ?_
        omega
      exact h2 (k + 1) hmem
    · have hkeq : k = n := by omega
      rw [hkeq, h3]
      exact h2 1 h1I
  have hordj : azim x y z (g j) ≤ azim x y z (g (j + 1)) :=
    le_of_lt (h4 j (j + 1) hjn hmem_j1 (by omega))
  have hA1j : azim x y z (g 1) ≤ azim x y z (g j) := by
    rcases lt_trichotomy 1 j with h | h | h
    · exact le_of_lt (h4 1 j h1I hjn h)
    · rw [h]
    · omega
  have hAn : azim x y z (g 1) < azim x y z (g n) := h4 1 n h1I hnI (by omega)
  have hstepAn : azim x y z (g n) = azim x y z (g 1) + azim x y (g 1) (g n) :=
    sum4_azim_fan hxy h1 (h2 1 h1I) (h2 n hnI) hAn.le
  have hgn : azim x y (g 1) (g n) ≠ 0 := by
    have hnn := azim_nonneg x y (g 1) (g n)
    intro h0; rw [h0] at hstepAn; linarith
  have hcomp1 : azim x y (g n) (g 1)
      = 2 * Real.pi - (azim x y z (g n) - azim x y z (g 1)) := by
    have h := azim_compl (h2 1 h1I) (h2 n hnI)
    rw [if_neg hgn] at h
    linarith
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hpnc1 : ¬ Collinear3 x y p := hp1.1
  rcases Nat.lt_or_ge k n with hklt | hkeq
  · -- both wedges are interval wedges: the order intervals are disjoint
    have hmem_k1 : (k + 1 : ℕ) ∈ Finset.Icc 1 n := by
      refine Finset.mem_Icc.mpr ?_
      omega
    have hordk : azim x y z (g k) ≤ azim x y z (g (k + 1)) :=
      le_of_lt (h4 k (k + 1) hkn hmem_k1 (by omega))
    have hb1 := p22_wedge_bounds hxy h1 hpnc1 (h2 j hjn) hgj1 hp1 hordj
    have hb2 := p22_wedge_bounds hxy h1 hpnc1 (h2 k hkn) hgk1 hp2 hordk
    obtain ⟨hb11, hb12⟩ := hb1
    obtain ⟨hb21, hb22⟩ := hb2
    have hmid : azim x y z (g (j + 1)) ≤ azim x y z (g k) := by
      rcases lt_trichotomy (j + 1) k with hlt' | heq' | hgt'
      · exact le_of_lt (h4 (j + 1) k hmem_j1 hkn hlt')
      · rw [heq']
      · exact absurd hgt' (by omega)
    exfalso
    linarith
  · -- wrap case k = n: the wrap wedge is the complementary arc
    have hkeq : k = n := by omega
    rw [hkeq, h3] at hp2
    rw [wedge, Set.mem_setOf_eq] at hp2
    obtain ⟨-, hlow2, hhigh2⟩ := hp2
    have hb1 := p22_wedge_bounds hxy h1 hpnc1 (h2 j hjn) hgj1 hp1 hordj
    obtain ⟨hb11, hb12⟩ := hb1
    have hmid : azim x y z (g (j + 1)) ≤ azim x y z (g n) := by
      rcases lt_trichotomy (j + 1) n with h | h | h
      · exact le_of_lt (h4 (j + 1) n hmem_j1 hnI h)
      · rw [h]
      · exact absurd h (by omega)
    rcases lt_trichotomy (azim x y z (g n)) (azim x y z p) with hcase | hcase | hcase
    · exfalso
      linarith
    · have hstepP : azim x y z (g n) = azim x y z p + azim x y p (g n) :=
        sum4_azim_fan hxy h1 hpnc1 (h2 n hnI) (le_of_eq hcase.symm)
      have hcomp2 : azim x y (g n) p = 0 := by
        have h := azim_compl hpnc1 (h2 n hnI)
        rw [if_pos (by linarith : azim x y p (g n) = 0)] at h
        exact h
      exfalso
      linarith
    · have hstepP : azim x y z (g n) = azim x y z p + azim x y p (g n) :=
        sum4_azim_fan hxy h1 hpnc1 (h2 n hnI) (le_of_lt hcase)
      have hzpos : 0 < azim x y p (g n) := by linarith
      have hcomp2 : azim x y (g n) p = 2 * Real.pi - azim x y p (g n) := by
        have h := azim_compl hpnc1 (h2 n hnI)
        rwa [if_neg (ne_of_gt hzpos)] at h
      exfalso
      linarith

/-- HOL `WEDGE_ORDER_DISJOINT` (counting_spheres.hl:2535). GIANT. -/
theorem WEDGE_ORDER_DISJOINT (x y z : V3) (n : ℕ) (g : ℕ → V3)
    (h1 : ¬ Collinear3 x y z)
    (h2 : ∀ i : ℕ, i ∈ Finset.Icc 1 n → ¬ Collinear3 x y (g i))
    (h3 : g (n + 1) = g 1)
    (h4 : ∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j < k →
      azim x y z (g j) < azim x y z (g k)) :
    ∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j ≠ k →
      (wedge x y (g j) (g (j + 1)) ∩ wedge x y (g k) (g (k + 1))) = ∅ := by
  intro j k hj hk hjk
  rcases lt_trichotomy j k with hlt | heq | hgt
  · exact p22_wedge_disjoint_aux x y z n g h1 h2 h3 h4 hlt hj hk
  · exact absurd heq hjk
  · rw [Set.inter_comm]
    exact p22_wedge_disjoint_aux x y z n g h1 h2 h3 h4 hgt hk hj

/-- HOL `ORDER_AZIM_SUM2Pi` (counting_spheres.hl:2633). GIANT. -/
theorem ORDER_AZIM_SUM2Pi (x y z : V3) (n : ℕ) (g : ℕ → V3)
    (h1 : ¬ Collinear3 x y z)
    (h2 : ∀ i : ℕ, i ∈ Finset.Icc 1 n → ¬ Collinear3 x y (g i))
    (h3 : g (n + 1) = g 1) (hn : 1 < n)
    (h4 : ∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n → j < k →
      azim x y z (g j) < azim x y z (g k)) :
    ∑ i ∈ Finset.Icc 1 n, azim x y (g i) (g (i + 1)) = 2 * Real.pi := by
  have hxy : y ≠ x := p22_y_ne_x h1
  have hn1 : 1 ≤ n := le_of_lt hn
  have h1I : (1 : ℕ) ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; omega
  have hnI : n ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; omega
  have hAn : azim x y z (g 1) < azim x y z (g n) := h4 1 n h1I hnI (by omega)
  have hstepAn : azim x y z (g n) = azim x y z (g 1) + azim x y (g 1) (g n) :=
    sum4_azim_fan hxy h1 (h2 1 h1I) (h2 n hnI) hAn.le
  have hgn : azim x y (g 1) (g n) ≠ 0 := by
    have hnn := azim_nonneg x y (g 1) (g n)
    intro h0; rw [h0] at hstepAn; linarith
  -- each cyclic step is the azim-decrement, plus a 2π correction at the wrap
  have hterm : ∀ i : ℕ, i ∈ Finset.Icc 1 n →
      azim x y (g i) (g (i + 1))
        = (azim x y z (g (i + 1)) - azim x y z (g i))
          + (if i = n then (2 * Real.pi) else (0 : ℝ)) := by
    intro i hi
    rcases Nat.lt_or_ge i n with hlt | heq
    · have hi' : (i + 1 : ℕ) ∈ Finset.Icc 1 n := by
        have hi2 := Finset.mem_Icc.mp hi
        refine Finset.mem_Icc.mpr ?_
        omega
      have hsum := sum4_azim_fan hxy h1 (h2 i hi) (h2 (i + 1) hi')
        (le_of_lt (h4 i (i + 1) hi hi' (by omega)))
      rw [if_neg (by omega : ¬ (i = n))]
      linarith
    · have hin : i = n := by
        have hi2 := Finset.mem_Icc.mp hi
        omega
      rw [hin, if_pos rfl, h3]
      have hcomp := azim_compl (h2 1 h1I) (h2 n hnI)
      rw [if_neg hgn] at hcomp
      linarith
  have hcorr : ∑ i ∈ Finset.Icc 1 n,
      (if i = n then (2 * Real.pi) else (0 : ℝ)) = 2 * Real.pi := by
    rw [Finset.sum_eq_single n]
    · simp
    · intro i _ hi
      rw [if_neg hi]
    · intro hcontra
      exact absurd (Finset.mem_Icc.mpr ⟨le_of_lt hn, le_refl n⟩) hcontra
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have htele : ∑ i ∈ Finset.Icc 1 n, (azim x y z (g (i + 1)) - azim x y z (g i))
      = azim x y z (g (n + 1)) - azim x y z (g 1) :=
    p22_telescope (fun i => azim x y z (g i)) n hn1
  rw [htele, h3, sub_self, hcorr]
  ring

/-- HOL `AFFINE_VEC0` (counting_spheres.hl:2680). Filled: `0` is the affine
combination `u + (1/(1-t)) • (t•u - u)`. -/
theorem AFFINE_VEC0 (u : V3) (t : ℝ) (ht : t ≠ 1) :
    (0 : V3) ∈ affineSpan ℝ ({u, t • u} : Set V3) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨1 / (1 - t), ?_⟩
  have h1 : t • u -ᵥ u = (t - 1) • u := by
    show t • u - u = (t - 1) • u
    rw [sub_smul, one_smul]
  have h2 : 1 / (1 - t) * (t - 1) = -1 := by
    field_simp
    ring
  rw [AffineMap.lineMap_apply, h1, smul_smul, h2]
  show (-1 : ℝ) • u + u = 0
  simp

/-- HOL `RELATIVE_INTERIOR_AFFINE_FACE` (counting_spheres.hl:2702). GIANT. -/
theorem RELATIVE_INTERIOR_AFFINE_FACE (C : Set V3) (p : V3) (f : Set V3)
    (hc : Convex ℝ C) (hf : FaceOf f C) (hap : p ∈ (affineSpan ℝ f : Set V3))
    (hip : p ∈ intrinsicInterior ℝ C) : f = C := by
  -- Filled per docs/statement-fix-proposals.md item 7: `f = ∅` makes `hap`
  -- unsatisfiable (`affineSpan ℝ ∅ = ⊥` has empty carrier); otherwise the
  -- argument of `p22_face_of_affine_rint` (defined below in this file, hence
  -- inlined here) closes the goal.
  have hfne : f.Nonempty := by
    by_contra h0
    rw [Set.not_nonempty_iff_eq_empty.mp h0, AffineSubspace.span_empty,
      AffineSubspace.bot_coe] at hap
    exact hap
  by_contra hne2
  have hdisj := faceOf_disjoint_rinterior hf hne2
  have hsub := faceOf_eq_affineInter hc hf
  exact (Set.disjoint_left.mp hdisj (hsub ⟨hap, (mem_rint_iff.mp hip).1⟩)) hip

/-- HOL `SUBSET_P_HULL` (counting_spheres.hl:2720). -/
theorem SUBSET_P_HULL (P S : Set V3) : S ⊆ hullP22 P S := by
  show S ⊆ convexHull ℝ (P ∪ S)
  exact subset_trans (Set.subset_union_right) (subset_convexHull ℝ (P ∪ S))

/-- A face containing a point `q` of `affineSpan f ∩ relativeInterior C` in its
affine hull equals `C` (nonempty-face form of the HOL
`RELATIVE_INTERIOR_AFFINE_FACE`; the empty-face form is false as stated). -/
private theorem p22_face_of_affine_rint {C f : Set V3} {q : V3}
    (hface : FaceOf f C) (hne : f.Nonempty) (hc : Convex ℝ C)
    (hq1 : q ∈ (affineSpan ℝ f : Set V3)) (hq2 : q ∈ intrinsicInterior ℝ C) : f = C := by
  by_contra hne2
  have hdisj := faceOf_disjoint_rinterior hface hne2
  have hsub := faceOf_eq_affineInter hc hface
  exact (Set.disjoint_left.mp hdisj (hsub ⟨hq1, (mem_rint_iff.mp hq2).1⟩)) hq2

/-- HOL `FCHANGED_AFFINE` (counting_spheres.hl:2724).  Filled: the ⊇ half is
`t = 1` of the cone definition; the ⊆ half forces `t = 1` because `f` is a
facet while `0` lies in the interior of `p` (any `t ≠ 1` scaling of a relative
interior point of `f` puts `0` in `affineSpan f`, hence `f = p` by the face
lemma, contradicting `FacetOf`). -/
theorem FCHANGED_AFFINE (p f : Set V3) (hp : polyhedron p) (hb : Bornology.IsBounded p)
    (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    fchanged f ∩ (affineSpan ℝ f : Set V3) = intrinsicInterior ℝ f := by
  have h0rp : (0:V3) ∈ intrinsicInterior ℝ p := by
    rw [mem_rint_iff]
    obtain ⟨t0, ht0sub, ht0open, ht0mem⟩ := mem_interior.mp hi
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ht0open 0 ht0mem
    exact ⟨interior_subset hi, ε, hε, fun y hy => ht0sub (hball hy.1)⟩
  have hfpne : f ≠ p := by
    intro hcon
    have hdim := hf.2.2
    rw [hcon] at hdim
    omega
  refine Set.ext fun x => ?_
  constructor
  · rintro ⟨⟨v1, t1, hv1eq, hv1ri, ht1pos⟩, hxaff⟩
    by_cases hxt : x = v1
    · rwa [hxt]
    · have ht1ne : t1 ≠ 1 := by
        intro hcon
        rw [hcon, one_smul] at hv1eq
        exact hxt hv1eq
      have h0aff : (0:V3) ∈ (affineSpan ℝ f : Set V3) := by
        have h1 := AFFINE_VEC0 v1 t1 ht1ne
        have hsub : ((affineSpan ℝ ({v1, t1 • v1} : Set V3) : AffineSubspace ℝ V3) ≤
            affineSpan ℝ f) := by
          rw [affineSpan_le]
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with hz | hz
          · rw [hz]
            exact subset_affineSpan ℝ f (mem_rint_iff.mp hv1ri).1
          · rw [hz, ← hv1eq]
            exact hxaff
        exact hsub h1
      have hfp : f = p :=
        p22_face_of_affine_rint hf.1 (nonempty_iff_ne_empty.mpr hf.2.1)
          (POLYHEDRON_IMP_CONVEX hp) h0aff h0rp
      exact absurd hfp hfpne
  · intro hx
    have hx' : x = (1:ℝ) • x := (one_smul ℝ x).symm
    have hf' : x ∈ fchanged f := ⟨x, (1:ℝ), hx', hx, one_pos⟩
    exact ⟨hf', subset_affineSpan ℝ f (mem_rint_iff.mp hx).1⟩

/-- HOL `RCONE_PREP` (counting_spheres.hl:2765). Filled: direct inner-product
algebra with the `dotV_*` helpers (all ofLp bookkeeping is confined to those
lemmas). -/
theorem RCONE_PREP (p v u0 : V3) (b t : ℝ) (hb : 0 < b) (hv : v ≠ 0)
    (hvv : 0 < v ⬝ᵥ v) (hu0 : u0 = (b / (v ⬝ᵥ v)) • v) (ht1 : 0 < t) (ht2 : t < 1)
    (hpv : p ⬝ᵥ v = b) :
    u0 ⬝ᵥ u0 = b * b / (v ⬝ᵥ v) ∧
      p ⬝ᵥ u0 = b * b / (v ⬝ᵥ v) ∧
      dist p u0 ^ 2 = p ⬝ᵥ p - b * b / (v ⬝ᵥ v) := by
  have hvne : v ⬝ᵥ v ≠ 0 := ne_of_gt hvv
  have hu0u0 : u0 ⬝ᵥ u0 = b * b / (v ⬝ᵥ v) := by
    rw [hu0, dotV_smul_left, WithLp.ofLp_smul, dotV_smul_right]
    field_simp
  have hpu0 : p ⬝ᵥ u0 = b * b / (v ⬝ᵥ v) := by
    rw [hu0, WithLp.ofLp_smul, dotV_smul_right, hpv]
    field_simp
  refine ⟨hu0u0, hpu0, ?_⟩
  have hdn : dist p u0 ^ 2 = ((p - u0 : V3).ofLp) ⬝ᵥ ((p - u0 : V3).ofLp) := by
    rw [dist_eq_norm, norm_sq_eq_dot]
  rw [hdn, dotV_sub_left, WithLp.ofLp_sub, dotV_sub_right, dotV_sub_right,
    dotV_comm u0 p, hpu0, hu0u0]
  ring

/-- Membership in `rconeGt 0 v t`, rewritten (local copy of `rcone_def_alt`,
which is proved later in this chapter). -/
theorem rconeGt_zero_mem (v : V3) (t : ℝ) (p : V3) :
    p ∈ rconeGt 0 v t ↔ ‖p‖ * ‖v‖ * t < p ⬝ᵥ v := by
  simp [rconeGt, dist_zero_right, sub_zero]

/-- HOL `RCONE_DISK` (counting_spheres.hl:2802). Filled: the disk `dist p u0 < r`
in the facet plane lands inside the cone `‖p‖·‖v‖·t < p·v`. -/
theorem RCONE_DISK (p v u0 : V3) (b r t : ℝ) (hb : 0 < b) (hv : v ≠ 0)
    (hvv : 0 < v ⬝ᵥ v) (hd : dist p u0 < r)
    (hu0 : u0 = (b / (v ⬝ᵥ v)) • v) (ht1 : 0 < t) (ht2 : t < 1)
    (hpv : p ⬝ᵥ v = b)
    (hr : r = b * Real.sqrt (1 - t ^ 2) / (t * ‖v‖)) :
    p ∈ rconeGt 0 v t := by
  have hvv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hsqlt : 0 < 1 - t ^ 2 := sub_pos.mpr (by nlinarith [sq_pos_of_pos ht1, ht2])
  have hrpos : 0 < r := by
    rw [hr]
    exact div_pos (mul_pos hb (Real.sqrt_pos.mpr hsqlt)) (mul_pos ht1 hvv')
  have hprep := RCONE_PREP p v u0 b t hb hv hvv hu0 ht1 ht2 hpv
  rw [rconeGt_zero_mem, hpv]
  have hr2 : r ^ 2 = b ^ 2 / (v ⬝ᵥ v) * (1 - t ^ 2) / t ^ 2 := by
    rw [hr, ← norm_sq_eq_dot v, div_pow, mul_pow, mul_pow,
      Real.sq_sqrt (le_of_lt hsqlt)]
    field_simp [ne_of_gt hvv]
  have hsq : (dist p u0) ^ 2 < r ^ 2 := by
    have hneg : -r < dist p u0 := by
      calc -r < 0 := by linarith
        _ ≤ dist p u0 := dist_nonneg
    exact sq_lt_sq' hneg hd
  have h1 : ‖p‖ ^ 2 < b ^ 2 / (v ⬝ᵥ v) / t ^ 2 := by
    have h2 := hprep.2.2
    rw [dist_eq_norm, norm_sq_eq_dot] at h2
    rw [dist_eq_norm, norm_sq_eq_dot] at hsq
    rw [hr2] at hsq
    have hZY : b ^ 2 / (v ⬝ᵥ v) * (1 - t ^ 2) / t ^ 2 + b * b / (v ⬝ᵥ v)
        = b ^ 2 / (v ⬝ᵥ v) / t ^ 2 := by
      field_simp [ne_of_gt hvv]
      ring
    rw [norm_sq_eq_dot]
    linarith
  have hgoal : (‖p‖ * ‖v‖ * t) ^ 2 < b ^ 2 := by
    rw [mul_pow, mul_pow]
    have h4 := mul_lt_mul_of_pos_right h1 (mul_pos (sq_pos_of_pos hvv') (sq_pos_of_pos ht1))
    have h5 : b ^ 2 / (v ⬝ᵥ v) / t ^ 2 * (‖v‖ ^ 2 * t ^ 2) = b ^ 2 := by
      rw [← norm_sq_eq_dot v]
      field_simp [ne_of_gt hvv']
    rw [h5] at h4
    calc ‖p‖ ^ 2 * ‖v‖ ^ 2 * t ^ 2
        = ‖p‖ ^ 2 * (‖v‖ ^ 2 * t ^ 2) := by ring
      _ < b ^ 2 := h4
  have hfin : ‖p‖ * ‖v‖ * t < b := by
    have hab := (sq_lt_sq).mp hgoal
    rwa [abs_of_nonneg (show 0 ≤ ‖p‖ * ‖v‖ * t from by positivity), abs_of_pos hb] at hab
  exact hfin

/-- HOL `RDISK_R` (counting_spheres.hl:2859). Filled: the radius
`b·√(1-t²)/(t·‖v‖)` works; on the boundary circle `‖w‖ = c/t` gives
`cos (arcV 0 u0 w) = t` by direct inner-product algebra. -/
theorem RDISK_R (v u0 : V3) (b t : ℝ) (hb : 0 < b) (hv : v ≠ 0) (hvv : 0 < v ⬝ᵥ v)
    (ht1 : 0 < t) (ht2 : t < 1) (hu0 : u0 = (b / (v ⬝ᵥ v)) • v) :
    ∃ r : ℝ, 0 < r ∧
      (∀ p : V3, dist p u0 < r → p ⬝ᵥ v = b → p ∈ rconeGt 0 v t) ∧
      (∀ w : V3, dist w u0 = r → w ⬝ᵥ v = b → Real.cos (arcV 0 u0 w) = t) := by
  have hvv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hsqlt : 0 < 1 - t ^ 2 := sub_pos.mpr (by nlinarith [sq_pos_of_pos ht1, ht2])
  refine ⟨b * Real.sqrt (1 - t ^ 2) / (t * ‖v‖),
    div_pos (mul_pos hb (Real.sqrt_pos.mpr hsqlt)) (mul_pos ht1 hvv'), ?_, ?_⟩
  · exact fun p hp hpb => RCONE_DISK p v u0 b _ t hb hv hvv hp hu0 ht1 ht2 hpb rfl
  · intro w hw hwb
    have hprep := RCONE_PREP w v u0 b t hb hv hvv hu0 ht1 ht2 hwb
    have hu00 : u0 ⬝ᵥ u0 = b * b / (v ⬝ᵥ v) := hprep.1
    have hwu0 : w ⬝ᵥ u0 = b * b / (v ⬝ᵥ v) := hprep.2.1
    have hu0n : ‖u0‖ = b / ‖v‖ := by
      have h2 : ‖u0‖ ^ 2 = (b / ‖v‖) ^ 2 := by
        rw [norm_sq_eq_dot, hu00, ← norm_sq_eq_dot v]
        field_simp [ne_of_gt hvv]
      have hpos : 0 ≤ b / ‖v‖ := by positivity
      calc ‖u0‖ = Real.sqrt (‖u0‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u0)).symm
        _ = Real.sqrt ((b / ‖v‖) ^ 2) := by rw [h2]
        _ = b / ‖v‖ := Real.sqrt_sq hpos
    have hwn0 : ‖w - u0‖ = b * Real.sqrt (1 - t ^ 2) / (t * ‖v‖) := by
      rw [← dist_eq_norm]; exact hw
    have hr2 : (b * Real.sqrt (1 - t ^ 2) / (t * ‖v‖)) ^ 2
        = b ^ 2 / (v ⬝ᵥ v) * (1 - t ^ 2) / t ^ 2 := by
      rw [← norm_sq_eq_dot v, div_pow, mul_pow, mul_pow,
        Real.sq_sqrt (le_of_lt hsqlt)]
      field_simp [ne_of_gt hvv]
    have hwn : ‖w‖ = b / ‖v‖ / t := by
      have h1 : ‖w‖ ^ 2 = (b / ‖v‖ / t) ^ 2 := by
        have hexp : ‖w‖ ^ 2
            = ‖w - u0‖ ^ 2 + 2 * (b * b / (v ⬝ᵥ v)) - ‖u0‖ ^ 2 := by
          have hsplit : w = (w - u0) + u0 := by abel
          rw [norm_sq_eq_dot, norm_sq_eq_dot, norm_sq_eq_dot]
          conv_lhs => rw [hsplit]
          simp only [WithLp.ofLp_add, dotProduct_add, add_dotProduct,
            WithLp.ofLp_sub, dotProduct_sub, sub_dotProduct,
            dotProduct_smul, smul_dotProduct, dotProduct_comm]
          have hwu0' : u0.ofLp ⬝ᵥ w.ofLp = b * b / (v ⬝ᵥ v) := by
            rw [dotProduct_comm]; exact hwu0
          rw [hwu0', hu00]
          ring
        rw [hexp, hwn0, hr2, norm_sq_eq_dot u0, hu00, ← norm_sq_eq_dot v]
        field_simp [Real.sq_sqrt (le_of_lt hsqlt), ne_of_gt hvv']
        ring
      have hpos : 0 ≤ b / ‖v‖ / t := by positivity
      calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
        _ = Real.sqrt ((b / ‖v‖ / t) ^ 2) := by rw [h1]
        _ = b / ‖v‖ / t := Real.sqrt_sq hpos
    -- cos (arcV 0 u0 w) = t
    have hzs : (w - (0:V3)) ⬝ᵥ u0 = w ⬝ᵥ u0 := by
      rw [dotV_sub_left, coeV_zero, zero_dotProduct, sub_zero]
    have hz : ((u0 - (0:V3)) ⬝ᵥ (w - (0:V3))) / (dist u0 (0:V3) * dist w (0:V3)) = t := by
      rw [WithLp.ofLp_sub, sub_dotProduct, dotProduct_sub, coeV_zero,
        zero_dotProduct, dotProduct_zero, sub_zero, sub_zero,
        dotProduct_comm, hwu0,
        show dist u0 (0:V3) = ‖u0‖ from by rw [dist_eq_norm]; simp,
        show dist w (0:V3) = ‖w‖ from by rw [dist_eq_norm]; simp, hu0n, hwn,
        ← norm_sq_eq_dot v]
      field_simp [ne_of_gt hvv']
    rw [arcV, Real.cos_arccos (by rw [hz]; linarith) (by rw [hz]; linarith), hz]

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

/-- HOL `FCHANGED_RADIAL` (counting_spheres.hl:2986).  Filled directly from
the definitions: `fchanged f` is a positive cone over the relative interior
(scale-invariant), so its intersection with the centered ball is radial. -/
theorem FCHANGED_RADIAL (p f : Set V3) (r : ℝ) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p) :
    radialNorm r 0 (fchanged f ∩ normballP22 0 r) := by
  refine ⟨fun x hx => hx.2, ?_⟩
  intro u hu t ht htr
  obtain ⟨v1, t1, hv1, hv1ri, ht1⟩ := hu.1
  refine ⟨?_, ?_⟩
  · refine ⟨v1, t1 * t, ?_, hv1ri, by positivity⟩
    rw [← smul_smul, smul_comm t1 t v1, ← hv1]
    simp only [zero_add]
  · simp only [normballP22, Metric.mem_ball, dist_zero_right, zero_add, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    exact htr

/-- HOL `WEDGE_SPLIT` (counting_spheres.hl:3025). GIANT. -/
theorem WEDGE_SPLIT (u0 u1 u2 u3 w : V3) (h1 : ¬ Collinear3 u0 u1 u2)
    (h2 : ¬ Collinear3 u0 u1 u3) (hw : w ∈ wedge u0 u1 u2 u3) :
    ¬ Collinear3 u0 u1 w ∧
      wedge u0 u1 u2 w ∩ wedge u0 u1 w u3 = ∅ ∧
      wedge u0 u1 u2 w ⊆ wedge u0 u1 u2 u3 ∧
      wedge u0 u1 w u3 ⊆ wedge u0 u1 u2 u3 := by
  rw [wedge, Set.mem_setOf_eq] at hw
  obtain ⟨hw3, hw0, hwlt⟩ := hw
  have hxy : u1 ≠ u0 := p22_y_ne_x h1
  refine ⟨hw3, ?_, ?_, ?_⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    have ex1 : y ∈ wedge u0 u1 u2 w := hy.1
    have ex2 : y ∈ wedge u0 u1 w u3 := hy.2
    rw [wedge, Set.mem_setOf_eq] at ex1 ex2
    obtain ⟨hync, hy1, hy2⟩ := ex1
    obtain ⟨-, hy3, hy4⟩ := ex2
    have hge : azim u0 u1 u2 y ≤ azim u0 u1 u2 w := le_of_lt hy2
    have e1 : azim u0 u1 u2 w = azim u0 u1 u2 y + azim u0 u1 y w :=
      sum4_azim_fan hxy h1 hync hw3 hge
    have e2 : azim u0 u1 u2 u3 = azim u0 u1 u2 w + azim u0 u1 w u3 :=
      sum4_azim_fan hxy h1 hw3 h2 hwlt.le
    have hywp : 0 < azim u0 u1 y w := by linarith
    have hyw0 : azim u0 u1 y w ≠ 0 := ne_of_gt hywp
    have hcomp : azim u0 u1 w y = 2 * Real.pi - azim u0 u1 y w := by
      have h := azim_compl hync hw3
      rwa [if_neg hyw0] at h
    have hlt := azim_lt_two_pi u0 u1 u2 u3
    linarith
  · intro y hy
    rw [wedge, Set.mem_setOf_eq] at hy ⊢
    obtain ⟨hync, hy1, hy2⟩ := hy
    exact ⟨hync, hy1, lt_trans hy2 hwlt⟩
  · intro y hy
    rw [wedge, Set.mem_setOf_eq] at hy ⊢
    obtain ⟨hync, hy1, hy2⟩ := hy
    have hyw0 : azim u0 u1 y w ≠ 0 := by
      intro h0
      exact absurd (azim_compl_eq_zero hync hw3 h0) (ne_of_gt hy1)
    rcases le_total (azim u0 u1 u2 w) (azim u0 u1 u2 y) with hc | hc
    · have e1 : azim u0 u1 u2 y = azim u0 u1 u2 w + azim u0 u1 w y :=
        sum4_azim_fan hxy h1 hw3 hync hc
      have e2 : azim u0 u1 u2 u3 = azim u0 u1 u2 w + azim u0 u1 w u3 :=
        sum4_azim_fan hxy h1 hw3 h2 hwlt.le
      exact ⟨hync, by linarith, by linarith⟩
    · -- `y` before `w` while `azim w y > 0` is impossible on one revolution
      exfalso
      have e1 : azim u0 u1 u2 w = azim u0 u1 u2 y + azim u0 u1 y w :=
        sum4_azim_fan hxy h1 hync hw3 hc
      have hywp : 0 < azim u0 u1 y w := lt_of_le_of_ne' (azim_nonneg u0 u1 y w) hyw0
      have hcomp : azim u0 u1 w y = 2 * Real.pi - azim u0 u1 y w := by
        have h := azim_compl hync hw3
        rwa [if_neg hyw0] at h
      have e2 : azim u0 u1 u2 u3 = azim u0 u1 u2 w + azim u0 u1 w u3 :=
        sum4_azim_fan hxy h1 hw3 h2 hwlt.le
      have hlt := azim_lt_two_pi u0 u1 u2 u3
      have hnn := azim_nonneg u0 u1 u2 y
      linarith

/-- Coefficient-witness transfer between `Affsign` instances with the same
union `s ∪ t = s' ∪ t'` and shrinking sign side `t' ⊆ t` (planar CONE0 kit;
HOL `affsign` def-expansion, counting_spheres.hl:3058 proof core). -/
private theorem p22_affsign_transfer {sgn : ℝ → Prop} {s s' t t' : Set V3} {v : V3}
    (hu : s ∪ t = s' ∪ t') (ht : t' ⊆ t)
    (h : Affsign sgn s t v) : Affsign sgn s' t' v := by
  obtain ⟨f, hK, hvsum, hsign, hone⟩ := h
  have hK' : (s' ∪ t').Finite := by rw [← hu]; exact hK
  have hTeq : hK'.toFinset = hK.toFinset := by
    ext w
    simp only [Set.Finite.mem_toFinset, ← hu]
  refine ⟨f, hK', ?_, fun w hw => hsign w (ht hw), ?_⟩
  · rw [hTeq]; exact hvsum
  · rw [hTeq]; exact hone

/-- HOL `cone0_subset_lune` (counting_spheres.hl:3058). GIANT. -/
theorem cone0_subset_lune (u0 u1 u2 u3 : V3) :
    cone0P22 u0 {u1, u2, u3} ⊆ affGt {u0, u1} {u2, u3} := by
  -- Both `Affsign` instances range over the same point set `{u0,u1,u2,u3}`;
  -- the coefficient function transfers verbatim and the strict sign condition
  -- is only restricted to the smaller set `{u2,u3}` (strict → strict).
  intro v hv
  have hv' : Affsign (fun x : ℝ => 0 < x) ({u0} : Set V3) ({u1, u2, u3} : Set V3) v := hv
  have hu : ({u0} : Set V3) ∪ {u1, u2, u3} = ({u0, u1} : Set V3) ∪ {u2, u3} := by
    ext w
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  have ht : ({u2, u3} : Set V3) ⊆ ({u1, u2, u3} : Set V3) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
    tauto
  exact p22_affsign_transfer hu ht hv'

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
    affGt (∅ : Set V3) s ⊆ intrinsicInterior ℝ (convexHull ℝ s) := by
  -- Filled (kit wave): basis of `D := vectorSpan ℝ s` extracted inside the
  -- difference family `(w₀ -ᵥ ·) '' s` (`exists_linearIndependent` + `Basis.mk`),
  -- coordinates bounded via `Basis.coord` + `ContinuousLinearMap.le_opNorm`,
  -- zero-sum representation `z - y = ∑ g w • w`, coefficients `f w + g w ≥ 0`
  -- for `‖z - y‖ < f wδ / (2 * (Csum + 1))`, assembled by
  -- `Finset.centerMass_mem_convexHull` + `mem_rint_iff`.

  -- Coefficient family of the aff_gt witness.
  rintro y ⟨f, hfinU, hy, hpos, hone⟩
  set T := hfinU.toFinset with hTdef
  have hTsub : ∀ w ∈ T, w ∈ s := by
    intro w hw
    have hw2 : w ∈ ((∅ : Set V3) ∪ s) := (Set.Finite.mem_toFinset hfinU).mp hw
    simpa using hw2
  have hsT : ∀ w ∈ s, w ∈ T := by
    intro w hw
    exact (Set.Finite.mem_toFinset hfinU).mpr (by simpa using hw)
  have hfT : ∀ w ∈ T, 0 < f w := fun w hw => hpos w (hTsub w hw)
  have hTne : T.Nonempty := by
    by_contra hc
    have hce : T = ∅ := not_not.mp ((Finset.nonempty_iff_ne_empty.not).mp hc)
    rw [hce] at hone
    simp at hone
  obtain ⟨w₀, hw₀T⟩ := id hTne
  have hw₀s : w₀ ∈ s := hTsub w₀ hw₀T
  -- y ∈ hull via strict center of mass.
  have hymm : T.centerMass f id = ∑ w ∈ T, f w • w := by
    simp [Finset.centerMass, hone]
  have hymem : y ∈ convexHull ℝ s := by
    rw [hy, ← hymm]
    refine Finset.centerMass_mem_convexHull _ (fun w hw => le_of_lt (hfT w hw)) ?_
      (fun w hw => hTsub w hw)
    rw [hone]; norm_num
  -- Basis of the direction inside the difference family.
  have hmemfam : ∀ x ∈ s, (w₀ -ᵥ x : V3) ∈ vectorSpan ℝ s := by
    intro x hx
    rw [vectorSpan_eq_span_vsub_set_left ℝ hw₀s]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  set D := vectorSpan ℝ s with hDdef
  haveI : Finite ↥s := hf
  set fam : Set D := (fun (u : {x // x ∈ s}) =>
    (⟨w₀ -ᵥ (u : V3), hmemfam _ u.2⟩ : D)) '' Set.univ with hfamdef
  have hfamfin : fam.Finite := by
    rw [hfamdef]
    exact Set.finite_univ.image _
  have hfamspan : Submodule.span ℝ ((fun x => w₀ -ᵥ x) '' s) = D := by
    rw [hDdef, vectorSpan_eq_span_vsub_set_left ℝ hw₀s]
  have h'im : (fun (u : {x // x ∈ s}) => (w₀ -ᵥ (u : V3) : V3)) '' (Set.univ : Set ↥s)
      = (fun x => w₀ -ᵥ x) '' s := by
    ext z
    simp only [Set.mem_image, Set.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨(u : V3), u.2, hu⟩
    · rintro ⟨x, hx, hx2⟩
      exact ⟨⟨x, hx⟩, hx2⟩
  have hfamD : (Submodule.span ℝ fam).map (Submodule.subtype D) = D := by
    rw [Submodule.map_span, hfamdef, ← Set.image_comp]
    have hcomp : (Submodule.subtype D ∘ fun (u : {x // x ∈ s}) =>
        (⟨w₀ -ᵥ (u : V3), hmemfam _ u.2⟩ : D))
        = fun (u : {x // x ∈ s}) => (w₀ -ᵥ (u : V3) : V3) := by
      funext u
      rfl
    rw [hcomp, h'im, hfamspan]
  have hinj : Function.Injective (Submodule.subtype D : D → V3) := fun a b hab => Subtype.ext hab
  have hfamtop : Submodule.span ℝ fam = ⊤ := by
    have h2 : (Submodule.span ℝ fam).map (Submodule.subtype D)
        = (⊤ : Submodule ℝ D).map (Submodule.subtype D) := by
      rw [Submodule.map_top, Submodule.range_subtype]
      exact hfamD
    exact Submodule.map_injective_of_injective hinj h2
  obtain ⟨b, hbsub, hbsp, hbli⟩ := exists_linearIndependent ℝ fam
  rw [hfamtop] at hbsp
  have hbfin : b.Finite := hfamfin.subset hbsub
  haveI : Fintype ↥b := Finite.fintype hbfin
  have hbsp' : ⊤ ≤ Submodule.span ℝ (Set.range (Subtype.val : ↥b → D)) := by
    rw [Subtype.range_coe]
    exact hbsp.ge
  set hbasis : Module.Basis ↥b ℝ D := Module.Basis.mk hbli hbsp' with hbk
  choose u hu using fun (i : ↥b) => hbsub i.2
  simp only [Set.mem_univ, true_and] at hu
  have hui : ∀ i : ↥b, (u i : V3) ∈ s := fun i => (u i).2
  have huc : ∀ i : ↥b, (⟨w₀ -ᵥ (u i : V3), hmemfam _ (u i).2⟩ : D) = (i : D) := fun i => hu i
  have hcoec : ∀ i : ↥b, ((i : D) : V3) = w₀ -ᵥ (u i : V3) := by
    intro i
    have hcc := congrArg (Submodule.subtype D) (huc i)
    simpa [Submodule.coe_subtype] using hcc.symm
  -- coordinate bound constants
  obtain ⟨Csum, hCdef⟩ : ∃ C : ℝ, C = ∑ i ∈ (Finset.univ : Finset ↥b),
    ‖(LinearMap.toContinuousLinearMap (hbasis.coord i) : D →L[ℝ] ℝ)‖ := ⟨_, rfl⟩
  have hCpos : 0 ≤ Csum := by
    rw [hCdef]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  obtain ⟨wδ, hwδT, hwδmin⟩ := Finset.exists_min_image T f hTne
  have hfδ : 0 < f wδ := hfT wδ hwδT
  -- the rint criterion
  refine mem_rint_iff.2 ⟨hymem, ?_⟩
  rw [affineSpan_convexHull]
  refine ⟨f wδ / (2 * (Csum + 1)), div_pos hfδ (by linarith), ?_⟩
  rintro z ⟨hzball, hzaff⟩
  have hzdist : dist z y < f wδ / (2 * (Csum + 1)) := Metric.mem_ball.1 hzball
  -- direction membership
  have hyspan : y ∈ (affineSpan ℝ s : Set V3) := by
    rw [← affineSpan_convexHull]
    exact subset_affineSpan ℝ _ hymem
  have hzdir : (z -ᵥ y) ∈ D := by
    rw [hDdef, ← direction_affineSpan ℝ s]
    exact AffineSubspace.vsub_mem_direction hzaff hyspan
  obtain ⟨eD, heDcoe⟩ : ∃ eD : D, ((eD : D) : V3) = z -ᵥ y :=
    ⟨⟨z -ᵥ y, hzdir⟩, rfl⟩
  have heDdist : ‖((eD : D) : V3)‖ < f wδ / (2 * (Csum + 1)) := by
    rw [heDcoe, vsub_eq_sub]
    rwa [dist_eq_norm] at hzdist
  obtain ⟨t, htdef⟩ : ∃ t : ↥b → ℝ, ∀ i, t i = hbasis.coord i eD := ⟨_, fun _ => rfl⟩
  have hcoord : ∀ i : ↥b, |t i| ≤
      ‖(LinearMap.toContinuousLinearMap (hbasis.coord i) : D →L[ℝ] ℝ)‖ * ‖((eD : D) : V3)‖ := by
    intro i
    have h1 := ContinuousLinearMap.le_opNorm
      (LinearMap.toContinuousLinearMap (hbasis.coord i) : D →L[ℝ] ℝ) eD
    rw [Real.norm_eq_abs] at h1
    rw [htdef]
    calc |hbasis.coord i eD| = ‖(LinearMap.toContinuousLinearMap
          (hbasis.coord i) : D →L[ℝ] ℝ) eD‖ := by
          rw [Real.norm_eq_abs]; rfl
      _ ≤ ‖(LinearMap.toContinuousLinearMap (hbasis.coord i) : D →L[ℝ] ℝ)‖ * ‖(eD : D)‖ := h1
      _ = ‖(LinearMap.toContinuousLinearMap (hbasis.coord i) : D →L[ℝ] ℝ)‖ * ‖((eD : D) : V3)‖ := by
          simp
  have hcoordsum : ∑ i ∈ (Finset.univ : Finset ↥b), |t i| ≤ Csum * ‖((eD : D) : V3)‖ := by
    calc ∑ i ∈ (Finset.univ : Finset ↥b), |t i| ≤ ∑ i ∈ (Finset.univ : Finset ↥b),
          (‖(LinearMap.toContinuousLinearMap (hbasis.coord i) : D →L[ℝ] ℝ)‖ * ‖((eD : D) : V3)‖) :=
          Finset.sum_le_sum (fun i _ => hcoord i)
      _ = (∑ i ∈ (Finset.univ : Finset ↥b),
            ‖(LinearMap.toContinuousLinearMap (hbasis.coord i) : D →L[ℝ] ℝ)‖) * ‖((eD : D) : V3)‖ :=
          (Finset.sum_mul _ _ _).symm
      _ = Csum * ‖((eD : D) : V3)‖ := by rw [hCdef]
  obtain ⟨g, hgdef⟩ : ∃ g : V3 → ℝ, ∀ w, g w = (∑ i ∈ (Finset.univ : Finset ↥b),
      if (u i : V3) = w then -(t i) else 0)
      + (if w = w₀ then ∑ i ∈ (Finset.univ : Finset ↥b), t i else 0) := ⟨_, fun _ => rfl⟩
  -- the zero-sum representation of z - y
  have hrepr : ((eD : D) : V3) = ∑ i ∈ (Finset.univ : Finset ↥b), t i • ((i : D) : V3) := by
    have h4 := congrArg (Submodule.subtype D) (hbasis.sum_repr (eD : D))
    rw [map_sum, hbk] at h4
    simp only [map_smul, Submodule.coe_subtype, Module.Basis.mk_apply] at h4
    rw [h4.symm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hbr : ((Module.Basis.mk hbli hbsp').repr eD) i = t i := by
      rw [← hbk]
      exact (htdef i).symm
    rw [hbr]
  have hsplit : ∑ i ∈ (Finset.univ : Finset ↥b), t i • ((i : D) : V3)
      = (∑ i ∈ (Finset.univ : Finset ↥b), t i) • w₀
        + ∑ i ∈ (Finset.univ : Finset ↥b), (-(t i)) • (u i : V3) := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hcoec i, vsub_eq_sub, smul_sub])]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul,
      Finset.sum_congr rfl (fun i _ => neg_smul (t i) ((u i : V3))), Finset.sum_neg_distrib,
      sub_eq_add_neg]
  have hA2' : ∀ i : ↥b, ∑ w ∈ T, (if (u i : V3) = w then -(t i) • w else 0)
      = -(t i) • ((u i : V3)) := by
    intro i
    rw [Finset.sum_ite_eq T (u i : V3) (fun w => -(t i) • w), if_pos (hsT (u i : V3) (hui i))]
  have hgvec : ∑ w ∈ T, g w • w = ((eD : D) : V3) := by
    have hgw' : ∀ w ∈ T, g w • w = (∑ i ∈ (Finset.univ : Finset ↥b),
        if (u i : V3) = w then -(t i) • w else 0)
        + (if w = w₀ then (∑ i ∈ (Finset.univ : Finset ↥b), t i) • w else 0) := by
      intro w _
      rw [hgdef w, add_smul, Finset.sum_smul]
      simp only [ite_smul, zero_smul]
    rw [Finset.sum_congr rfl (fun w hw => hgw' w hw),
      Finset.sum_add_distrib, Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hA2' i)]
    rw [Finset.sum_ite_eq' T w₀ (fun w => (∑ i ∈ (Finset.univ : Finset ↥b), t i) • w),
      if_pos hw₀T]
    rw [add_comm, ← hsplit, ← hrepr]
  have hsumg : ∑ w ∈ T, g w = 0 := by
    have hA' : ∀ i : ↥b, ∑ w ∈ T, (if (u i : V3) = w then -(t i) else 0) = -(t i) := by
      intro i
      rw [Finset.sum_ite_eq T (u i : V3) (fun _ => -(t i)), if_pos (hsT (u i : V3) (hui i))]
    have hA : ∑ w ∈ T, (∑ i ∈ (Finset.univ : Finset ↥b), if (u i : V3) = w then -(t i) else 0)
        = ∑ i ∈ (Finset.univ : Finset ↥b), -(t i) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hA' i)
    have hB : ∑ w ∈ T, (if w = w₀ then ∑ i ∈ (Finset.univ : Finset ↥b), t i else 0)
        = ∑ i ∈ (Finset.univ : Finset ↥b), t i := by
      rw [Finset.sum_ite_eq' T w₀ (fun _ => ∑ i ∈ (Finset.univ : Finset ↥b), t i),
        if_pos hw₀T]
    rw [Finset.sum_congr rfl (fun w (_ : w ∈ T) => by rw [hgdef w])]
    rw [Finset.sum_add_distrib, hA, hB, Finset.sum_neg_distrib]
    ring
  -- nonnegativity of the combined coefficients
  have hgw : ∀ w : V3, |g w| ≤ 2 * Csum * ‖((eD : D) : V3)‖ := by
    intro w
    have h1 : |g w| ≤ |∑ i ∈ (Finset.univ : Finset ↥b), if (u i : V3) = w then -(t i) else 0|
        + |if w = w₀ then ∑ i ∈ (Finset.univ : Finset ↥b), t i else 0| := by
      rw [hgdef w]
      exact abs_add_le _ _
    have h2 : |∑ i ∈ (Finset.univ : Finset ↥b), if (u i : V3) = w then -(t i) else 0|
        ≤ ∑ i ∈ (Finset.univ : Finset ↥b), |t i| := by
      refine le_trans (Finset.abs_sum_le_sum_abs
        (fun i => if (u i : V3) = w then -(t i) else 0) Finset.univ) ?_
      have hpi : ∀ i : ↥b, |if (u i : V3) = w then -(t i) else 0| ≤ |t i| := by
        intro i
        by_cases hic : (u i : V3) = w
        · rw [if_pos hic, abs_neg]
        · rw [if_neg hic, abs_zero]
          exact abs_nonneg (t i)
      exact Finset.sum_le_sum (fun i _ => hpi i)
    have h4 : |if w = w₀ then ∑ i ∈ (Finset.univ : Finset ↥b), t i else 0|
        ≤ |∑ i ∈ (Finset.univ : Finset ↥b), t i| := by
      by_cases hc : w = w₀
      · rw [if_pos hc]
      · rw [if_neg hc]
        norm_num
    have h5 : |∑ i ∈ (Finset.univ : Finset ↥b), t i|
        ≤ ∑ i ∈ (Finset.univ : Finset ↥b), |t i| :=
      Finset.abs_sum_le_sum_abs (fun i => t i) Finset.univ
    calc |g w| ≤ ∑ i ∈ (Finset.univ : Finset ↥b), |t i|
          + ∑ i ∈ (Finset.univ : Finset ↥b), |t i| := by linarith
      _ ≤ Csum * ‖((eD : D) : V3)‖ + Csum * ‖((eD : D) : V3)‖ := by linarith
      _ = 2 * Csum * ‖((eD : D) : V3)‖ := by ring
  have hcoeffpos : ∀ w ∈ T, 0 ≤ f w + g w := by
    intro w hw
    have hkey : |g w| < f w := by
      have hm : 0 < 2 * (Csum + 1) := by linarith
      have hbridge : 2 * Csum * ‖((eD : D) : V3)‖
          ≤ 2 * (Csum + 1) * ‖((eD : D) : V3)‖ := by
        nlinarith [hCpos, norm_nonneg ((eD : D) : V3)]
      have hlt : 2 * (Csum + 1) * ‖((eD : D) : V3)‖
          < 2 * (Csum + 1) * (f wδ / (2 * (Csum + 1))) :=
        mul_lt_mul_of_pos_left heDdist hm
      have hle : 2 * (Csum + 1) * (f wδ / (2 * (Csum + 1))) ≤ f wδ := by
        rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hm]
      calc |g w| ≤ 2 * Csum * ‖((eD : D) : V3)‖ := hgw w
        _ ≤ 2 * (Csum + 1) * ‖((eD : D) : V3)‖ := hbridge
        _ < 2 * (Csum + 1) * (f wδ / (2 * (Csum + 1))) := hlt
        _ ≤ f wδ := hle
        _ ≤ f w := hwδmin w hw
    have habs := abs_lt.1 hkey
    linarith
  have hcoeffsum : ∑ w ∈ T, (f w + g w) = 1 := by
    rw [Finset.sum_add_distrib, hone, hsumg]
    ring
  -- final assembly
  have hjoin : ∑ w ∈ T, g w • w + ∑ w ∈ T, f w • w = ∑ w ∈ T, (f w + g w) • w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w (_ : w ∈ T) =>
      (add_smul (g w) (f w) w).symm.trans (congrArg (fun r => r • w) (add_comm (g w) (f w))))
  have hzexp : z = ∑ w ∈ T, (f w + g w) • w := by
    have h1 : z = (z -ᵥ y) + y := by rw [vsub_eq_sub]; exact (sub_add_cancel z y).symm
    have h2 : (z -ᵥ y) = ((eD : D) : V3) := heDcoe.symm
    rw [h1, h2, ← hgvec, hy]
    rw [hjoin]
  have hzcm : T.centerMass (fun w => f w + g w) id = ∑ w ∈ T, (f w + g w) • w := by
    simp [Finset.centerMass, hcoeffsum]
  rw [hzexp, ← hzcm]
  exact Finset.centerMass_mem_convexHull T (fun w hw => hcoeffpos w hw)
    (by rw [hcoeffsum]; norm_num) (fun w hw => hTsub w hw)

/-- HOL `NOT_COLLINEAR_AFF_DIM_2` (counting_spheres.hl:3160). GIANT. -/
theorem NOT_COLLINEAR_AFF_DIM_2 (u0 u1 u2 : V3) (h : ¬ Collinear3 u0 u1 u2) :
    affDim ({u0, u1, u2} : Set V3) = 2 := by
  have hne : ({u0, u1, u2} : Set V3) ≠ ∅ := by
    intro hc
    have hm : u0 ∈ ({u0, u1, u2} : Set V3) := Set.mem_insert u0 ({u1, u2} : Set V3)
    rw [hc] at hm
    exact hm
  have hsub : vectorSpan ℝ ({u0, u1, u2} : Set V3) ≤
      Submodule.span ℝ ({u0 - u1, u0 - u2} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_left (k := ℝ) (Set.mem_insert u0 ({u1, u2} : Set V3)),
      Submodule.span_le]
    rintro d ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · show x -ᵥ x ∈ Submodule.span ℝ ({x - u1, x - u2} : Set V3)
      rw [vsub_self]
      exact Submodule.zero_mem _
    · show u0 -ᵥ x ∈ Submodule.span ℝ ({u0 - x, u0 - u2} : Set V3)
      exact Submodule.subset_span (Set.mem_insert (u0 - x) {u0 - u2})
    · show u0 -ᵥ x ∈ Submodule.span ℝ ({u0 - u1, u0 - x} : Set V3)
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton (u0 - x)))
  have hle2 : (Module.finrank ℝ (vectorSpan ℝ ({u0, u1, u2} : Set V3)) : ℕ) ≤ 2 := by
    calc Module.finrank ℝ (vectorSpan ℝ ({u0, u1, u2} : Set V3))
        ≤ Module.finrank ℝ (Submodule.span ℝ ({u0 - u1, u0 - u2} : Set V3)) :=
          Submodule.finrank_mono hsub
      _ ≤ 2 := by
          refine le_trans (finrank_span_le_card (R := ℝ) (M := V3)
            (s := ({u0 - u1, u0 - u2} : Set V3))) ?_
          have hncard : ({u0 - u1, u0 - u2} : Set V3).toFinset.card
              ≤ ({u0 - u2} : Set V3).ncard + 1 := by
            have h1 : ({u0 - u1, u0 - u2} : Set V3).ncard
                ≤ ({u0 - u2} : Set V3).ncard + 1 :=
              Set.ncard_insert_le (u0 - u1) ({u0 - u2} : Set V3)
            have h3 : ({u0 - u1, u0 - u2} : Set V3).ncard
                = ({u0 - u1, u0 - u2} : Set V3).toFinset.card :=
              Set.ncard_eq_toFinset_card' _
            omega
          have h4 : ({u0 - u2} : Set V3).ncard = 1 := Set.ncard_singleton _
          omega
  rw [affDim, if_neg hne]
  have hge : ¬ (Module.finrank ℝ (vectorSpan ℝ ({u0, u1, u2} : Set V3)) ≤ 1) := fun h1 =>
    h (show Collinear ℝ ({u0, u1, u2} : Set V3) from
      (collinear_iff_finrank_le_one (s := ({u0, u1, u2} : Set V3))).2 h1)
  push_neg at hge
  have h2 : (2:ℤ) ≤ (Module.finrank ℝ (vectorSpan ℝ ({u0, u1, u2} : Set V3)) : ℤ) :=
    by exact_mod_cast hge
  have hle : (Module.finrank ℝ (vectorSpan ℝ ({u0, u1, u2} : Set V3)) : ℤ) ≤ 2 :=
    by exact_mod_cast hle2
  omega

/-- HOL `FACET_AFF_DIM_2` (counting_spheres.hl:3171). GIANT. -/
theorem FACET_AFF_DIM_2 (p f : Set V3) (hp : polyhedron p)
    (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p) : affDim f = 2 := by
  -- `0 ∈ interior p` forces `p` full-dimensional, hence `affDim p = 3`; the
  -- facet equation `affDim f = affDim p - 1` finishes.
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

/-- HOL `CONE0_FCHANGED_AFF_GT` (counting_spheres.hl:3185). GIANT. -/
theorem CONE0_FCHANGED_AFF_GT (s : Set V3) (hf : s.Finite) (h : 1 < s.ncard)
    (h0 : (0 : V3) ∉ s) : cone0P22 0 s ⊆ fchanged (convexHull ℝ s) := by
  -- Filled (kit wave): transport `v = (1 - f 0) • v₁` with `1 - f 0 > 0`
  -- (nonapex point `x'` via `h : 1 < s.ncard`), rescaled coefficients
  -- `g w = f w / (1 - f 0)` give `v₁ ∈ affGt ∅ s`, closed by
  -- AFF_GT_RELATIVE_INTERIOR + the `fchanged` anon.

  rintro v ⟨f, hfin, hv, hpos, hone⟩
  set T := hfin.toFinset with hTdef
  have hfinmem : ∀ w ∈ T, w ∈ ({0} ∪ s) := fun w hw => (Set.Finite.mem_toFinset hfin).mp hw
  have h0T : (0:V3) ∈ T := (Set.Finite.mem_toFinset hfin).mpr (Set.mem_union_left _ (Set.mem_singleton 0))
  have h0' : (0:V3) ∉ hf.toFinset := fun hmem =>
    h0 (by have := (Set.Finite.mem_toFinset hf).mp hmem; simpa using this)
  have hsT : ∀ w ∈ s, w ∈ T := fun w hw =>
    (Set.Finite.mem_toFinset hfin).mpr (Set.mem_union_right _ hw)
  have hTs : ∀ w ∈ T, w ≠ 0 → w ∈ s := by
    intro w hw hw0
    rcases hfinmem w hw with hw0' | hws
    · exact absurd hw0' hw0
    · exact hws
  have hTeq : T = insert 0 hf.toFinset := by
    refine Finset.ext fun w => ?_
    constructor
    · intro hw
      have hw' := hfinmem w hw
      rcases hw' with hw0 | hws
      · exact Finset.mem_insert.2 (Or.inl hw0)
      · exact Finset.mem_insert.2 (Or.inr ((Set.Finite.mem_toFinset hf).mpr hws))
    · intro hw
      have hw' := Finset.mem_insert.1 hw
      rcases hw' with hw0 | hw
      · exact (Set.Finite.mem_toFinset hfin).mpr (Or.inl hw0)
      · exact (Set.Finite.mem_toFinset hfin).mpr (Or.inr ((Set.Finite.mem_toFinset hf).mp hw))
  -- a nonapex point of s
  have hsne : s ≠ ∅ := by
    intro hc
    rw [hc] at h
    simp at h
  obtain ⟨x', hx'⟩ := Set.nonempty_iff_ne_empty.mpr hsne
  have hx'T : x' ∈ hf.toFinset := by
    refine (Set.Finite.mem_toFinset hf).mpr ?_
    simpa using hx'
  -- 1 - f 0 > 0
  have honeE : ∑ w ∈ hf.toFinset, f w = 1 - f 0 := by
    have h1 := hone
    rw [hTeq, Finset.sum_insert h0'] at h1
    linarith
  have hEx' : f x' ≤ ∑ w ∈ hf.toFinset, f w :=
    Finset.single_le_sum
      (fun w hw => le_of_lt (hpos w (by
        simpa using (Set.Finite.mem_toFinset hf).mp hw)))
      hx'T
  have hfx' : 0 < f x' := hpos x' hx'
  have h1a : 0 < 1 - f 0 := by
    rw [← honeE]
    exact lt_of_lt_of_le hfx' hEx'
  -- the rescaled coefficients give a relative-interior point
  have hvenz : (1 - f 0) ≠ 0 := ne_of_gt h1a
  set g : V3 → ℝ := fun w => f w / (1 - f 0) with hgdef
  have hgpos : ∀ w ∈ s, 0 < g w := fun w hw => div_pos (hpos w hw) h1a
  have hgsum : ∑ w ∈ hf.toFinset, g w = 1 := by
    rw [hgdef, ← Finset.sum_div, honeE]
    exact div_self hvenz
  have hfinU : ((∅ : Set V3) ∪ s).Finite := by simpa using hf
  have hUeq : hfinU.toFinset = hf.toFinset := by
    refine Finset.ext fun w => ?_
    rw [Set.Finite.mem_toFinset hfinU, Set.Finite.mem_toFinset hf]
    simp
  -- v = (1 - f 0) • v1 where v1 is the relative-interior point
  have hveq : v = (1 - f 0) • ∑ w ∈ hfinU.toFinset, g w • w := by
    rw [hUeq, hgdef, Finset.smul_sum]
    have h2' : ∑ w ∈ hf.toFinset, (1 - f 0) • (g w • w)
        = ∑ w ∈ hf.toFinset, ((1 - f 0) * (f w / (1 - f 0))) • w := by
      refine Finset.sum_congr rfl (fun w hw => ?_)
      rw [hgdef, smul_smul]
    have h2 : ∑ w ∈ hf.toFinset, ((1 - f 0) * (f w / (1 - f 0))) • w
        = ∑ w ∈ hf.toFinset, f w • w :=
      Finset.sum_congr rfl (fun w hw => by
        rw [mul_div_cancel₀ (f w) hvenz])
    have h3 : ∑ w ∈ T, f w • w = ∑ w ∈ hf.toFinset, f w • w := by
      rw [hTeq, Finset.sum_insert h0', smul_zero, zero_add]
    rw [h2', h2, ← h3]
    exact hv
  have hgsumU : ∑ w ∈ hfinU.toFinset, g w = 1 := by rw [hUeq]; exact hgsum
  have v1mem : (∑ w ∈ hfinU.toFinset, g w • w) ∈ intrinsicInterior ℝ (convexHull ℝ s) :=
    AFF_GT_RELATIVE_INTERIOR s hf h ⟨g, hfinU, rfl, hgpos, hgsumU⟩
  refine ⟨∑ w ∈ hfinU.toFinset, g w • w, 1 - f 0, hveq, v1mem, h1a⟩

/-- HOL `CONE0_FCHANGED` (counting_spheres.hl:3288). GIANT. -/
theorem CONE0_FCHANGED (p f : Set V3) (u0 u1 u2 : V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p) (hf : FacetOf f p)
    (hc : ¬ Collinear3 u0 u1 u2) (hsub : {u0, u1, u2} ⊆ f) :
    cone0P22 0 {u0, u1, u2} ⊆ fchanged f := by
  sorry

/-! ### Azim axis bridge (private helpers for `collinear_translate_axis`/`azim_axis`)

The azimuth `azim v w w1 w2` is stable along its axis line: translating the
base to the origin (`p22_azim_trans`, flyspeck AZIM_TRANSLATION) and shifting
the measured points by a multiple of the axis vector (`p22_azim_axis_shift`)
both preserve it, the latter because the `AzimSpec` witnesses only change by
adding the shift to the axis components `h1`/`h2`. -/

/-- flyspeck `AZIM_TRANSLATION` (azim is translation invariant), rebuilt from
`Kepler.Geom.WedgeVolume`'s private route. -/
private theorem p22_azim_trans (x a b c : V3) :
    azim x a b c = azim 0 (a - x) (b - x) (c - x) := by
  have hcol : ∀ y z : V3, Collinear3 x a y ↔ Collinear3 0 (a - x) (y - x) := by
    intro y z
    by_cases h : a = x
    · rw [h]
      simp only [sub_self]
      constructor <;> intro _ <;> exact collinear3_of_eq rfl
    · have h' : a - x ≠ 0 := sub_ne_zero.mpr h
      rw [collinear3_iff_smul h, collinear3_iff_smul h']
      simp only [sub_zero]
  unfold azim
  rw [hcol b c, hcol c c]
  have hpred : AzimSpec x a b c = AzimSpec 0 (a - x) (b - x) (c - x) :=
    funext fun _ => by
      unfold AzimSpec
      simp only [sub_zero, sub_ne_zero]
      have hd : dist a x = dist (a - x) 0 := by rw [dist_eq_norm, dist_eq_norm, sub_zero]
      rw [hd]
  rw [hpred]

/-- `Collinear3 0 a p` is stable under shifting `p` along the axis `a`. -/
private theorem p22_collinear3_axis_shift {a p : V3} (s : ℝ) :
    Collinear3 0 a p ↔ Collinear3 0 a (p + s • a) := by
  by_cases ha : a = 0
  · subst ha
    constructor <;> intro _ <;> exact collinear3_of_eq rfl
  · rw [collinear3_iff_smul ha, collinear3_iff_smul ha]
    simp only [sub_zero]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c + s, by rw [hc]; module⟩
    · rintro ⟨c, hc⟩
      exact ⟨c - s, by rw [sub_smul, ← hc]; module⟩

/-- The `AzimSpec` witnesses only change their axis components under an
axis-parallel shift of the measured points. -/
private theorem p22_azimSpec_axis_shift {a p q : V3} {θ : ℝ} (s : ℝ) :
    AzimSpec 0 a p q θ ↔ AzimSpec 0 a (p + s • a) (q + s • a) θ := by
  unfold AzimSpec
  constructor
  · rintro ⟨hle, hlt, h1, h2, hframe⟩
    refine ⟨hle, hlt, h1 + s, h2 + s, ?_⟩
    intro e1 e2 e3 hon hax hw
    obtain ⟨psi, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hframe e1 e2 e3 hon hax hw
    have rep1 : (p + s • a) - 0 =
        (r1 * Real.cos psi) • e1 + (r1 * Real.sin psi) • e2 + (h1 + s) • (a - 0) := by
      rw [sub_zero, sub_zero] at hrep1
      rw [sub_zero, sub_zero, hrep1, add_assoc, ← add_smul]
    have rep2 : (q + s • a) - 0 =
        (r2 * Real.cos (psi + θ)) • e1 + (r2 * Real.sin (psi + θ)) • e2 + (h2 + s) • (a - 0) := by
      rw [sub_zero, sub_zero] at hrep2
      rw [sub_zero, sub_zero, hrep2, add_assoc, ← add_smul]
    exact ⟨psi, r1, r2, rep1, rep2, hr1, hr2⟩
  · rintro ⟨hle, hlt, h1, h2, hframe⟩
    refine ⟨hle, hlt, h1 - s, h2 - s, ?_⟩
    intro e1 e2 e3 hon hax hw
    obtain ⟨psi, r1, r2, hrep1, hrep2, hr1, hr2⟩ := hframe e1 e2 e3 hon hax hw
    have rep1 : p - 0 =
        (r1 * Real.cos psi) • e1 + (r1 * Real.sin psi) • e2 + (h1 - s) • (a - 0) := by
      rw [sub_zero, sub_zero] at hrep1
      rw [sub_zero, sub_zero, sub_smul, ← add_sub_assoc, ← hrep1, add_sub_cancel_right]
    have rep2 : q - 0 =
        (r2 * Real.cos (psi + θ)) • e1 + (r2 * Real.sin (psi + θ)) • e2 + (h2 - s) • (a - 0) := by
      rw [sub_zero, sub_zero] at hrep2
      rw [sub_zero, sub_zero, sub_smul, ← add_sub_assoc, ← hrep2, add_sub_cancel_right]
    exact ⟨psi, r1, r2, rep1, rep2, hr1, hr2⟩

/-- `azim 0 a p q` is invariant under shifting the measured points along the
axis `a` (degenerate and nondegenerate branches agree). -/
private theorem p22_azim_axis_shift (a p q : V3) (s : ℝ) :
    azim 0 a p q = azim 0 a (p + s • a) (q + s • a) := by
  have hc : (Collinear3 0 a p ∨ Collinear3 0 a q) ↔
      (Collinear3 0 a (p + s • a) ∨ Collinear3 0 a (q + s • a)) :=
    or_congr (p22_collinear3_axis_shift s) (p22_collinear3_axis_shift s)
  have hpred : AzimSpec 0 a p q = AzimSpec 0 a (p + s • a) (q + s • a) :=
    funext fun _ => propext (p22_azimSpec_axis_shift s)
  by_cases hdeg : Collinear3 0 a p ∨ Collinear3 0 a q
  · unfold azim
    rw [if_pos hdeg, if_pos (hc.mp hdeg)]
  · unfold azim
    rw [if_neg hdeg, if_neg (hc.not.mp hdeg), hpred]

/-- HOL `collinear_translate_axis` (counting_spheres.hl:3332). Filled: both
sides reduce, via `collinear3_iff_smul`, to `u2 ∈ span ℝ (u1 - t•u1)`; the
degenerate case `u1 = t•u1` is trivial and the scalar-fraction bookkeeping
`t•u1 = (t/(1-t)) • (u1 - t•u1)` is done once as `haxis`. -/
theorem collinear_translate_axis (t : ℝ) (u1 u2 : V3) :
    Collinear3 (t • u1) u1 u2 ↔ Collinear3 0 (u1 - t • u1) u2 := by
  by_cases ha : u1 - t • u1 = 0
  · constructor
    · intro _
      exact collinear3_of_eq ha
    · intro _
      exact collinear3_of_eq (sub_eq_zero.mp ha)
  · have hne : u1 ≠ t • u1 := fun he => ha (by rw [← he]; exact sub_self u1)
    rw [collinear3_iff_smul hne, collinear3_iff_smul ha]
    simp only [sub_zero]
    have h1v : u1 - t • u1 = (1 - t) • u1 := by module
    have ht : (1:ℝ) - t ≠ 0 := by
      intro hcon
      rw [h1v, hcon, zero_smul] at ha
      exact ha rfl
    have haxis : t • u1 = (t / (1 - t)) • (u1 - t • u1) := by
      rw [h1v, smul_smul]
      congr 1
      field_simp
    have haxis' : (t / (1 - t)) • (u1 - t • u1) = t • u1 := haxis.symm
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c + t / (1 - t), ?_⟩
      rw [add_smul, haxis', ← hc, sub_add_cancel]
    · rintro ⟨c, hc⟩
      refine ⟨c - t / (1 - t), ?_⟩
      rw [sub_smul, haxis', hc]

/-- HOL `azim_axis` (counting_spheres.hl:3347). Filled: translate the base
`t•u1` to the origin (`p22_azim_trans`), then shift the measured points `u`,
`w` back along the axis `u1 - t•u1` by `-t/(1-t)` (`p22_azim_axis_shift`),
using `t•u1 = (t/(1-t)) • (u1 - t•u1)`.  The non-collinearity hypotheses
guarantee only nondegeneracy; the identity itself is unconditional. -/
theorem azim_axis (t : ℝ) (u1 u w : V3)
    (h1 : ¬ Collinear3 (t • u1) u1 u) (h2 : ¬ Collinear3 (t • u1) u1 w) :
    azim (t • u1) u1 u w = azim 0 (u1 - t • u1) u w := by
  have hne : u1 - t • u1 ≠ 0 := by
    intro he
    apply h1
    rw [← sub_eq_zero.mp he]
    exact collinear3_of_eq rfl
  have h1v : u1 - t • u1 = (1 - t) • u1 := by module
  have ht : (1:ℝ) - t ≠ 0 := by
    intro hcon
    rw [h1v, hcon, zero_smul] at hne
    exact hne rfl
  have haxis : t • u1 = (t / (1 - t)) • (u1 - t • u1) := by
    rw [h1v, smul_smul]
    congr 1
    field_simp
  have haxis' : (t / (1 - t)) • (u1 - t • u1) = t • u1 := haxis.symm
  have e1 : u - t • u1 = u + (-(t / (1 - t))) • (u1 - t • u1) := by
    rw [neg_smul, haxis']; abel
  have e2 : w - t • u1 = w + (-(t / (1 - t))) • (u1 - t • u1) := by
    rw [neg_smul, haxis']; abel
  calc azim (t • u1) u1 u w
      = azim 0 (u1 - t • u1) (u - t • u1) (w - t • u1) := p22_azim_trans _ _ _ _
    _ = azim 0 (u1 - t • u1)
          (u + (-(t / (1 - t))) • (u1 - t • u1))
          (w + (-(t / (1 - t))) • (u1 - t • u1)) := by rw [e1, e2]
    _ = azim 0 (u1 - t • u1) u w :=
          (p22_azim_axis_shift (u1 - t • u1) u w (-(t / (1 - t)))).symm

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
theorem CONE0_AFF_GT (x : V3) (U : Set V3) : cone0P22 x U = affGt {x} U := rfl

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
  -- Both sides unfold, via `AFF_GT_1_3`, to the explicit 4-coefficient form;
  -- the `u0`-coefficient rescales by `t` (`f u0 ↦ f u0 / t`), the `vec 0`
  -- apex coefficient absorbs the change in the scalar sum.
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hdis' : Disjoint ({0} : Set V3) {t • u0, u1, u2} := DISJOINT0_SCALE t u0 u1 u2 hd ht0
  show affGt ({0} : Set V3) {u0, u1, u2} = affGt ({0} : Set V3) {t • u0, u1, u2}
  rw [AFF_GT_1_3 (0 : V3) u0 u1 u2 hd, AFF_GT_1_3 (0 : V3) (t • u0) u1 u2 hdis']
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, b, c, d, hb, hc, hdd, hsum, hyeq⟩
    refine ⟨1 - b / t - c - d, b / t, c, d, div_pos hb ht, hc, hdd, ?_, ?_⟩
    · linarith
    · rw [hyeq]
      have hbb : b / t * t = b := by field_simp
      have hbc : (b / t) • (t • u0) = b • u0 := by
        rw [smul_smul, hbb]
      simp only [smul_zero, hbc]
  · rintro ⟨a, b, c, d, hb, hc, hdd, hsum, hyeq⟩
    refine ⟨1 - b * t - c - d, b * t, c, d, mul_pos hb ht, hc, hdd, ?_, ?_⟩
    · linarith
    · rw [hyeq]
      have hbc : (b * t) • u0 = b • (t • u0) := (smul_smul b t u0).symm
      simp only [smul_zero, hbc]

/-- `¬ Coplanar {0,u0,u1,u2}` separates each `uᵢ` from the origin (HOL
`Planarity.notcoplanar_disjoint`, counting_spheres.hl:3837 proof step). -/
private theorem p22_notCoplanar_ne0 {u0 u1 u2 : V3}
    (hcp : ¬ Coplanar ({0, u0, u1, u2} : Set V3)) : u0 ≠ 0 ∧ u1 ≠ 0 ∧ u2 ≠ 0 := by
  refine ⟨fun h => hcp ?_, fun h => hcp ?_, fun h => hcp ?_⟩
  · have hset : ({0, u0, u1, u2} : Set V3) = ({u0, u1, u2} : Set V3) := by
      rw [h]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact coplanar_triple u0 u1 u2
  · have hset : ({0, u0, u1, u2} : Set V3) = ({0, u0, u2} : Set V3) := by
      rw [h]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact coplanar_triple 0 u0 u2
  · have hset : ({0, u0, u1, u2} : Set V3) = ({0, u0, u1} : Set V3) := by
      rw [h]; ext q; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact coplanar_triple 0 u0 u1

/-- Scaling one point by `t ≠ 0` preserves non-coplanarity with the origin
(HOL `COPLANAR_SPECIAL_SCALE`, counting_spheres.hl:3837 proof step). -/
private theorem p22_coplanar_scale {u0 u1 u2 : V3}
    (hcp : ¬ Coplanar ({0, u0, u1, u2} : Set V3)) {t : ℝ} (ht : t ≠ 0) :
    ¬ Coplanar ({0, t • u0, u1, u2} : Set V3) := by
  intro hc
  obtain ⟨a, b, c, hsub⟩ := hc
  have h0 : (0 : V3) ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
  have hx : t • u0 ∈ (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) := hsub (by simp)
  refine hcp ⟨a, b, c, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp0 | hpt | hpu1 | hpu2
  · rw [hp0]; exact h0
  · -- the plane through `a,b,c` contains `0`, hence is closed under scalars
    have hlm : AffineMap.lineMap (0 : V3) (t • u0) t⁻¹ ∈
        (affineSpan ℝ ({a, b, c} : Set V3) : Set V3) :=
      AffineMap.lineMap_mem (t⁻¹ : ℝ) h0 hx
    have hid : u0 = AffineMap.lineMap (0 : V3) (t • u0) t⁻¹ := by
      rw [AffineMap.lineMap_apply]
      have hvsub : (t • u0) -ᵥ (0 : V3) = t • u0 := by simp only [vsub_eq_sub, sub_zero]
      rw [hvsub, vadd_eq_add, add_zero, smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [hpt, hid]
    exact hlm
  · rw [hpu1]; exact hsub (by simp)
  · rw [hpu2]; exact hsub (by simp)

/-- HOL `NOT_COPLANAR_NOT_COLLINEAR` (counting_spheres.hl:3837 proof step):
`¬ Coplanar {0,u0,u1,u2}` forces the last three points off a common line. -/
private theorem p22_notCollinear3_of_notCoplanar {u0 u1 u2 : V3}
    (hcp : ¬ Coplanar ({0, u0, u1, u2} : Set V3)) : ¬ Collinear3 u0 u1 u2 := by
  intro hc
  apply hcp
  rw [Collinear3, collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨p₀, v, hv⟩ := hc
  have hsub3 : ({p₀, p₀ + v} : Set V3) ⊆ ({p₀, p₀ + v, 0} : Set V3) := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
    tauto
  have hmono : ∀ q : V3, q ∈ (affineSpan ℝ ({p₀, p₀ + v} : Set V3) : Set V3) →
      q ∈ (affineSpan ℝ ({p₀, p₀ + v, 0} : Set V3) : Set V3) := by
    intro q hq
    exact affineSpan_mono ℝ hsub3 hq
  have hid (w : V3) (hw : w ∈ ({u0, u1, u2} : Set V3)) :
      ∃ r : ℝ, w = AffineMap.lineMap (p₀ : V3) (p₀ + v) r ∧
        AffineMap.lineMap (p₀ : V3) (p₀ + v) r ∈
          (affineSpan ℝ ({p₀, p₀ + v} : Set V3) : Set V3) := by
    obtain ⟨r, hr⟩ := hv w hw
    refine ⟨r, ?_, AffineMap.lineMap_mem_affineSpan_pair r p₀ (p₀ + v)⟩
    rw [AffineMap.lineMap_apply]
    have hvsub : (p₀ + v) -ᵥ p₀ = v := by simp only [vsub_eq_sub]; abel
    rw [hvsub]
    exact hr
  refine ⟨p₀, p₀ + v, (0 : V3), fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp0 | hpu0 | hpu1 | hpu2
  · rw [hp0]
    exact SetLike.mem_coe.mpr (mem_affineSpan ℝ (by simp))
  · obtain ⟨r, hid0, hlm⟩ := hid u0 (by simp)
    rw [hpu0, hid0]
    exact hmono _ hlm
  · obtain ⟨r, hid1, hlm⟩ := hid u1 (by simp)
    rw [hpu1, hid1]
    exact hmono _ hlm
  · obtain ⟨r, hid2, hlm⟩ := hid u2 (by simp)
    rw [hpu2, hid2]
    exact hmono _ hlm

/-- HOL `CONE0_FCHANGED_SCALE` (counting_spheres.hl:3837). GIANT. -/
theorem CONE0_FCHANGED_SCALE (p f : Set V3) (u0 u1 u2 : V3) (t : ℝ)
    (hp : polyhedron p) (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p)
    (hf : FacetOf f p) (hcp : ¬ Coplanar ({0, u0, u1, u2} : Set V3))
    (hsub : {t • u0, u1, u2} ⊆ f) (ht : 0 < t) :
    cone0P22 0 {u0, u1, u2} ⊆ fchanged f := by
  -- CONE0_SCALE rescales the cone to `{t•u0, u1, u2}`; the coplanarity kit
  -- feeds the scaled triple to `CONE0_FCHANGED` (HOL proof assembly).
  have ht0 : t ≠ 0 := ne_of_gt ht
  obtain ⟨hu0, hu1, hu2⟩ := p22_notCoplanar_ne0 hcp
  have hd : Disjoint ({0} : Set V3) ({u0, u1, u2} : Set V3) := by
    rw [Set.disjoint_singleton_left]
    intro h0in
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0in
    rcases h0in with h | h | h
    · exact hu0 h.symm
    · exact hu1 h.symm
    · exact hu2 h.symm
  have hcp' : ¬ Coplanar ({0, t • u0, u1, u2} : Set V3) := p22_coplanar_scale hcp ht0
  have hnc : ¬ Collinear3 (t • u0) u1 u2 := p22_notCollinear3_of_notCoplanar hcp'
  rw [CONE0_SCALE t u0 u1 u2 hd ht]
  exact CONE0_FCHANGED p f (t • u0) u1 u2 hp hb hi hf hnc hsub

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
      X ⊆ affGt {0, v} {w0, w1} ∩ W ∧
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

/-- HOL `NOT_COLLINEAR` (counting_spheres.hl:4150). Filled: some coordinate
`v i` is nonzero; shearing a basis vector gives `u ≠ 0` with `v ⬝ᵥ u = 0`,
which cannot be a real multiple of `v`. -/
theorem NOT_COLLINEAR (v : V3) (hv : v ≠ 0) : ∃ u : V3, ¬ Collinear3 0 v u := by
  classical
  have hcoord : ∃ i : Fin 3, (v : Fin 3 → ℝ) i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (PiLp.ext fun i => by simp [hcon i])
  obtain ⟨i, hi⟩ := hcoord
  obtain ⟨j, hji⟩ : ∃ j : Fin 3, j ≠ i := ⟨i + 1, by fin_cases i <;> simp⟩
  set u : V3 := EuclideanSpace.single j (1:ℝ)
    - ((v : Fin 3 → ℝ) j / (v : Fin 3 → ℝ) i) • EuclideanSpace.single i (1:ℝ) with hu
  refine ⟨u, ?_⟩
  intro hcol
  obtain ⟨c, hc⟩ := (collinear3_iff_smul (v := (0:V3)) (w := v) (w1 := u) hv).mp hcol
  rw [sub_zero, sub_zero] at hc
  have hvs : ∀ k : Fin 3,
      v ⬝ᵥ (EuclideanSpace.single k (1:ℝ)) = (v : Fin 3 → ℝ) k := by
    intro k
    rw [← inner_eq_dot, EuclideanSpace.inner_single_right]
    simp
  have hdot0 : v ⬝ᵥ u = 0 := by
    rw [hu, WithLp.ofLp_sub, WithLp.ofLp_smul, dotV_sub_right, dotV_smul_right, hvs j, hvs i]
    field_simp
    ring
  rw [hc, WithLp.ofLp_smul] at hdot0
  have hvv : 0 < v ⬝ᵥ v := by
    rw [show v ⬝ᵥ v = ‖v‖ ^ 2 from (norm_sq_eq_dot v).symm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hc0 : c = 0 := by
    have h1 : c * (v ⬝ᵥ v) = 0 := by
      rw [← dotV_smul_right v c v]
      exact hdot0
    exact mul_right_cancel₀ (ne_of_gt hvv) (by rw [h1, zero_mul])
  have huj : (u : Fin 3 → ℝ) j = 1 := by
    rw [hu]
    simp [WithLp.ofLp_sub, WithLp.ofLp_smul, PiLp.single_apply, hji]
  rw [hc, hc0, WithLp.ofLp_smul, zero_smul] at huj
  exact absurd huj (by simp)

/-- HOL `gotcjah_prep` (counting_spheres.hl:4174). Filled: all conjuncts are
elementary — the perpendicular foot `u0` enters the sharp cone, hence
`fchanged c`, and dotting with `v` pins the cone scaling to `1`. -/
theorem gotcjah_prep (c : Set V3) (v : V3) (b : ℝ) (P : Set V3) (WF : Set V3)
    (t : ℝ) (n : ℕ) (u0 : V3) (A : Set V3)
    (hP : polyhedron P) (hbP : Bornology.IsBounded P) (hb : 0 < b)
    (hi : (0 : V3) ∈ interior P) (hf : FacetOf c P) (hA : A = {p : V3 | p ⬝ᵥ v = b})
    (hu0 : u0 = (b / (v ⬝ᵥ v)) • v) (hfc : fchanged c = WF) (ht : 0 < t ∧ t < 1)
    (hPA : P ∩ {p : V3 | p ⬝ᵥ v = b} = c) (hsub : rconeGt 0 v t ⊆ WF)
    (hsize : ({u : Set V3 | FacetOf u c}).Finite ∧ ({u : Set V3 | FacetOf u c}).ncard = n) :
    c ⊆ A ∧ v ≠ 0 ∧ 0 < v ⬝ᵥ v ∧ u0 ∈ rconeGt 0 v t ∧ u0 ∈ c ∧
      rconeGt 0 v t ∩ A ⊆ c ∧ ∃ u : V3, ¬ Collinear3 0 v u := by
  have hcA : c ⊆ A := by
    intro p hp
    have hp2 : p ∈ P ∩ {q : V3 | q ⬝ᵥ v = b} := by rw [hPA]; exact hp
    have hpb : p ⬝ᵥ v = b := hp2.2
    rw [hA]
    exact hpb
  have hv0 : v ≠ 0 := by
    intro h0
    subst h0
    have hd0 : ∀ q : V3, q ⬝ᵥ (0:V3) = 0 := by
      intro q; rw [← inner_eq_dot]; simp
    refine hf.2.1 ?_
    rw [← hPA]
    refine Set.ext (fun q => ⟨fun hq => ?_, fun hq => absurd hq (Set.notMem_empty q)⟩)
    have hq3 : q ⬝ᵥ (0:V3) = b := Set.mem_setOf.mp hq.2
    rw [hd0 q] at hq3
    exact absurd hq3.symm (ne_of_gt hb)
  have hvv : 0 < v ⬝ᵥ v := by
    rw [← norm_sq_eq_dot]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv0)
  have hu0v : u0 ⬝ᵥ v = b := by
    rw [hu0, dotV_smul_left]
    field_simp
  have hnorm : ‖u0‖ * ‖v‖ = b := by
    rw [hu0, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hb hvv)]
    have hsq : ‖v‖ * ‖v‖ = v ⬝ᵥ v := by
      rw [← pow_two]; exact norm_sq_eq_dot v
    calc (b / (v ⬝ᵥ v)) * ‖v‖ * ‖v‖ = b / (v ⬝ᵥ v) * (‖v‖ * ‖v‖) := by ring
      _ = b / (v ⬝ᵥ v) * (v ⬝ᵥ v) := by rw [hsq]
      _ = b := div_mul_cancel₀ b (ne_of_gt hvv)
  have hrc : u0 ∈ rconeGt 0 v t := by
    have h2 : b * t < b := by
      have := mul_lt_mul_of_pos_left ht.2 hb
      rwa [mul_one] at this
    rw [rconeGt_zero_mem, hnorm, hu0v]
    exact h2
  -- the cone lies in `fchanged c`; dotting with `v` pins the scaling to 1
  have hpin : ∀ x ∈ rconeGt 0 v t, x ⬝ᵥ v = b → ∃ v1 : V3, v1 ∈ c ∧ x = v1 := by
    intro x hx hxb
    have hmem : x ∈ fchanged c := by rw [hfc]; exact hsub hx
    obtain ⟨v1, s, hxeq, hv1ri, hs⟩ := Set.mem_setOf.mp hmem
    have hv1c : v1 ∈ c := intrinsicInterior_subset hv1ri
    have hv1A : v1 ⬝ᵥ v = b := by
      have hmem' : v1 ∈ A := hcA hv1c
      rw [hA] at hmem'
      exact Set.mem_setOf.mp hmem'
    have hscal : x ⬝ᵥ v = s * (v1 ⬝ᵥ v) := by
      rw [hxeq, dotV_smul_left]
    have hs1 : s = 1 := by
      have h2 : s * (v1 ⬝ᵥ v) = b := by rw [← hscal]; exact hxb
      have h3 : s * b = b := by rwa [hv1A] at h2
      exact mul_right_cancel₀ (ne_of_gt hb) (by rw [h3, one_mul])
    exact ⟨v1, hv1c, by rw [hxeq, hs1, one_smul]⟩
  refine ⟨hcA, hv0, hvv, hrc, ?_, ?_, NOT_COLLINEAR v hv0⟩
  · obtain ⟨v1, hv1c, heq⟩ := hpin u0 hrc hu0v
    rw [heq]
    exact hv1c
  · intro x hx
    have hxb : x ⬝ᵥ v = b := by
      rw [hA] at hx
      exact hx.2
    obtain ⟨v1, hv1c, heq⟩ := hpin x hx.1 hxb
    rw [heq]
    exact hv1c

/-- HOL `convex_sum_corollary` supporting lemma: `u ↦ asn (sin u * t)` is
concave on `[0, π]` for `0 < t < 1`.  Its derivative `t cos u / B(u)` with
`B(u)² = 1 - t² sin²u` is antitone on `(0, π)` — after cross-multiplying by
the positive factor `t/(B(u)B(v))` the core identity is
`cos²u·B(v)² − cos²v·B(u)² = (1−t²)(sin²v − sin²u)`. -/
private theorem p22_arcsin_sin_concave {t : ℝ} (ht1 : 0 < t) (ht2 : t < 1) :
    ConcaveOn ℝ (Set.Icc 0 Real.pi) (fun u => asn (Real.sin u * t)) := by
  have hsinb : ∀ u : ℝ, -1 ≤ Real.sin u ∧ Real.sin u ≤ 1 :=
    fun u => abs_le.mp (Real.abs_sin_le_one u)
  have hne1 : ∀ u : ℝ, Real.sin u * t ≠ 1 := by
    intro u hcon
    have hsu : Real.sin u = 1 / t := by
      rw [eq_comm, div_eq_iff ht1.ne']
      exact hcon.symm
    have h3 : Real.sin u ≤ 1 := (hsinb u).2
    rw [hsu, div_le_iff₀ ht1] at h3
    linarith
  have hne2 : ∀ u : ℝ, Real.sin u * t ≠ -1 := by
    intro u hcon
    have hsu : Real.sin u = -1 / t := by
      rw [eq_comm, div_eq_iff ht1.ne']
      exact hcon.symm
    have h3 : -1 ≤ Real.sin u := (hsinb u).1
    rw [hsu, le_div_iff₀ ht1] at h3
    linarith
  have hBpos : ∀ u : ℝ, 0 < Real.sqrt (1 - (Real.sin u * t) ^ 2) := by
    intro u
    have h1 : |Real.sin u * t| ≤ t := by
      have h2 : |Real.sin u * t| = |Real.sin u| * |t| := by rw [abs_mul]
      rw [h2, abs_of_pos ht1]
      exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one u) (le_of_lt ht1)).trans
        (by rw [one_mul])
    have h2 : (Real.sin u * t) ^ 2 < 1 := by
      rw [← sq_abs (Real.sin u * t)]
      calc |Real.sin u * t| ^ 2 ≤ t ^ 2 := by
            nlinarith [h1, abs_nonneg (Real.sin u * t), ht2]
        _ < 1 := by nlinarith [h1, ht2]
    exact Real.sqrt_pos.mpr (by linarith)
  have hFderiv : ∀ u : ℝ, HasDerivAt (fun w => asn (Real.sin w * t))
      (t * Real.cos u / Real.sqrt (1 - (Real.sin u * t) ^ 2)) u := by
    intro u
    have hcomp : HasDerivAt (fun w => Real.sin w * t) (Real.cos u * t) u :=
      (Real.hasDerivAt_sin u).mul_const t
    have h2 := (Real.hasDerivAt_arcsin (hne2 u) (hne1 u)).comp u hcomp
    have hrw : (1 / Real.sqrt (1 - (Real.sin u * t) ^ 2)) * (Real.cos u * t)
        = t * Real.cos u / Real.sqrt (1 - (Real.sin u * t) ^ 2) := by
      field_simp
    rw [hrw] at h2
    exact h2
  have hsinnonneg : ∀ u : ℝ, 0 < u → u < Real.pi → 0 ≤ Real.sin u :=
    fun u h1 h2 => Real.sin_nonneg_of_nonneg_of_le_pi h1.le h2.le
  have hcosnonneg : ∀ u : ℝ, 0 < u → u ≤ Real.pi / 2 → 0 ≤ Real.cos u := by
    intro u hu1 hu2
    rcases lt_or_eq_of_le hu2 with h | h
    · have hb := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨hu1.le, le_trans hu2
        (by linarith [Real.pi_pos])⟩)
        (Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos.le], by linarith [Real.pi_pos]⟩) h
      rw [Real.cos_pi_div_two] at hb
      exact hb.le
    · rw [h, Real.cos_pi_div_two]
  have hcosnonpos : ∀ u : ℝ, Real.pi / 2 ≤ u → u < Real.pi → Real.cos u ≤ 0 := by
    intro u hu1 hu2
    rcases lt_or_eq_of_le hu1 with h | h
    · have hb := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨by linarith [Real.pi_pos.le],
        le_trans hu1 hu2.le⟩)
        (Set.mem_Icc.mpr ⟨by linarith [hu1], hu2.le⟩) h
      rw [Real.cos_pi_div_two] at hb
      exact le_of_lt hb
    · rw [← h, Real.cos_pi_div_two]
  have hsqle : ∀ w : ℝ, (Real.sin w * t) ^ 2 < 1 := by
    intro w
    have h1 : |Real.sin w * t| ≤ t := by
      have h2 : |Real.sin w * t| = |Real.sin w| * |t| := by rw [abs_mul]
      rw [h2, abs_of_pos ht1]
      exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one w) (le_of_lt ht1)).trans (by rw [one_mul])
    rw [← sq_abs (Real.sin w * t)]
    nlinarith [h1, ht2, abs_nonneg (Real.sin w * t)]
  have hanti : AntitoneOn (deriv (fun w => asn (Real.sin w * t))) (Set.Ioo 0 Real.pi) := by
    intro u hu v hv huv
    rw [HasDerivAt.deriv (hFderiv u), HasDerivAt.deriv (hFderiv v)]
    have hBu : 0 < Real.sqrt (1 - (Real.sin u * t) ^ 2) := hBpos u
    have hBv : 0 < Real.sqrt (1 - (Real.sin v * t) ^ 2) := hBpos v
    rw [div_le_div_iff₀ hBv hBu, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ ht1.le
    -- goal : cos v * Bu ≤ cos u * Bv
    have hsu0 : 0 ≤ Real.sin u := hsinnonneg u hu.1 hu.2
    have hsv0 : 0 ≤ Real.sin v := hsinnonneg v hv.1 hv.2
    have hsq1 : Real.sqrt (1 - (Real.sin v * t) ^ 2) ^ 2 = 1 - (Real.sin v * t) ^ 2 :=
      Real.sq_sqrt (by linarith [hsqle v])
    have hsq2 : Real.sqrt (1 - (Real.sin u * t) ^ 2) ^ 2 = 1 - (Real.sin u * t) ^ 2 :=
      Real.sq_sqrt (by linarith [hsqle u])
    have ecu : Real.cos u ^ 2 = 1 - Real.sin u ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq u]
    have ecv : Real.cos v ^ 2 = 1 - Real.sin v ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq v]
    have h2 : (0:ℝ) ≤ 1 - t ^ 2 := by nlinarith [ht2]
    have hX2 : (Real.cos u * Real.sqrt (1 - (Real.sin v * t) ^ 2)) ^ 2
        = Real.cos u ^ 2 * (1 - (Real.sin v * t) ^ 2) := by
      rw [mul_pow, hsq1]
    have hY2 : (Real.cos v * Real.sqrt (1 - (Real.sin u * t) ^ 2)) ^ 2
        = Real.cos v ^ 2 * (1 - (Real.sin u * t) ^ 2) := by
      rw [mul_pow, hsq2]
    rcases le_or_gt v (Real.pi / 2) with hvle | hvgt
    · -- both arguments in (0, π/2]
      have hcu0 : 0 ≤ Real.cos u := hcosnonneg u hu.1 (le_trans huv hvle)
      have hcv0 : 0 ≤ Real.cos v := hcosnonneg v hv.1 hvle
      have hsineq : Real.sin u ≤ Real.sin v := by
        rcases lt_or_eq_of_le huv with h | h
        · exact le_of_lt (Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := u)
            (by linarith [hu.1, Real.pi_pos]) hvle h)
        · exact h ▸ le_refl _
      have hsq' : (Real.sin u) ^ 2 ≤ (Real.sin v) ^ 2 := by
        nlinarith [hsu0, hsv0, hsineq, sq_nonneg (Real.sin u), sq_nonneg (Real.sin v)]
      have hY2X2 : (Real.cos v * Real.sqrt (1 - (Real.sin u * t) ^ 2)) ^ 2
          ≤ (Real.cos u * Real.sqrt (1 - (Real.sin v * t) ^ 2)) ^ 2 := by
        rw [hX2, hY2, ecu, ecv, ← sub_nonneg]
        have hexp : (1 - Real.sin u ^ 2) * (1 - (Real.sin v * t) ^ 2)
            - (1 - Real.sin v ^ 2) * (1 - (Real.sin u * t) ^ 2)
            = (1 - t ^ 2) * ((Real.sin v) ^ 2 - (Real.sin u) ^ 2) := by
          ring
        rw [hexp]
        exact mul_nonneg h2 (sub_nonneg.mpr hsq')
      exact le_of_sq_le_sq hY2X2 (mul_nonneg hcu0 hBv.le)
    · -- v > π/2
      rcases le_or_gt u (Real.pi / 2) with hucase | hucase
      · -- mixed: cos u ≥ 0 ≥ cos v
        have hcu0 : 0 ≤ Real.cos u := hcosnonneg u hu.1 hucase
        have hcv0 : Real.cos v ≤ 0 := hcosnonpos v hvgt.le hv.2
        have hX0 : 0 ≤ Real.cos u * Real.sqrt (1 - (Real.sin v * t) ^ 2) :=
          mul_nonneg hcu0 hBv.le
        have hY0 : Real.cos v * Real.sqrt (1 - (Real.sin u * t) ^ 2) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hcv0 hBu.le
        linarith
      · -- both in [π/2, π): mirror of the first case
        have hcu0 : Real.cos u ≤ 0 := hcosnonpos u hucase.le hu.2
        have hcv0 : Real.cos v ≤ 0 := hcosnonpos v (hucase.le.trans huv) hv.2
        have hsineq : Real.sin v ≤ Real.sin u := by
          rcases lt_or_eq_of_le huv with h | h
          · have h1 : Real.sin (Real.pi - v) ≤ Real.sin (Real.pi - u) :=
              le_of_lt (Real.sin_lt_sin_of_lt_of_le_pi_div_two
                (le_trans (by linarith [Real.pi_pos])
                  (sub_nonneg.mpr (by linarith [hv.2])))
                (by linarith [hucase.le]) (by linarith [h]))
            rwa [Real.sin_pi_sub, Real.sin_pi_sub] at h1
          · exact h ▸ le_refl _
        have hsq' : (Real.sin v) ^ 2 ≤ (Real.sin u) ^ 2 := by
          nlinarith [hsu0, hsv0, hsineq, sq_nonneg (Real.sin u), sq_nonneg (Real.sin v)]
        have hX2Y2 : (Real.cos u * Real.sqrt (1 - (Real.sin v * t) ^ 2)) ^ 2
            ≤ (Real.cos v * Real.sqrt (1 - (Real.sin u * t) ^ 2)) ^ 2 := by
          rw [hX2, hY2, ecu, ecv, ← sub_nonneg]
          have hexp : (1 - Real.sin v ^ 2) * (1 - (Real.sin u * t) ^ 2)
              - (1 - Real.sin u ^ 2) * (1 - (Real.sin v * t) ^ 2)
              = (1 - t ^ 2) * ((Real.sin u) ^ 2 - (Real.sin v) ^ 2) := by
            ring
          rw [hexp]
          nlinarith [h2, hsq', hsu0, hsv0]
        have hYneg : 0 ≤ -(Real.cos v * Real.sqrt (1 - (Real.sin u * t) ^ 2)) := by
          rw [neg_nonneg]
          nlinarith [hcv0, hBu.le]
        have hXneg : 0 ≤ -(Real.cos u * Real.sqrt (1 - (Real.sin v * t) ^ 2)) := by
          rw [neg_nonneg]
          nlinarith [hcu0, hBv.le]
        have hfin := le_of_sq_le_sq
          (a := -(Real.cos u * Real.sqrt (1 - (Real.sin v * t) ^ 2)))
          (b := -(Real.cos v * Real.sqrt (1 - (Real.sin u * t) ^ 2)))
          (by have h1 : (-(Real.cos u * Real.sqrt (1 - (Real.sin v * t) ^ 2))) ^ 2
                = (Real.cos u * Real.sqrt (1 - (Real.sin v * t) ^ 2)) ^ 2 := neg_sq _
              have h2 : (-(Real.cos v * Real.sqrt (1 - (Real.sin u * t) ^ 2))) ^ 2
                = (Real.cos v * Real.sqrt (1 - (Real.sin u * t) ^ 2)) ^ 2 := neg_sq _
              rw [h1, h2]; exact hX2Y2) hYneg
        linarith
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc 0 Real.pi) ?_ ?_
    (by rw [interior_Icc]; exact hanti)
  · exact (Real.continuous_arcsin.comp (Real.continuous_sin.mul_const t)).continuousOn
  · intro z hz
    rw [interior_Icc] at hz
    exact (hFderiv z).differentiableAt.differentiableWithinAt

/-- HOL `convex_sum_corollary` (counting_spheres.hl:4276). Filled via the
concavity of `u ↦ asn (sin u * t)` and Jensen's inequality with uniform
weights `1/n`. -/
theorem convex_sum_corollary (n : ℕ) (t : ℝ) (bet : ℕ → ℝ) (hn : 0 < n)
    (ht : 0 < t ∧ t < 1) (hsum : ∑ i ∈ Finset.Icc 1 n, bet i = Real.pi)
    (hb : ∀ i : ℕ, i ∈ Finset.Icc 1 n → 0 ≤ bet i ∧ bet i ≤ Real.pi) :
    Real.pi - n * asn (Real.sin (Real.pi / n) * t) ≤
      ∑ i ∈ Finset.Icc 1 n, (bet i - asn (Real.sin (bet i) * t)) := by
  have hcc := p22_arcsin_sin_concave ht.1 ht.2
  have hw1 : ∑ i ∈ Finset.Icc 1 n, (1 / n : ℝ) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    field_simp
  have hmem : ∀ i ∈ Finset.Icc 1 n, bet i ∈ Set.Icc 0 Real.pi := fun i hi =>
    Set.mem_Icc.mpr ⟨(hb i hi).1, (hb i hi).2⟩
  have hj := ConcaveOn.le_map_sum (𝕜 := ℝ) (β := ℝ) (s := Set.Icc 0 Real.pi)
    (f := fun u => asn (Real.sin u * t)) (t := Finset.Icc 1 n) (w := fun _ => 1 / n)
    (p := bet) hcc (fun i _ => by positivity) hw1 hmem
  simp only [smul_eq_mul] at hj
  have hsumw : ∑ i ∈ Finset.Icc 1 n, (1 / n : ℝ) * bet i = Real.pi / n := by
    rw [← Finset.mul_sum, hsum]
    field_simp
  rw [hsumw] at hj
  have hn' : (0:ℝ) ≤ n := by exact_mod_cast hn.le
  have hlhs : ∑ i ∈ Finset.Icc 1 n, asn (Real.sin (bet i) * t)
      ≤ n * asn (Real.sin (Real.pi / n) * t) := by
    have h1 := mul_le_mul_of_nonneg_left hj hn'
    rw [Finset.mul_sum] at h1
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans h1
    have hni : ((n:ℝ) * ((1:ℝ) / n)) = 1 := by field_simp
    rw [← mul_assoc, hni, one_mul]
  have hrhs : ∑ i ∈ Finset.Icc 1 n, (bet i - asn (Real.sin (bet i) * t))
      = Real.pi - ∑ i ∈ Finset.Icc 1 n, asn (Real.sin (bet i) * t) := by
    rw [Finset.sum_sub_distrib, hsum]
  rw [hrhs]
  linarith [hlhs]

/-- HOL `SOL_SUBSET` (counting_spheres.hl:4305). Filled from `sol_spec` and
monotonicity of real-valued measure. -/
theorem SOL_SUBSET (x : V3) (s t : Set V3) (r : ℝ) (hr : 0 < r)
    (hms : MeasurableSet (s ∩ normballP22 x r)) (hmt : MeasurableSet (t ∩ normballP22 x r))
    (hsub : s ⊆ t) (hrs : radialNorm r x (s ∩ normballP22 x r))
    (hrt : radialNorm r x (t ∩ normballP22 x r)) : sol x s ≤ sol x t := by
  rw [sol_spec hr hms hrs, sol_spec hr hmt hrt]
  refine (div_le_div_iff₀ (b := r ^ 3) (d := r ^ 3) (by positivity) (by positivity)).mpr ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 3)
  exact MeasureTheory.measureReal_mono (Set.inter_subset_inter hsub Subset.rfl)
    (ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_right)
      (MeasureTheory.measure_ball_lt_top (μ := MeasureTheory.volume) (x := x) (r := r))))

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

/-- `arcV 0 p v` is Mathlib's vector angle `InnerProductGeometry.angle p v`. -/
private theorem p22_arcV_eq_angle (p v : V3) :
    arcV 0 p v = InnerProductGeometry.angle p v := by
  rw [arcV, InnerProductGeometry.angle, dist_zero_right, dist_zero_right]
  congr 1
  rw [← inner_eq_dot]
  simp

/-- Cosine of `arcV 0 p v` is the normalized dot product. -/
private theorem p22_cos_arcV (p v : V3) (hp : p ≠ 0) (hv : v ≠ 0) :
    Real.cos (arcV 0 p v) = (p ⬝ᵥ v) / (‖p‖ * ‖v‖) := by
  rw [p22_arcV_eq_angle, InnerProductGeometry.cos_angle, inner_eq_dot]

/-- Members of `[0, π]` for `arcV 0 p v` (any `p v`, degenerate included). -/
private theorem p22_arcV_mem_Icc (p v : V3) : arcV 0 p v ∈ Set.Icc (0:ℝ) Real.pi :=
  Set.mem_Icc.mpr ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- HOL `rcone_gt_arcV` (counting_spheres.hl:4618). Filled: the rcone
inequality is `cos g < cos (arcV 0 p v)` after Cauchy–Schwarz normalization,
and `cos` is strictly antitone on `[0, π]`. -/
theorem rcone_gt_arcV (v p : V3) (g : ℝ) (hg1 : 0 < g) (hg2 : g < Real.pi / 2)
    (hp : p ∈ rconeGt 0 v (Real.cos g)) : arcV 0 p v < g := by
  have hc : 0 < Real.cos g := (cos_bounds_0_Pi2 g hg1 hg2).1
  obtain ⟨hp0, hv0⟩ := rcone_nz v p (Real.cos g) hc hp
  rw [rcone_def_alt] at hp
  have hnn : (0:ℝ) < ‖p‖ * ‖v‖ := mul_pos (norm_pos_iff.mpr hp0) (norm_pos_iff.mpr hv0)
  have hp' : Real.cos g < Real.cos (arcV 0 p v) := by
    rw [p22_cos_arcV p v hp0 hv0, lt_div_iff₀ hnn, mul_comm]
    exact hp
  have hgle : g ∈ Set.Icc (0:ℝ) Real.pi :=
    Set.mem_Icc.mpr ⟨hg1.le, by linarith [Real.pi_pos]⟩
  refine lt_of_le_of_ne
    ((Real.strictAntiOn_cos.le_iff_ge hgle (p22_arcV_mem_Icc p v)).mp (le_of_lt hp')) ?_
  intro hcon
  rw [hcon] at hp'
  exact lt_irrefl (Real.cos g) hp'

/-- HOL `rcone_gt_arc_triangle` (counting_spheres.hl:4685). Filled: the
angle triangle inequality (`InnerProductGeometry.angle_le_angle_add_angle`)
plus `rcone_gt_arcV` give `arcV 0 v w < gv + gw`, contradicting `h3`. -/
theorem rcone_gt_arc_triangle (p v w : V3) (gv gw : ℝ) (hw : w ≠ 0)
    (h1 : 0 < gv) (h2 : gv < Real.pi / 2) (hp : p ∈ rconeGt 0 v (Real.cos gv))
    (h3 : gv + gw ≤ arcV 0 v w) : gw < arcV 0 p w := by
  by_contra hcon
  push_neg at hcon
  have hc : arcV 0 p v < gv := rcone_gt_arcV v p gv h1 h2 hp
  have hvp : arcV 0 v p = arcV 0 p v := by
    rw [p22_arcV_eq_angle v p, p22_arcV_eq_angle p v, InnerProductGeometry.angle_comm]
  have htri : arcV 0 v w ≤ arcV 0 v p + arcV 0 p w := by
    rw [p22_arcV_eq_angle v w, p22_arcV_eq_angle v p, p22_arcV_eq_angle p w]
    exact InnerProductGeometry.angle_le_angle_add_angle v p w
  have hlt : arcV 0 v p < gv := by rw [hvp]; exact hc
  have h6 : arcV 0 v p + arcV 0 p w < arcV 0 v p + gw := by linarith
  have h7 : arcV 0 v p + gw < gv + gw := by linarith
  have hfinal : arcV 0 v w < arcV 0 v w := by linarith
  exact absurd hfinal (lt_irrefl _)

/-- HOL `rcone_gt_facet` (counting_spheres.hl:4710). Filled: `q` is the
positive multiple of `p` of norm `cos gv / cos (arcV 0 p v) < 1`; combining
`rcone_gt_arc_triangle` (angle) with the strict antitonicity of `cos` on
`[0, π]` bounds `p ⬝ᵥ w`, and rescaling gives the claim. -/
theorem rcone_gt_facet (gv gw : ℝ) (v w q p : V3) (h1 : 0 < gv ∧ gv < Real.pi / 2)
    (h2 : 0 < gw ∧ gw < Real.pi / 2) (hw : w ≠ 0)
    (hp : p ∈ rconeGt 0 v (Real.cos gv))
    (hq : q = ((‖v‖ * Real.cos gv) / (p ⬝ᵥ v)) • p)
    (h4 : gv + gw ≤ arcV 0 v w) : q ⬝ᵥ w < ‖w‖ * Real.cos gw := by
  have hcgv : 0 < Real.cos gv := (cos_bounds_0_Pi2 gv h1.1 h1.2).1
  have hcgw : 0 < Real.cos gw := (cos_bounds_0_Pi2 gw h2.1 h2.2).1
  have hpp : 0 < p ⬝ᵥ v := rcone_dot_pos v (Real.cos gv) p hcgv hp
  obtain ⟨hp0, hv0⟩ := rcone_nz v p (Real.cos gv) hcgv hp
  have hnp : (0:ℝ) < ‖p‖ := norm_pos_iff.mpr hp0
  have hnv : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  have hnn : (0:ℝ) < ‖p‖ * ‖v‖ := mul_pos hnp hnv
  have hcosarc : Real.cos (arcV 0 p v) = (p ⬝ᵥ v) / (‖p‖ * ‖v‖) :=
    p22_cos_arcV p v hp0 hv0
  have hpv : p ⬝ᵥ v = ‖p‖ * ‖v‖ * Real.cos (arcV 0 p v) := by rw [hcosarc]; field_simp
  have harcv : arcV 0 p v < gv := rcone_gt_arcV v p gv h1.1 h1.2 hp
  have hmem_gv : gv ∈ Set.Icc (0:ℝ) Real.pi :=
    Set.mem_Icc.mpr ⟨h1.1.le, by linarith [Real.pi_pos]⟩
  have hcoslt : Real.cos gv < Real.cos (arcV 0 p v) :=
    Real.strictAntiOn_cos (p22_arcV_mem_Icc p v) hmem_gv harcv
  have hqlt : ‖q‖ < 1 := by
    have hcp : 0 < (‖v‖ * Real.cos gv) / (p ⬝ᵥ v) :=
      div_pos (mul_pos hnv hcgv) hpp
    rw [hq, norm_smul, Real.norm_eq_abs, abs_of_pos hcp, div_mul_eq_mul_div,
      div_lt_iff₀ hpp, one_mul, hpv]
    calc ‖v‖ * Real.cos gv * ‖p‖ = ‖p‖ * ‖v‖ * Real.cos gv := by ring
      _ < ‖p‖ * ‖v‖ * Real.cos (arcV 0 p v) :=
          mul_lt_mul_of_pos_left hcoslt hnn
  -- the angle to w is > gw, so the normalized dot with w is < cos gw
  have harc : gw < arcV 0 p w := rcone_gt_arc_triangle p v w gv gw hw h1.1 h1.2 hp h4
  have hmem_gw : gw ∈ Set.Icc (0:ℝ) Real.pi :=
    Set.mem_Icc.mpr ⟨h2.1.le, by linarith [Real.pi_pos]⟩
  have hcosltw : Real.cos (arcV 0 p w) < Real.cos gw :=
    Real.strictAntiOn_cos hmem_gw (p22_arcV_mem_Icc p w) harc
  have hnpw : (0:ℝ) < ‖p‖ * ‖w‖ := mul_pos hnp (norm_pos_iff.mpr hw)
  have hpw : p ⬝ᵥ w < ‖p‖ * ‖w‖ * Real.cos gw := by
    rw [p22_cos_arcV p w hp0 hw, div_lt_iff₀ hnpw] at hcosltw
    linarith [show Real.cos gw * (‖p‖ * ‖w‖) = ‖p‖ * ‖w‖ * Real.cos gw from by ring]
  have hfin : q ⬝ᵥ w < ‖q‖ * (‖w‖ * Real.cos gw) := by
    have hcp : 0 < (‖v‖ * Real.cos gv) / (p ⬝ᵥ v) := div_pos (mul_pos hnv hcgv) hpp
    have hqn : ‖q‖ = ((‖v‖ * Real.cos gv) / (p ⬝ᵥ v)) * ‖p‖ := by
      rw [hq, norm_smul, Real.norm_eq_abs, abs_of_pos hcp]
    have hsub : ((‖v‖ * Real.cos gv) / (p ⬝ᵥ v)) * (p ⬝ᵥ w)
        < ((‖v‖ * Real.cos gv) / (p ⬝ᵥ v)) * (‖p‖ * ‖w‖ * Real.cos gw) :=
      mul_lt_mul_of_pos_left hpw hcp
    have hstep : ((‖v‖ * Real.cos gv) / (p ⬝ᵥ v)) * (‖p‖ * ‖w‖ * Real.cos gw)
        = ‖q‖ * (‖w‖ * Real.cos gw) := by
      rw [hqn]; ring
    have hqvw : q ⬝ᵥ w = ((‖v‖ * Real.cos gv) / (p ⬝ᵥ v)) * (p ⬝ᵥ w) := by
      rw [hq, dotV_smul_left]
    calc q ⬝ᵥ w = ((‖v‖ * Real.cos gv) / (p ⬝ᵥ v)) * (p ⬝ᵥ w) := hqvw
      _ < ((‖v‖ * Real.cos gv) / (p ⬝ᵥ v)) * (‖p‖ * ‖w‖ * Real.cos gw) := hsub
      _ = ‖q‖ * (‖w‖ * Real.cos gw) := hstep
  calc q ⬝ᵥ w < ‖q‖ * (‖w‖ * Real.cos gw) := hfin
    _ ≤ 1 * (‖w‖ * Real.cos gw) :=
        mul_le_mul_of_nonneg_right (le_of_lt hqlt)
          (le_of_lt (mul_pos (norm_pos_iff.mpr hw) hcgw))
    _ = ‖w‖ * Real.cos gw := one_mul _

/-- HOL `BIJ_SYM` (counting_spheres.hl:4784), restated with `[Nonempty a]`:
in HOL every type is inhabited so a function `b → a` always exists; in Lean it
does not when `a` is empty (e.g. `a = Empty`, `b = Unit`, `A = ∅`, `B = univ`
satisfies the hypothesis), so the side condition is required.  Filled via the
`invFunOn` inverse bijection. -/
theorem BIJ_SYM {a : Type*} {b : Type*} [Nonempty a] (A : Set a) (B : Set b)
    (h : ∃ f : a → b, Set.BijOn f A B) : ∃ g : b → a, Set.BijOn g B A := by
  obtain ⟨f, hf⟩ := h
  exact ⟨Function.invFunOn f A, hf.symm hf.invOn_invFunOn.symm⟩

/-- HOL `BIJ_TRANS` (counting_spheres.hl:4793). -/
theorem BIJ_TRANS {a b c : Type*} (A : Set a) (B : Set b) (C : Set c)
    (h1 : ∃ f : a → b, Set.BijOn f A B) (h2 : ∃ g : b → c, Set.BijOn g B C) :
    ∃ h : a → c, Set.BijOn h A C := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  exact ⟨g ∘ f, Set.BijOn.comp hg hf⟩

/-- HOL `PREIMAGE_BIJ` (counting_spheres.hl:4802), restated faithfully with
`[Nonempty b]`: HOL's `preimage A f {c}` is `{x ∈ A | f x = c}`, whereas the
original port dropped the `A`/`B` restrictions in `h3`, which breaks the
theorem (take `a = Unit`, `b = c = ℕ`, `A = ∅`, `B = C = {0}`,
`f = g = const 0`: the hypotheses hold but no bijection `∅ → {0}` is onto).
The `Nonempty b` side condition is needed because the total map `a → b` of the
conclusion need not exist otherwise (`a = Unit`, `b = Empty`, `A = B = C = ∅`).
Filled by the HOL choice argument `q a := p_{f a} a`. -/
theorem PREIMAGE_BIJ {a b c : Type*} [Nonempty b] (A : Set a) (B : Set b) (C : Set c)
    (f : a → c) (g : b → c)
    (h1 : ∀ x : a, x ∈ A → f x ∈ C) (h2 : ∀ y : b, y ∈ B → g y ∈ C)
    (h3 : ∀ z : c, z ∈ C → ∃ p, Set.BijOn p {x : a | x ∈ A ∧ f x = z}
      {y : b | y ∈ B ∧ g y = z}) :
    ∃ q, Set.BijOn q A B := by
  classical
  -- totalize the choice: for `z ∉ C` take an arbitrary map (never used below)
  have ht : ∀ z : c, ∃ p : a → b,
      (z ∈ C → Set.BijOn p {x : a | x ∈ A ∧ f x = z} {y : b | y ∈ B ∧ g y = z}) := by
    intro z
    by_cases hz : z ∈ C
    · obtain ⟨p, hp⟩ := h3 z hz
      exact ⟨p, fun _ => hp⟩
    · exact ⟨fun _ => Classical.choice ‹Nonempty b›, fun hz' => absurd hz' hz⟩
  choose pp hpp using ht
  refine ⟨fun x => pp (f x) x, ?_⟩
  have hmem : ∀ x : a, x ∈ A → pp (f x) x ∈ B ∧ g (pp (f x) x) = f x := by
    intro x hx
    show pp (f x) x ∈ {y : b | y ∈ B ∧ g y = f x}
    exact (hpp (f x) (h1 x hx)).mapsTo ⟨hx, rfl⟩
  refine ⟨fun x hx => (hmem x hx).1, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    simp only [] at heq
    have hg₁ := (hmem x₁ hx₁).2
    have hg₂ := (hmem x₂ hx₂).2
    have hf12 : f x₁ = f x₂ := by rw [← hg₁, ← hg₂, heq]
    have hp12 : pp (f x₁) = pp (f x₂) := by rw [hf12]
    rw [← hp12] at heq
    exact (hpp (f x₁) (h1 x₁ hx₁)).injOn ⟨hx₁, rfl⟩ ⟨hx₂, hf12.symm⟩ heq
  · intro y hy
    obtain ⟨x, hxmem, hex⟩ := (hpp (g y) (h2 y hy)).surjOn ⟨hy, rfl⟩
    refine ⟨x, hxmem.1, ?_⟩
    show pp (f x) x = y
    rw [hxmem.2]
    exact hex

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

/-- HOL `POLYHEDRON_D1_D` (counting_spheres.hl:4855). Both sides are the empty
dart set under the `hypermap1OfFanxP22`/`d1FanP22` stub encoding. -/
theorem POLYHEDRON_D1_D (p : Set V3) (hb : Bornology.IsBounded p) (hp : polyhedron p)
    (hi : (0 : V3) ∈ interior p) :
    dFanP22 0 (verticesP22 p) (edgesP22 p) = d1FanP22 0 (verticesP22 p) (edgesP22 p) := by
  simp [dFanP22, d1FanP22, hypermap1OfFanxP22]

/-- HOL `POLYHEDRON_PLAIN` (counting_spheres.hl:4866). The stub hypermap has
identity edge map, hence is plain. -/
theorem POLYHEDRON_PLAIN (p : Set V3) (hb : Bornology.IsBounded p) (hp : polyhedron p)
    (hi : (0 : V3) ∈ interior p) :
    (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).Plain := by
  simp only [hypermap1OfFanxP22, Hypermap.Plain]
  exact Equiv.Perm.ext fun _ => rfl

/-- HOL `POLYHEDRON_NODE_3` (counting_spheres.hl:4905). Vacuous: the stub dart
set is empty. -/
theorem POLYHEDRON_NODE_3 (p : Set V3) (x : Dart3) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
    (hx : x ∈ dFanP22 0 (verticesP22 p) (edgesP22 p)) :
    3 ≤ ((hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).node x).ncard := by
  simp [dFanP22, hypermap1OfFanxP22] at hx

/-- HOL `POLYHEDRON_TGJISOK` (counting_spheres.hl:4955). The stub dart set is
empty, so the (truncated) `ℕ` inequality holds trivially. -/
theorem POLYHEDRON_TGJISOK (p : Set V3) (hb : Bornology.IsBounded p)
    (hp : polyhedron p) (hi : (0 : V3) ∈ interior p) :
    (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).darts.card ≤
      6 * (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).numberOfFaces - 12 := by
  simp only [hypermap1OfFanxP22]
  exact Nat.zero_le _

/-- HOL `EDGE_PAIR_pr23` (counting_spheres.hl:5003). GIANT. -/
theorem EDGE_PAIR_pr23 (x : V3) (V : Set V3) (E : Set (Set V3)) (d d' : Dart3)
    (h : eFanP22 x V E d = d') : pr2 d = pr3 d' ∧ pr3 d = pr2 d' := by
  sorry

/-- HOL `EDGE_pr23` (counting_spheres.hl:5020). Vacuous: the stub `d1FanP22`
is empty. -/
theorem EDGE_pr23 (x : V3) (V : Set V3) (E : Set (Set V3)) (y y1 : Dart3)
    (hfan : Fan.FAN x V E)
    (hcard : ∀ v ∈ V, (setOfEdgeP22 v V E).ncard > 1)
    (hy : y ∈ d1FanP22 x V E) (hy1 : y1 ∈ d1FanP22 x V E)
    (hpr : ({pr2 y, pr3 y} : Set V3) = {pr2 y1, pr3 y1}) (hne : y ≠ y1) :
    (hypermap1OfFanxP22 x V E).edgeMap y1 = y := by
  simp [d1FanP22] at hy

/-- HOL `SIMPLE_FACE_EDGE_INJ` (counting_spheres.hl:5066). GIANT. -/
theorem SIMPLE_FACE_EDGE_INJ {α : Type*} [DecidableEq α] (H : Hypermap α) (y y1 : α)
    (hs : H.Simple) (hnode : 1 < (H.node (H.faceMap y)).ncard)
    (hy : y ∈ H.darts) (hfy : y ∈ H.face y1) : y ≠ H.edgeMap y1 := by
  intro h
  have hNF : H.nodeMap (H.faceMap y) = y1 := by
    rw [h]
    have h1 := H.nodeMap_mul_faceMap
    have key := congrArg (fun p : Equiv.Perm α => p (H.edgeMap y1)) h1
    rw [Equiv.Perm.mul_apply] at key
    simp at key
    exact key
  have hface1 : H.face (H.faceMap y) = H.face y :=
    orbitMap_eq_of_mem H.faceMap_permutes
      (pow_apply_mem_orbitMap H.faceMap 1 y)
  have hface2 : H.face y = H.face y1 :=
    orbitMap_eq_of_mem H.faceMap_permutes hfy
  have h2 : y1 ∈ H.node (H.faceMap y) ∩ H.face (H.faceMap y) := by
    refine ⟨⟨1, ?_⟩, ?_⟩
    · rw [pow_one]; exact hNF
    · rw [hface1, hface2]; exact H.mem_face_self y1
  rw [Hypermap.Simple.apply H hs (H.faceMap y)] at h2
  have hy1F : y1 = H.faceMap y := Set.mem_singleton_iff.mp h2
  have hfix : H.nodeMap (H.faceMap y) = H.faceMap y := by rw [hNF, hy1F]
  have hsingle : H.node (H.faceMap y) = {H.faceMap y} :=
    orbitMap_eq_singleton hfix
  rw [hsingle, Set.ncard_singleton] at hnode
  norm_num at hnode

/-- Under the `hypermap1OfFanxP22` stub (empty dart set) the face set is
empty. -/
private theorem p22_faceSet_stub (x : V3) (V : Set V3) (E : Set (Set V3)) :
    (hypermap1OfFanxP22 x V E).faceSet = (∅ : Set (Set Dart3)) := by
  simp [hypermap1OfFanxP22, Hypermap.faceSet, setOfOrbits]

/-- HOL `INJ_EDGES_FACE_pr23` (counting_spheres.hl:5119).  Vacuous: the stub
`faceSet` is empty, so the face-membership hypothesis is contradictory. -/
theorem INJ_EDGES_FACE_pr23 (p : Set V3) (f : Set Dart3) (y1 y : Dart3)
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
    (hf : f ∈ (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).faceSet)
    (hy : y ∈ f) (hy1 : y1 ∈ f)
    (hpr : ({pr2 y, pr3 y} : Set V3) = {pr2 y1, pr3 y1}) : y = y1 := by
  rw [p22_faceSet_stub] at hf
  exact absurd hf (Set.notMem_empty f)

/-- HOL `BIJ_EDGES_DART_FACE` (counting_spheres.hl:5178).  Vacuous: the stub
`faceSet` is empty, so the face-membership hypothesis is contradictory. -/
theorem BIJ_EDGES_DART_FACE (p : Set V3) (f : Set Dart3) (f1 : Set V3)
    (hb : Bornology.IsBounded p) (hp : polyhedron p) (hi : (0 : V3) ∈ interior p)
    (hf : f ∈ (hypermap1OfFanxP22 0 (verticesP22 p) (edgesP22 p)).faceSet)
    (hf1 : FacetOf f1 p)
    (hlead : fchanged f1 =
      dartsetLeadsIntoFanP22 0 (verticesP22 p) (edgesP22 p) f) :
    ∃ b, Set.BijOn b (edges f1) f := by
  rw [p22_faceSet_stub] at hf
  exact absurd hf (Set.notMem_empty f)

/-- HOL `SEGMENT_EDGE_ONTO` (counting_spheres.hl:5206). GIANT. -/
theorem SEGMENT_EDGE_ONTO (p : Set V3) (e : Set V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (he : edgeOf e p) :
    ∃ v w : V3, e = segment ℝ v w := by
  sorry

/-- HOL `EDGE_OF_FACET_OF` (counting_spheres.hl:5217). GIANT. -/
theorem EDGE_OF_FACET_OF (p c e : Set V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p) (hc : FacetOf c p) :
    edgeOf e c ↔ FacetOf e c := by
  have hdc : affDim c = 2 := FACET_AFF_DIM_2 p c hp hi hc
  constructor
  · rintro ⟨hface, hdim⟩
    have hne : e ≠ ∅ := by
      intro he
      rw [he, affDim] at hdim
      simpa using hdim
    refine ⟨hface, hne, ?_⟩
    rw [hdc]
    linarith
  · rintro ⟨hface, hne, hdim⟩
    rw [hdc] at hdim
    exact ⟨hface, hdim⟩

/-- HOL `EDGE_OF_FACET_EDGE` (counting_spheres.hl:5238). GIANT. -/
theorem EDGE_OF_FACET_EDGE (p c e : Set V3) (hp : polyhedron p)
    (hb : Bornology.IsBounded p) (hi : (0 : V3) ∈ interior p) (hc : FacetOf c p)
    (he : FacetOf e c) : edgeOf e p := by
  have hdc : affDim c = 2 := FACET_AFF_DIM_2 p c hp hi hc
  refine ⟨FaceOf.trans he.1 hc.1, ?_⟩
  rw [he.2.2, hdc]
  norm_num

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
  refine ⟨fun f hf => FINITE_POLYHEDRON_FACETS (FACE_OF_POLYHEDRON_POLYHEDRON hp hf.1),
    FINITE_POLYHEDRON_FACETS hp, ?_⟩
  have hE' : (⋃ f ∈ ({f : Set V3 | FacetOf f P} : Set (Set V3)),
      {e : Set V3 | FacetOf e f}).Finite :=
    (FINITE_POLYHEDRON_FACETS hp).biUnion
      (fun f hf => FINITE_POLYHEDRON_FACETS (FACE_OF_POLYHEDRON_POLYHEDRON hp hf.1))
  refine Set.Finite.subset
    (Set.Finite.prod (FINITE_POLYHEDRON_FACETS hp) hE') ?_
  rintro ⟨a, b⟩ ⟨h1, h2⟩
  exact ⟨h1, Set.mem_biUnion h1 h2⟩

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
  classical
  -- the constraints other than `v0` form a finite set; scale `p` by a factor
  -- strictly between 1 and every constraint ratio `w.2 / (w.1 ⬝ p)`.
  have hv02 : 0 < v0.2 := hpos v0 hv0V
  by_cases hQe : (V \ {v0}) = ∅
  · refine ⟨2, ?_, ?_⟩
    · rw [dotV_smul_right, hv0]
      linarith
    · intro w hw hwne
      have hwQ : w ∈ (V \ {v0}) := ⟨hw, hwne⟩
      rw [hQe] at hwQ
      exact absurd hwQ (Set.notMem_empty w)
  · have hQne : ((fun w : V3 × ℝ => (w.1 ⬝ᵥ p) / w.2) '' (V \ {v0})).Nonempty := by
      obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hQe
      exact ⟨_, Set.mem_image_of_mem _ hw⟩
    have himF : ((fun w : V3 × ℝ => (w.1 ⬝ᵥ p) / w.2) '' (V \ {v0})).Finite :=
      (hV.subset Set.diff_subset).image _
    set M : ℝ := (Finset.max' (himF.toFinset) (by simpa using hQne)) with hM
    have hMmem : M ∈ (fun w : V3 × ℝ => (w.1 ⬝ᵥ p) / w.2) '' (V \ {v0}) := by
      have := Finset.max'_mem (himF.toFinset) (by simpa using hQne)
      simpa [hM] using this
    have hMle : ∀ x ∈ (fun w : V3 × ℝ => (w.1 ⬝ᵥ p) / w.2) '' (V \ {v0}), x ≤ M := by
      intro x hx
      have hx' : x ∈ himF.toFinset := by simpa [hM] using hx
      exact Finset.le_max' _ _ hx'
    obtain ⟨w0, hw0Q, hw0r⟩ := hMmem
    have hw0Q' := (Set.mem_sdiff w0).mp hw0Q
    have hw0ne : w0 ≠ v0 := fun hcon => hw0Q'.2 (by rw [hcon]; simp)
    have hw0V : w0 ∈ V := hw0Q'.1
    have hw0pos : 0 < w0.2 := hpos w0 hw0V
    have hMlt : M < 1 := by
      rw [← hw0r, div_lt_one hw0pos]
      exact hrest w0 hw0V hw0ne
    rcases le_or_gt M 0 with hMneg | hMpos
    · -- every ratio is ≤ 0, hence every other constraint's left side is ≤ 0;
      -- the plain doubling `t := 2` already works
      refine ⟨2, ?_, ?_⟩
      · rw [dotV_smul_right, hv0]
        linarith
      · intro w hw hwne
        have hwQ : w ∈ (V \ {v0}) := ⟨hw, hwne⟩
        have hw2 : 0 < w.2 := hpos w hw
        have hupp : (w.1 ⬝ᵥ p) / w.2 ≤ M :=
          hMle _ (Set.mem_image_of_mem _ hwQ)
        have hle0 : w.1 ⬝ᵥ p ≤ 0 := by
          have h1 : (w.1 ⬝ᵥ p) / w.2 ≤ 0 := le_trans hupp hMneg
          have h2 : w.1 ⬝ᵥ p ≤ 0 * w.2 := (div_le_iff₀ hw2).mp h1
          rwa [zero_mul] at h2
        rw [dotV_smul_right]
        have h3 := hrest w hw hwne
        linarith
    · -- 0 < M < 1: the factor (1 + M⁻¹)/2 lies strictly between 1 and 1/M
      have hMne : M ≠ 0 := ne_of_gt hMpos
      have hMinv : (1:ℝ) < M⁻¹ := (one_lt_inv₀ hMpos).mpr hMlt
      have ht1 : (1:ℝ) < (1 + M⁻¹) / 2 := by linarith
      refine ⟨(1 + M⁻¹) / 2, ?_, ?_⟩
      · rw [dotV_smul_right, hv0]
        calc v0.2 = (1:ℝ) * v0.2 := by ring
          _ < ((1 + M⁻¹) / 2) * v0.2 := mul_lt_mul_of_pos_right ht1 hv02
      · intro w hw hwne
        have hwQ : w ∈ (V \ {v0}) := ⟨hw, hwne⟩
        have hw2 : 0 < w.2 := hpos w hw
        have hupp : (w.1 ⬝ᵥ p) / w.2 ≤ M :=
          hMle _ (Set.mem_image_of_mem _ hwQ)
        rw [dotV_smul_right]
        rcases le_or_gt (w.1 ⬝ᵥ p) 0 with hneg | hpos'
        · have htx : ((1 + M⁻¹) / 2) * (w.1 ⬝ᵥ p) ≤ (1:ℝ) * (w.1 ⬝ᵥ p) :=
            mul_le_mul_of_nonpos_right (le_of_lt ht1) hneg
          have h3 := hrest w hw hwne
          linarith
        · have ha : (w.1 ⬝ᵥ p) ≤ M * w.2 := (div_le_iff₀ hw2).mp hupp
          have hkey : ((1 + M⁻¹) / 2) * (w.1 ⬝ᵥ p)
              ≤ ((1 + M⁻¹) / 2) * (M * w.2) :=
            mul_le_mul_of_nonneg_left ha (by linarith)
          have hassoc : ((1 + M⁻¹) / 2) * (M * w.2)
              = ((1 + M⁻¹) / 2) * M * w.2 := (mul_assoc _ _ _).symm
          have hlt2 : ((1 + M⁻¹) / 2) * M * w.2 < w.2 := by
            have hm : ((1 + M⁻¹) / 2) * M < 1 := by
              have hMne0 : M ≠ 0 := hMne
              field_simp
              linarith
            calc ((1 + M⁻¹) / 2) * M * w.2 < (1:ℝ) * w.2 :=
                mul_lt_mul_of_pos_right hm hw2
              _ = w.2 := by ring
          rw [hassoc] at hkey
          linarith

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

/-- HOL `FACET_FINITE` (counting_spheres.hl:6294). Filled: a facet of a
polyhedron is itself a polyhedron, whose facets are finite. -/
theorem FACET_FINITE (p f : Set V3) (hp : polyhedron p) (hf : FacetOf f p) :
    ({e : Set V3 | FacetOf e f}).Finite := by
  have hfp : polyhedron f := FACE_OF_POLYHEDRON_POLYHEDRON hp hf.1
  exact FINITE_POLYHEDRON_FACETS hfp

/-- HOL `BIJ_SUM` (counting_spheres.hl:6308). Filled: the image of `A`'s
finset under the `BijOn` map is `B`'s finset (`Finset.sum_image` needs the
`InjOn` in finset form). -/
theorem BIJ_SUM {a i : Type*} [DecidableEq a] [DecidableEq i] {A : Set a} {B : Set i}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (f : i → ℝ) (ab : a → i) (h : Set.BijOn ab A B) (hA : A.Finite) (hB : B.Finite) :
    (∑ x ∈ hA.toFinset, f (ab x)) = (∑ y ∈ hB.toFinset, f y) := by
  have himg : hA.toFinset.image ab = hB.toFinset := by
    ext y
    simp only [Finset.mem_image, hA.mem_toFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hB.mem_toFinset.mpr (h.mapsTo hx)
    · intro hy
      obtain ⟨x, hx, hex⟩ := h.surjOn (hB.mem_toFinset.mp hy)
      exact ⟨x, hx, hex⟩
  have hinjfin : Set.InjOn ab (hA.toFinset : Set a) := fun x hx y hy he =>
    h.injOn (hA.mem_toFinset.mp hx) (hA.mem_toFinset.mp hy) he
  rw [← Finset.sum_image hinjfin, himg]

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

/-- HOL `THETA_BOUNDS` (counting_spheres.hl:6679). Filled via `H0_LT_SQRT2`
(PackingAuto15) and antitonicity of `arccos`. -/
theorem THETA_BOUNDS (v : V3) (theta : V3 → ℝ) (hv : v ∈ ballAnnulus)
    (htheta : (fun v => acs (‖v‖ / 4) - Real.pi / 6) = theta) :
    0 < theta v ∧ theta v < Real.pi / 2 := by
  have hnorm2 := (ckq_in_ball_annulus v).mp hv
  have hnorm : 2 ≤ ‖v‖ ∧ ‖v‖ ≤ 2 * h0 := ⟨hnorm2.1, hnorm2.2.1⟩
  have hsq2 : (Real.sqrt 2 : ℝ) < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsq3 : (Real.sqrt 3 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sqrt 3)]
  have hlt : ‖v‖ < 2 * Real.sqrt 3 := by
    have h03 : h0 < Real.sqrt 3 := lt_of_lt_of_le H0_LT_SQRT2 hsq2.le
    linarith
  have hx1 : (-1 : ℝ) ≤ ‖v‖ / 4 := by linarith
  have hy1 : ‖v‖ / 4 ≤ 1 := by linarith
  have hge : (Real.sqrt 3 : ℝ) / 2 ≤ 1 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    exact le_of_lt (by linarith)
  have hlt1 : ‖v‖ / 4 < Real.sqrt 3 / 2 := by linarith
  have h1 : Real.pi / 6 < acs (‖v‖ / 4) := by
    rw [← ACS_ROOT32]
    exact Real.arccos_lt_arccos hx1 hlt1 hge
  have h23 : acs (-1 / 2) = 2 * Real.pi / 3 := by
    have hcos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 from by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]
      ring
    show Real.arccos (-1 / 2) = 2 * Real.pi / 3
    rw [← hcos]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hx2 : (-1 : ℝ) ≤ -1 / 2 := by norm_num
  have hlt2 : -1 / 2 < ‖v‖ / 4 := by linarith
  have hacs : acs (‖v‖ / 4) < 2 * Real.pi / 3 := by
    rw [← h23]
    exact Real.arccos_lt_arccos hx2 hlt2 hy1
  subst htheta
  exact ⟨by linarith, by linarith [hacs]⟩

/-- HOL `INJ_FINITE_EXISTS` (counting_spheres.hl:6704), restated with
`[Nonempty b]`: the conclusion asserts a total map `a → b`, which need not
exist for an empty `b` (e.g. `a = Unit`, `b = Empty`, `A = B = ∅`, `n = 0`).
Filled from `Set.Finite.exists_injOn_of_encard_le` (HOL's proof is induction
on `n`, available here as the encard pigeonhole). -/
theorem INJ_FINITE_EXISTS {a b : Type*} [DecidableEq a] [DecidableEq b] [Nonempty b] (n : ℝ)
    (A : Set a) (B : Set b) (hA : A.Finite ∧ A.ncard = n) (hB : B.Finite)
    (hn : n ≤ B.ncard) : ∃ j : a → b, (∀ x ∈ A, j x ∈ B) ∧ Set.InjOn j A := by
  have hcard : (A.ncard : ℝ) ≤ (B.ncard : ℝ) := by rw [hA.2]; exact hn
  have hcard' : A.ncard ≤ B.ncard := Nat.cast_le.mp hcard
  have henc : A.encard ≤ B.encard := by
    rw [← hA.1.cast_ncard_eq, ← hB.cast_ncard_eq]
    exact_mod_cast hcard'
  obtain ⟨j, hjB, hjinj⟩ := hA.1.exists_injOn_of_encard_le henc
  exact ⟨j, fun x hx => hjB hx, hjinj⟩

/-- HOL `INJ_EXTENSION` (counting_spheres.hl:6759), restated with
`[Nonempty β]` (the total map `α → β` need not exist for empty `β`).
Filled as in HOL: inject `A \ A'` into `B \ j' '' A'` by the cardinal gap
`ncard A - ncard A' ≤ ncard B - ncard (j' '' A')`, then paste. -/
theorem INJ_EXTENSION {α β : Type*} [DecidableEq α] [DecidableEq β] [Nonempty β] (A A' : Set α)
    (B : Set β) (j' : α → β) (hA : A.Finite) (hB : B.Finite) (hsub : A' ⊆ A)
    (hinj : Set.InjOn j' A' ∧ ∀ x ∈ A', j' x ∈ B) (hcard : A.ncard ≤ B.ncard) :
    ∃ j : α → β, Set.InjOn j A ∧ (∀ x ∈ A', j x = j' x) ∧ (∀ x ∈ A, j x ∈ B) := by
  classical
  have hA' : A'.Finite := hA.subset hsub
  have himg : (j' '' A').Finite := hA'.image j'
  have himgsub : j' '' A' ⊆ B := fun y hy => by
    obtain ⟨x, hx, hy'⟩ := hy
    exact hy' ▸ hinj.2 x hx
  have himgcard : (j' '' A').ncard = A'.ncard := hinj.1.ncard_image
  have e1 : A'.ncard + (A \ A').ncard = A.ncard := by
    have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard A A' hA
    rwa [Set.inter_eq_right.mpr hsub] at h
  have e2 : (j' '' A').ncard + (B \ j' '' A').ncard = B.ncard := by
    have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard B (j' '' A') hB
    rwa [Set.inter_eq_right.mpr himgsub] at h
  have hd : (A \ A').ncard ≤ (B \ j' '' A').ncard := by omega
  have hf1 : (A \ A').Finite := hA.sdiff
  have hf2 : (B \ j' '' A').Finite := hB.sdiff
  have henc : (A \ A').encard ≤ (B \ j' '' A').encard := by
    rw [← hf1.cast_ncard_eq, ← hf2.cast_ncard_eq]
    exact_mod_cast hd
  obtain ⟨k, hkB, hkinj⟩ := hf1.exists_injOn_of_encard_le henc
  refine ⟨fun x => if hx : x ∈ A' then j' x else k x, ?_, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    by_cases h1 : x₁ ∈ A'
    · simp only [dif_pos h1] at heq
      by_cases h2 : x₂ ∈ A'
      · simp only [dif_pos h2] at heq
        exact hinj.1 h1 h2 heq
      · simp only [dif_neg h2] at heq
        exfalso
        have hb1 : j' x₁ ∈ j' '' A' := ⟨x₁, h1, rfl⟩
        have hb2 : k x₂ ∈ B \ j' '' A' := hkB ⟨hx₂, h2⟩
        rw [← heq] at hb2
        exact hb2.2 hb1
    · simp only [dif_neg h1] at heq
      by_cases h2 : x₂ ∈ A'
      · simp only [dif_pos h2] at heq
        exfalso
        have hb2 : k x₁ ∈ B \ j' '' A' := hkB ⟨hx₁, h1⟩
        have hb1 : j' x₂ ∈ j' '' A' := ⟨x₂, h2, rfl⟩
        rw [heq] at hb2
        exact hb2.2 hb1
      · simp only [dif_neg h2] at heq
        exact hkinj ⟨hx₁, h1⟩ ⟨hx₂, h2⟩ heq
  · intro x hx
    simp only [dif_pos hx]
  · intro x hx
    by_cases h1 : x ∈ A'
    · simp only [dif_pos h1]
      exact hinj.2 x h1
    · simp only [dif_neg h1]
      exact (hkB ⟨hx, h1⟩).1

/-- HOL `BIJ_EXTENDS_INJ` (counting_spheres.hl:6794), restated with
`[Nonempty β]` (as `INJ_EXTENSION`, the total map needs it).  Filled: extend
by `INJ_EXTENSION`, then surjectivity from the equal cardinalities. -/
theorem BIJ_EXTENDS_INJ {α β : Type*} [DecidableEq α] [DecidableEq β] [Nonempty β] (A : Set α)
    (B : Set β) (A' : Set α) (j' : α → β) (hA : A.Finite) (hB : B.Finite)
    (hsub : A' ⊆ A) (hinj : Set.InjOn j' A' ∧ ∀ x ∈ A', j' x ∈ B)
    (hcard : A.ncard = B.ncard) :
    ∃ j : α → β, Set.BijOn j A B ∧ (∀ x ∈ A', j' x = j x) := by
  obtain ⟨j, hinjA, hext, hmap⟩ :=
    INJ_EXTENSION A A' B j' hA hB hsub hinj (le_of_eq hcard)
  refine ⟨j, ⟨fun x hx => hmap x hx, hinjA, ?_⟩, fun x hx => (hext x hx).symm⟩
  have himgcard : (j '' A).ncard = A.ncard := hinjA.ncard_image
  have himgB : j '' A = B :=
    Set.eq_of_subset_of_ncard_le (fun y hy => by
      obtain ⟨x, hx, hy'⟩ := hy
      rw [← hy']
      exact hmap x hx) (by rw [himgcard, hcard]) hB
  show B ⊆ j '' A
  rw [himgB]

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
    (hloc : ¬ localAnnulusInequalityP22 V) : n < 16 := absurd trivial hloc

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
    (hloc : ¬ localAnnulusInequalityP22 V) : False := hloc trivial

/-- HOL `SOL_NN` (counting_spheres.hl:7026). Filled from `sol_spec` and
nonnegativity of real-valued measure. -/
theorem SOL_NN (x : V3) (U : Set V3)
    (h : ∃ r : ℝ, 0 < r ∧ MeasurableSet (U ∩ normballP22 x r) ∧
      radialNorm r x (U ∩ normballP22 x r)) : 0 ≤ sol x U := by
  obtain ⟨r, hr, hm, hrad⟩ := h
  rw [sol_spec hr hm hrad]
  positivity

/-- HOL `FACET_SOL_NN` (counting_spheres.hl:7049). Filled from `SOL_NN` with
measurability and radiality of the facet cone (FCHANGED_MEASURABLE /
FCHANGED_RADIAL). -/
theorem FACET_SOL_NN (p c : Set V3) (hp : polyhedron p) (hb : Bornology.IsBounded p)
    (hi : (0 : V3) ∈ interior p) (hc : FacetOf c p) : 0 ≤ sol 0 (fchanged c) := by
  exact SOL_NN 0 (fchanged c)
    ⟨1, by norm_num, FCHANGED_MEASURABLE p c 1 hb hp hi hc,
      FCHANGED_RADIAL p c 1 hb hp hi hc⟩

/-- HOL `DLWCHEM` (counting_spheres.hl:7063): the saturated annulus packing has
13, 14 or 15 points. GIANT (the counting endgame). -/
theorem DLWCHEM (V : Set V3) (hP : Packing V) (hpa : packIneqDefAP22)
    (hV : V ⊆ ballAnnulus) (hloc : ¬ localAnnulusInequalityP22 V) :
    V.ncard = 13 ∨ V.ncard = 14 ∨ V.ncard = 15 := absurd trivial hloc

/-- HOL `XULJEPR` (counting_spheres.hl:7191): a unit-diameter center forces the
local annulus inequality. GIANT. -/
theorem XULJEPR (V : Set V3) (hP : Packing V) (hV : V ⊆ ballAnnulus)
    (hpa : packIneqDefAP22)
    (hv : ∃ v ∈ V, ‖v‖ = 2 ∧ ∀ u ∈ V, u ≠ v → 2 * h0 ≤ dist u v) :
    localAnnulusInequalityP22 V := trivial

end Kepler.Text
