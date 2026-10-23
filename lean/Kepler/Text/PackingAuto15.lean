/-
Packing chapter, mcell counting / union calculus over the gamma-cells
(S15 stage): the `marchal3` lane.

HOL source: `scripts/packing/marchal3.hl` (6809 lines). Contents: 4
`new_definition`s (`aff_ge_alt`, `smallest_angle_set`, `smallest_angle_line`,
`gammaY`) plus the chapter's named lemmas: the Rogers/voronoi membership kit
(`HD_IN_ROGERS`, `ROGERS_SUBSET_VORONOI_CLOSED`, `HD_IN_MCELL`), the
finiteness/counting calculus of Marchal cells (`FINITE_MCELL_SET_*`,
`CARD_*_BOUND*`, `BOUNDARY_VOLUME`, `PACKING_BALL_BOUNDARY`,
`BOUNDS_V*_klemma`, `CARD_EDGEX_LE_16`, `CARD_MCELL_CONTAINS_POINT_klemma`),
cell rigidity (`MCELL_ID_OMEGA_LIST_N`, `MCELL_ID_MXI`, `MCELL_ID_MXI_2`),
cell geometry (`MCELL_SUBSET_BALL*`, `EDGEX_SUBSET_MCELL`,
`FINITE_VX`, `FINITE_EDGE_X2`), dihedral bookkeeping (`DIHX_RANGE`,
`DIHX_LE_PI`, `DIHX_SYM`, `DIHV_SYM_2/3`), the smallest-angle kit
(`smallest_angle_*`, `SMALLEST_ANGLE_*`), conic-cap positivity
(`CONIC_CAP_*`), and the gamma bounds (`gamma_y_pos_le`,
`gamma_y_lmfun_bound2`, `BOUND_GAMMA_X_lmfun`), plus pattern-lambda
bookkeeping (`pre_beta`, `BETA_PAIR_THM`, `BETA_SET_2_THM`,
`well_defined_unordered_pair`, `WELLDEFINED_FUNCTION_2`, `SUM_PAIR_2_SET`)
and `barV`/`lmfun` basics. These feed the KIZHLTL volume/sum interfaces and
the leaf/sum_gamma bounds downstream.

`mcell_set` usage report. Unlike marchal2 (where PackingAuto12 found
`mcell_set` UNUSED), marchal3 uses `mcell_set` essentially: as hypothesis or
conclusion in `FINITE_MCELL_SET_LEMMA_concl`/`FINITE_MCELL_SET_LEMMA`,
`FINITE_MCELL_SET_LEMMA_2`, `MCELL_SUBSET_BALL_4`, `MCELL_SUBSET_BALL8_2`,
`gamma_y_pos_le`, `gamma_y_lmfun_bound2`, `BOUND_GAMMA_X_lmfun`, `DIHX_SYM`,
`EDGEX_SUBSET_MCELL`, `CRITICAL_EDGEX_SUBSET_MCELL`, `FINITE_VX`,
`CARD_EDGEX_LE_16`, `CARD_MCELL_CONTAINS_POINT_klemma` and (through the
KIZHLTL concls it feeds) throughout the counting calculus. Ported as
membership in the PackingAuto2 `mcellSet` family (`X ∈ mcellSet V`).

Encoding notes.
- HOL `real^3` ↔ `V3` (Kepler.Geom); `packing` ↔ `Packing` (Kepler.Statement);
  `HD ul` ↔ `hdV ul`; `mcell_set` ↔ `mcellSet`; `VX`, `edgeX`, `dihX`, `dihV`,
  `dihu2/3/4`, `gammaX`, `lmfun`, `h0`, `criticalEdgeX`, `mxi`, `omega_list_n`
  ↔ `omegaListN`, `hl`, `barV`, `set_of_list` ↔ `setOfList`, `nullSet`,
  `voronoi_closed` ↔ `voronoiClosed`, `rogers`, `rcone_gt` ↔ `rconeGt` are the
  PackingAuto2 definitions. HOL `~NULLSET X` / `~negligible X` ↔
  `¬ nullSet X` (`volume X = 0`).
- New defs ported here: HOL `aff_ge_alt` ↔ `affGeAlt` (over
  `Kepler.Geom.linCombo`), `smallest_angle_set`/`smallest_angle_line` ↔
  `smallestAngleSet`/`smallestAngleLine`, `gammaY` ↔ `gammaY`, plus
  `conic_cap` ↔ `conicCap` (flyspeck_multivariate.ml:4832), the OPEN `wedge`
  (flyspeck_multivariate.ml:3714; distinct from the closed `wedgeGe` of
  PackingAuto2), and `int_ball` ↔ `intBall` (mirror of PackingAuto1.lean:84,
  whose olean is not importable in this checkout).
- HOL pattern abstractions `\{u,v}. g u v` are rendered by the choice
  function `patternPair` (public: it occurs in statements), mirroring the
  `Classical.epsilon` rendering of `gammaX` in PackingAuto2; `pairOf` is the
  analogous ordered-pair choice used in `gammaY`. HOL `\{u,v}.`-calculus
  (`pre_beta`, `BETA_PAIR_THM`, ...) is stated for `patternPair`.
- HOL `lift : real -> real^1` is rendered as the constant `Fin 1`-vector
  `fun _ : Fin 1 => f x : Fin 1 → ℝ`; the LIFT_* continuity kit is stated for
  that rendering (domain specialized to `V3`, all this chapter needs).
- HOL `sum` ↔ `setSum`, `CARD` ↔ `Nat.card`, `FINITE` ↔ `Set.Finite`,
  `bounded` ↔ `Bornology.IsBounded`, `subspace` ↔ `Submodule ℝ V3`,
  `ball (vec 0, r)` ↔ `Metric.ball 0 r`, `vol` ↔ `MeasureTheory.volume`,
  `0..k` ↔ `Set.Iic k`, `coplanar` ↔ `Coplanar ℝ`.
- HOL `measurable` is rendered as `NullMeasurableSet · volume` in
  `MEASURABLE_BALL_AFF_GE`: Mathlib's unconditional fact for convex sets is
  `Convex.nullMeasurableSet` (`Convex.addHaar_frontier`), and no
  `Measure.IsComplete` instance for `volume` exists in Mathlib to upgrade it.
- Proofs: mechanical lemmas are proved; the large geometry/counting proofs
  (`MCELL_ID_*`, `LEFT_ACTION_LIST_*`, `DIHX_SYM`, the klemma bound kit, ...)
  are `sorry` skeletons faithful to the source statements, for later lanes.
  The `CONIC_CAP_*` trio is PROVED (GT-3 Kit D lane, affine-box route):
  `p15_box_pos` (Kit D: `p15_comboMap` endomorphism with `det != 0` from Kit B
  linear independence, open good-parameter region, volume transport via
  `Measure.addHaar_image_linearMap`) + `p15_coplML` (the chapter's
  `Coplanar` implies Mathlib's `Coplanar ℝ`, via `vectorSpan` finrank ≤ 2)
  + `wedge_eq_affGt`/`p15_bisector_exists` for the wedge form.

DISCHARGES: none. None of the PackingAuto2 `*_concl` interfaces matches this
chapter: `TIWWFYQ` is already proved in PackingAuto5 (pack3 lane);
`URRPHBZ3`/`QZYZMJC`/`KIZHLTL1-3` belong to the KIZHLTL/URRPHBZ lanes;
`GOTCJAH`/`UPFZBZM`/`RDWKARC` belong to the sum_gamma / UPFZBZM / RDWKARC
lanes. marchal3 supplies infrastructure toward KIZHLTL (the finite-mcell-set
and card-bound shape of `FINITE_MCELL_SET_LEMMA_concl` is exactly the family
entering `KIZHLTL*_concl`), not a concl discharge itself.
(NOTE: `PackingAuto9`/`PackingAuto14` oleans do not exist in this checkout;
they are not imported and nothing proved here needs them.)
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
import Kepler.Text.PackingAuto14
import Kepler.Text.PackingAuto17
import Kepler.Text.Polytope
import Kepler.Geom.LuneVolume
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## Support kit (private, `p15_` prefix; plus the new chapter defs) -/

/-- HOL `int_ball` (mirror of `PackingAuto1.lean:84`; that olean is not
importable in this checkout, so the chapter keeps its own copy): the integer
lattice points inside the ball. -/
def intBall (c : V3) (r : ℝ) : Set V3 :=
  {x : V3 | (∀ i : Fin 3, ∃ n : ℤ, (x i : ℝ) = (n : ℝ)) ∧ x ∈ Metric.ball c r}

/-- HOL `conic_cap` (flyspeck_multivariate.ml:4832):
`conic_cap v0 v1 r a = normball v0 r INTER rcone_gt v0 v1 a`. -/
def conicCap (v0 v1 : V3) (r a : ℝ) : Set V3 :=
  Metric.closedBall v0 r ∩ rconeGt v0 v1 a

/-- HOL `wedge` (flyspeck_multivariate.ml:3714), the OPEN wedge; distinct
from PackingAuto2's closed `wedgeGe`. -/
def wedge (v0 v1 w1 w2 : V3) : Set V3 :=
  {y : V3 | ¬Collinear3 v0 v1 y ∧ 0 < azim v0 v1 w1 y ∧
    azim v0 v1 w1 y < azim v0 v1 w1 w2}

/-- HOL pattern abstraction `\{u, v}. g u v` (used by `gammaY`, `pre_beta`,
`BETA_PAIR_THM`, `BETA_SET_2_THM`, `SUM_PAIR_2_SET` in marchal3.hl): rendered
by a Classical choice of the value over the ordered-pair presentations, in
the same style as the `gammaX` rendering in PackingAuto2. The `Nonempty β`
constraint is an artifact of the choice rendering (HOL's `@x.` has junk on
empty domains). -/
noncomputable def patternPair {β : Type*} [Nonempty β] (g : V3 → V3 → β) : Set V3 → β :=
  fun e => Classical.epsilon fun x : β => ∃ u v : V3, e = ({u, v} : Set V3) ∧ g u v = x

/-- Ordered-pair choice for an unordered pair `e`, mirroring the
`Classical.epsilon fun r => e = {r.1, r.2}` rendering used for `gammaX`. -/
private noncomputable def pairOf (e : Set V3) : V3 × V3 :=
  Classical.epsilon fun r : V3 × V3 => e = {r.1, r.2}

private theorem pairOf_spec {e : Set V3} (h : ∃ u v : V3, e = ({u, v} : Set V3)) :
    {(pairOf e).1, (pairOf e).2} = e := by
  obtain ⟨u, v, hv⟩ := h
  have hs := Classical.epsilon_spec (p := fun r : V3 × V3 => e = {r.1, r.2}) ⟨(u, v), hv⟩
  exact hs.symm

private theorem p15_arcV_sym (u v w : V3) : arcV u v w = arcV u w v := by
  unfold arcV
  congr 1
  simp [dotProduct_comm, mul_comm]

private theorem p15_arcV_range (u v w : V3) : 0 ≤ arcV u v w ∧ arcV u v w ≤ Real.pi := by
  rw [arcV]
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

private theorem p15_dihV_range (x y z t : V3) : 0 ≤ dihV x y z t ∧ dihV x y z t ≤ Real.pi := by
  unfold dihV
  exact p15_arcV_range 0 _ _

private theorem p15_setOfList_finite {α : Type*} (ul : List α) : (setOfList ul).Finite := by
  refine Set.Finite.subset ul.toFinset.finite_toSet ?_
  intro x hx
  exact List.mem_toFinset.mpr hx

private theorem p15_card_image {α β : Type*} (F : α → β) (S : Set α)
    (hInj : Set.InjOn F S) : Nat.card ↥(F '' S) = Nat.card ↥S :=
  Nat.card_congr (Equiv.Set.imageOfInjOn F S hInj).symm

private theorem p15_dot_contOn {X : Type*} [TopologicalSpace X] {s : Set X}
    {f g : X → V3} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x ⬝ᵥ g x) s := by
  have h : (fun x : X => f x ⬝ᵥ g x) = fun x => inner ℝ (f x) (g x) := by
    funext x
    exact (inner_eq_dot _ _).symm
  rw [h]
  exact hf.inner hg

/-! ## marchal3.hl:47-1167 Lemma 1-3: Rogers/voronoi membership, finite mcell sets -/

/-- marchal3.hl:47 `HD_IN_ROGERS`. -/
theorem HD_IN_ROGERS (V : Set V3) (ul : List V3) (hs : saturated V) (hp : Packing V)
    (hb : barV V 3 ul) : hdV ul ∈ rogers V ul := by
  rw [ROGERS_EXPLICIT V ul hs hp hb]
  exact IN_SET_IMP_IN_CONVEX_HULL_SET _ _ (Set.mem_insert _ _)

/-- marchal3.hl:56 `ROGERS_SUBSET_VORONOI_CLOSED`. -/
theorem ROGERS_SUBSET_VORONOI_CLOSED (V : Set V3) (ul : List V3) (hs : saturated V)
    (hp : Packing V) (hb : barV V 3 ul) : rogers V ul ⊆ voronoiClosed V (hdV ul) := by
  intro x hx
  rw [ROGERS_EXPLICIT V ul hs hp hb] at hx
  have hconv : Convex ℝ (voronoiClosed V (hdV ul)) := CONVEX_VORONOI_CLOSED V (hdV ul)
  have hω : ∀ i : ℕ, i ≤ 3 →
      omegaListN V ul i ∈ voronoiClosed V (hdV ul) := by
    intro i hi
    have hw := OMEGA_LIST_N_IN_VORONOI_LIST V ul 3 i hb hi
    rw [voronoiList, voronoiSet] at hw
    have hmemF : (voronoiClosed V (hdV ul) : Set V3) ∈
        {x | ∃ v ∈ setOfList (truncateSimplex i ul), voronoiClosed V v = x} :=
      ⟨hdV ul, by
        rw [← HD_TRUNCATE_SIMPLEX ul i (by rw [hb.1]; omega)]
        exact HD_IN_SET_OF_LIST (truncateSimplex i ul)
          (by rw [LENGTH_TRUNCATE_SIMPLEX i ul (by rw [hb.1]; omega)]; omega), rfl⟩
    exact (Set.sInter_subset_of_mem hmemF) hw
  have hmem : ∀ z ∈ ({hdV ul, omegaListN V ul 1, omegaListN V ul 2, omegaListN V ul 3} :
      Set V3), z ∈ voronoiClosed V (hdV ul) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · intro w _
      rw [dist_self]
      exact dist_nonneg
    · rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact hω 1 (by omega)
      · rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact hω 2 (by omega)
        · rcases Set.mem_singleton_iff.mp hz with rfl
          exact hω 3 (by omega)
  exact convexHull_min hmem hconv hx

/-- HOL `BARV_3_IMP_FINITE_lemma1` (QZYZMJC.hl:62-100; private `p15_` copy of
the proved PackingAuto16 template, discharging to
`Kepler.Text.PackingAuto12.VORONOI_LIST_3_SINGLETON_EXPLICIT`): two list
points of a `barV V 3` simplex over a saturated packing are less than `4`
apart. -/
private theorem p15_barV3ImpFinite1 {V : Set V3} {ul : List V3} {u v : V3}
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (huv : {u, v} ⊆ setOfList ul) : dist u v < 4 := by
  obtain ⟨a, ha1, _ha2, _ha3⟩ := VORONOI_LIST_3_SINGLETON_EXPLICIT V ul hp hs hb
  have hamem : a ∈ voronoiList V ul := by rw [ha1]; exact rfl
  have key : ∀ s ∈ setOfList ul, dist a s < 2 := by
    intro s hsmem
    obtain ⟨y, hyV, hyd⟩ := hs a
    have hmem : a ∈ ⋂₀ {voronoiClosed V w | w ∈ setOfList ul} := hamem
    have has : a ∈ voronoiClosed V s :=
      Set.mem_sInter.mp hmem (voronoiClosed V s) ⟨s, hsmem, rfl⟩
    have h1 : dist a s ≤ dist a y := by
      simpa only [voronoiClosed, Set.mem_setOf_eq] using has y hyV
    calc dist a s ≤ dist a y := h1
      _ < 2 := hyd
  have hdu : dist a u < 2 := key u (huv (by simp))
  have hdv : dist a v < 2 := key v (huv (by simp))
  calc dist u v ≤ dist u a + dist a v := dist_triangle u a v
    _ < 4 := by rw [dist_comm u a]; linarith

/-- HOL `BARV_3_IMP_FINITE_lemma2` (QZYZMJC.hl:104-110; private `p15_` copy
of the proved PackingAuto16 template): the whole list sits in the radius-`4`
ball around any of its points. -/
private theorem p15_barV3ImpFinite2 {V : Set V3} {ul : List V3} {v : V3}
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hv : v ∈ setOfList ul) :
    setOfList ul ⊆ Metric.ball v 4 := by
  intro s hsmem
  refine p15_barV3ImpFinite1 hp hs hb ?_
  intro x hx
  rcases (by simpa using hx : x = s ∨ x = v) with hx1 | hx1
  · rw [hx1]
    exact hsmem
  · rw [hx1]
    exact hv

/-- marchal3.hl:101 `HD_IN_MCELL`. -/
theorem HD_IN_MCELL (V : Set V3) (ul : List V3) (i : ℕ) (X : Set V3)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell i V ul)
    (hne : X ≠ ∅) (hi : i ≠ 0) : hdV ul ∈ X := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  have hsethd : hdV ul ∈ setOfList ul :=
    HD_IN_SET_OF_LIST ul (by rw [hb.1]; omega)
  by_cases h1 : i = 1
  · -- i = 1: the Rogers simplex inside cball(HD, √2) minus the strict cone
    -- at HD; the head is in the simplex, in the closed ball, off the cone
    -- (its dot product at the tip vanishes).
    have hX1 : X = mcell1 V ul := by
      rw [hX, h1]
      exact (MCELL_EXPLICIT 1 V ul).2.1
    rw [hX1] at hne ⊢
    rw [mcell1] at hne ⊢
    by_cases hcond : Real.sqrt 2 ≤ hl ul
    · rw [if_pos hcond]
      refine ⟨⟨HD_IN_ROGERS V ul hs hp hb, ?_⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_self]
        exact Real.sqrt_nonneg _
      · intro hmem
        simp only [rconeGt, Set.mem_setOf_eq] at hmem
        rw [sub_self, dist_self] at hmem
        simp at hmem
    · rw [if_neg hcond] at hne
      exact absurd rfl hne
  by_cases h2 : i = 2
  · -- i = 2: the edge cell; the head is at the tip of both cones (vanishing
    -- dot / a ≤ 1 arithmetic) and a vertex of the aff_ge wedge.
    have hX2 : X = mcell2 V ul := by
      rw [hX, h2]
      exact (MCELL_EXPLICIT 2 V ul).2.2.1
    rw [hX2] at hne ⊢
    rw [mcell2] at hne ⊢
    by_cases hcond : hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
    · rw [if_pos hcond]
      simp only []
      obtain ⟨hlt2, _⟩ := hcond
      have hale : hl (truncateSimplex 1 ul) / Real.sqrt 2 ≤ 1 :=
        (div_le_one (Real.sqrt_pos.mpr (by norm_num))).mpr (le_of_lt hlt2)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [rconeGe, Set.mem_setOf_eq]
        rw [sub_self, dist_self]
        simp
      · simp only [rconeGe, Set.mem_setOf_eq]
        have hdot : inner ℝ (hdV ul - hdV ul.tail) (hdV ul - hdV ul.tail)
            = (hdV ul - hdV ul.tail) ⬝ᵥ (hdV ul - hdV ul.tail) :=
          inner_eq_dot _ _
        rw [← hdot, real_inner_self_eq_norm_sq, dist_eq_norm]
        rw [pow_two]
        have hd2 : 0 ≤ ‖hdV ul - hdV ul.tail‖ * ‖hdV ul - hdV ul.tail‖ :=
          mul_nonneg (norm_nonneg _) (norm_nonneg _)
        calc ‖hdV ul - hdV ul.tail‖ * ‖hdV ul - hdV ul.tail‖
            = ‖hdV ul - hdV ul.tail‖ * ‖hdV ul - hdV ul.tail‖ * 1 := (mul_one _).symm
          _ ≥ ‖hdV ul - hdV ul.tail‖ * ‖hdV ul - hdV ul.tail‖ *
              (hl (truncateSimplex 1 ul) / Real.sqrt 2) :=
            mul_le_mul_of_nonneg_left hale hd2
      · exact CONVEX_HULL_4_SUBSET_AFF_GE_2_2 _ _ _ _
          (IN_SET_IMP_IN_CONVEX_HULL_SET _ _ (by simp))
    · rw [if_neg hcond] at hne
      exact absurd rfl hne
  by_cases h3 : i = 3
  · -- i = 3: the facet cell is the hull of the first three points (plus mxi);
    -- the head is the first truncation point.
    have hX3 : X = mcell3 V ul := by
      rw [hX, h3]
      exact (MCELL_EXPLICIT 3 V ul).2.2.2.1
    rw [hX3] at hne ⊢
    rw [mcell3] at hne ⊢
    by_cases hcond : hl (truncateSimplex 2 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul
    · rw [if_pos hcond]
      refine IN_SET_IMP_IN_CONVEX_HULL_SET _ _ (Or.inl ?_)
      rw [← HD_TRUNCATE_SIMPLEX ul 2 (by rw [hb.1]; omega)]
      exact HD_IN_SET_OF_LIST (truncateSimplex 2 ul)
        (by rw [LENGTH_TRUNCATE_SIMPLEX 2 ul (by rw [hb.1]; omega)]; omega)
    · rw [if_neg hcond] at hne
      exact absurd rfl hne
  -- 4 ≤ i: the whole Delaunay tetrahedron; the head is a list point.
  have h4 : 4 ≤ i := by omega
  have hX4 : X = mcell4 V ul := by
    rw [hX]
    exact (MCELL_EXPLICIT i V ul).2.2.2.2 h4
  rw [hX4] at hne ⊢
  rw [mcell4] at hne ⊢
  by_cases hcond : hl ul < Real.sqrt 2
  · rw [if_pos hcond]
    exact IN_SET_IMP_IN_CONVEX_HULL_SET _ _ hsethd
  · rw [if_neg hcond] at hne
    exact absurd rfl hne

/-- marchal3.hl:231 `FINITE_MCELL_SET_lemma1`. -/
theorem FINITE_MCELL_SET_lemma1 (V : Set V3) (ul : List V3) (i : ℕ) (r : ℝ) (X : Set V3)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell i V ul)
    (hball : X ⊆ Metric.ball 0 r) (hne : X ≠ ∅) :
    ∀ u ∈ setOfList ul, u ∈ Metric.ball 0 (r + 6) := by
  have hsethd : hdV ul ∈ setOfList ul :=
    HD_IN_SET_OF_LIST ul (by rw [hb.1]; omega)
  have hsub : setOfList ul ⊆ Metric.ball (hdV ul) 4 :=
    p15_barV3ImpFinite2 hp hs hb hsethd
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · -- i = 0: a cell point sees the head at distance < 2 (saturation via
    -- rogers ⊆ voronoi_closed), so every list point is within r + 2 + 4.
    subst h0
    have hX0 : X = rogers V ul \ Metric.ball (hdV ul) (Real.sqrt 2) := by
      rw [hX]
      exact (MCELL_EXPLICIT 0 V ul).1
    obtain ⟨s, hsmem⟩ := Set.nonempty_iff_ne_empty.mpr hne
    rw [hX0, Set.mem_sdiff] at hsmem
    obtain ⟨yro, _hnball⟩ := hsmem
    have hvoro : s ∈ voronoiClosed V (hdV ul) :=
      ROGERS_SUBSET_VORONOI_CLOSED V ul hs hp hb yro
    obtain ⟨y, hyV, hyd⟩ := hs s
    have h1 : dist s (hdV ul) ≤ dist s y := by
      simpa only [voronoiClosed, Set.mem_setOf_eq] using hvoro y hyV
    have h2 : dist s (hdV ul) < 2 := by linarith
    have hsX : s ∈ X := by
      rw [hX0]
      exact ⟨yro, _hnball⟩
    have hs0 : dist s 0 < r := hball hsX
    intro u hu
    have hu4 : dist u (hdV ul) < 4 := hsub hu
    rw [Metric.mem_ball]
    have t1 : dist u 0 ≤ dist u (hdV ul) + dist (hdV ul) 0 := dist_triangle u (hdV ul) 0
    have t2 : dist (hdV ul) 0 ≤ dist (hdV ul) s + dist s 0 := dist_triangle (hdV ul) s 0
    have h2' : dist (hdV ul) s < 2 := by rw [dist_comm]; exact h2
    linarith
  · -- i ≠ 0: the head itself is a cell point, hence within ball 0 r.
    have hhdX : hdV ul ∈ X := HD_IN_MCELL V ul i X hp hs hb hX hne hpos.ne'
    have hhd0 : dist (hdV ul) 0 < r := hball hhdX
    intro u hu
    have hu4 : dist u (hdV ul) < 4 := hsub hu
    rw [Metric.mem_ball]
    have t1 : dist u 0 ≤ dist u (hdV ul) + dist (hdV ul) 0 := dist_triangle u (hdV ul) 0
    linarith

/-- marchal3.hl:329 `FINITE_MCELL_SET_LEMMA_concl` (a plain statement `let`
in the source). -/
def FINITE_MCELL_SET_LEMMA_concl : Prop :=
  ∀ (V : Set V3) (r : ℝ), Packing V → saturated V →
    {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}.Finite

/-- marchal3.hl:332 `FINITE_MCELL_SET_LEMMA` (statement is
`FINITE_MCELL_SET_LEMMA_concl`). -/
theorem FINITE_MCELL_SET_LEMMA : FINITE_MCELL_SET_LEMMA_concl := by
  intro V r hp hs
  -- KIUMVTC: `V ∩ ball(0, r+6)` is finite.
  have hs1 : (V ∩ Metric.ball 0 (r + 6)).Finite := hp.finite_inter_ball (r + 6)
  -- the 4-point lists drawn from `V ∩ ball(0, r+6)`
  have hs2 : ({ul : List V3 | ∃ u0 u1 u2 u3 : V3, u0 ∈ V ∩ Metric.ball 0 (r + 6) ∧
      u1 ∈ V ∩ Metric.ball 0 (r + 6) ∧ u2 ∈ V ∩ Metric.ball 0 (r + 6) ∧
      u3 ∈ V ∩ Metric.ball 0 (r + 6) ∧ ul = [u0, u1, u2, u3]}).Finite := by
    have hsub : {ul : List V3 | ∃ u0 u1 u2 u3 : V3, u0 ∈ V ∩ Metric.ball 0 (r + 6) ∧
        u1 ∈ V ∩ Metric.ball 0 (r + 6) ∧ u2 ∈ V ∩ Metric.ball 0 (r + 6) ∧
        u3 ∈ V ∩ Metric.ball 0 (r + 6) ∧ ul = [u0, u1, u2, u3]} ⊆
        (fun q : V3 × V3 × V3 × V3 => [q.1, q.2.1, q.2.2.1, q.2.2.2]) ''
        ((V ∩ Metric.ball 0 (r + 6)) ×ˢ ((V ∩ Metric.ball 0 (r + 6)) ×ˢ
          ((V ∩ Metric.ball 0 (r + 6)) ×ˢ (V ∩ Metric.ball 0 (r + 6))))) := by
      intro l hl
      rw [Set.mem_setOf_eq] at hl
      obtain ⟨u0, u1, u2, u3, h0, h1', h2', h3', rfl⟩ := hl
      exact ⟨(u0, u1, u2, u3),
        Set.mem_prod.mpr ⟨h0, Set.mem_prod.mpr ⟨h1', Set.mem_prod.mpr ⟨h2', h3'⟩⟩⟩, rfl⟩
    exact Set.Finite.subset ((hs1.prod (hs1.prod (hs1.prod hs1))).image _) hsub
  -- the parameter pairs `(i, ul)`, `i ≤ 4`, `ul` a 4-point list as above
  have hs3 : (((Set.Iic (4 : ℕ)) ×ˢ {ul : List V3 | ∃ u0 u1 u2 u3 : V3,
      u0 ∈ V ∩ Metric.ball 0 (r + 6) ∧ u1 ∈ V ∩ Metric.ball 0 (r + 6) ∧
      u2 ∈ V ∩ Metric.ball 0 (r + 6) ∧ u3 ∈ V ∩ Metric.ball 0 (r + 6) ∧
      ul = [u0, u1, u2, u3]}).Finite) := (Set.finite_Iic 4).prod hs2
  have hsub : {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X} ⊆
      insert (∅ : Set V3)
        ((fun t : ℕ × List V3 => mcell t.1 V t.2) '' ((Set.Iic (4 : ℕ)) ×ˢ
          {ul : List V3 | ∃ u0 u1 u2 u3 : V3, u0 ∈ V ∩ Metric.ball 0 (r + 6) ∧
            u1 ∈ V ∩ Metric.ball 0 (r + 6) ∧ u2 ∈ V ∩ Metric.ball 0 (r + 6) ∧
            u3 ∈ V ∩ Metric.ball 0 (r + 6) ∧ ul = [u0, u1, u2, u3]})) := by
    intro X hX
    rw [Set.mem_setOf_eq] at hX
    obtain ⟨hballX, hcellX⟩ := hX
    have hcellX' : ∃ i ul, X = mcell i V ul ∧ barV V 3 ul := hcellX
    obtain ⟨i, ul, hXmul, hbul⟩ := hcellX'
    by_cases hne : X = ∅
    · exact Or.inl hne
    · refine Or.inr ⟨(if i ≤ 4 then i else 4, ul), Set.mem_prod.mpr ⟨?_, ?_⟩, ?_⟩
      · by_cases hle : i ≤ 4
        · rw [if_pos hle]
          exact hle
        · rw [if_neg hle]
          exact le_refl 4
      · obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hbul
        have hmemV : ∀ u ∈ setOfList ul, u ∈ V ∩ Metric.ball 0 (r + 6) := by
          intro u hu
          exact ⟨BARV_SUBSET V 3 ul hbul hu,
            FINITE_MCELL_SET_lemma1 V ul i r X hp hs hbul hXmul hballX hne u hu⟩
        exact ⟨u0, u1, u2, u3, hmemV u0 (by rw [hul]; simp [setOfList]),
          hmemV u1 (by rw [hul]; simp [setOfList]),
          hmemV u2 (by rw [hul]; simp [setOfList]),
          hmemV u3 (by rw [hul]; simp [setOfList]), hul⟩
      · by_cases hle : i ≤ 4
        · rw [if_pos hle, hXmul]
        · rw [if_neg hle, hXmul]
          exact ((MCELL_EXPLICIT i V ul).2.2.2.2 (by omega)).symm
  exact Set.Finite.subset (Set.Finite.insert (∅ : Set V3)
    (hs3.image (fun t : ℕ × List V3 => mcell t.1 V t.2))) hsub

/-- marchal3.hl:443 `CARD_BOUNDARY_INT_BALL_BOUND_1`. -/
theorem CARD_BOUNDARY_INT_BALL_BOUND_1 (x : V3) (k1 k2 : ℝ) (hk1 : 0 < k1) (hk2 : 0 < k2) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      (((Nat.card ↥((intBall x (r + k1)) \ (intBall x (r - k2))) : ℕ) : ℝ)) ≤ C * r ^ 2 := sorry

/-- marchal3.hl:513 `CARD_BOUNDARY_INT_BALL_BOUND`. -/
theorem CARD_BOUNDARY_INT_BALL_BOUND (x : V3) (k1 k2 : ℝ) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      (((Nat.card ↥((intBall x (r + k1)) \ (intBall x (r - k2))) : ℕ) : ℝ)) ≤ C * r ^ 2 := sorry

/-- marchal3.hl:610 `BOUNDARY_VOLUME`.
-- NEEDS: 测度算术，独立中等档（~100-130 行）。路线：VOLUME_BALL 取
-- `EuclideanSpace.volume_ball_fin_three`（ENNReal，ofReal r^3 * ofReal (π*4/3)）
-- 过 `Measure.real_def` 转 `volume.real`；annulus = sdiff 可测（`measurableSet_ball`）
-- 且内球 ⊆ 外球（r-k2 ≤ r+k1）时 `measure_sdiff` 给体积差；立方差恒等式
-- (r+k1)³-(r-k2)³ = 3(k1+k2)r² + 3(k1²-k2²)r + (k1³+k2³) 逐项被
-- C = (4/3)π·(3|k1+k2| + 3k1² + |k1³+k2³|)·r² 压住（1 ≤ r 给 r ≤ r²）。
-- r < k2 支（内球空）：ball(p, r+k1) ⊆ ball(p, |k1+k2|) =: D（k1+k2 ≥ 0 时），
-- 体积 ≤ D ≤ D·r²（volume ≥ 0）；k1+k2 < 0 时 r+k1 < 0 球空即 0。 -/
theorem BOUNDARY_VOLUME (p : V3) (k1 k2 : ℝ) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      volume.real (Metric.ball p (r + k1) \ Metric.ball p (r - k2)) ≤ C * r ^ 2 := sorry

/-- marchal3.hl:737 `PACKING_BALL_BOUNDARY`.
-- NEEDS: 消费 BOUNDARY_VOLUME(k1+1, k2+1) 的计数装配（~120-160 行）。路线：
-- ① B := (V ∩ ball p (r+k1)) \ (V ∩ ball p (r-k2)) 有限：⊆ V ∩ ball 0 (r+k1+‖p‖+1)
--    （dist 三角形），后者 = `hp.finite_inter_ball`（0 心版，Statement 已真证）。
-- ② 计数链 = Statement.finite_inter_ball 的 `key` 论证原样平移到心 p：
--    `measure_biUnion_finset` + `EuclideanSpace.volume_ball_fin_three` +
--    `Finset.sum_const`/`nsmul_eq_mul`，两两不交由 `Packing.dist_ge_two`
--    （球内点三角形 < 2 假设），并集 ⊆ 环 (r+k1+1, r-(k2+1)) 也由三角形。
-- ③ 收尾 CARD B ≤ CARD B·(4π/3)：只需 4π/3 > 1，即 π > 3/4 ——
--    `Real.pi_gt_three` 已足够（HOL 的 #3.14159 < π 只是出这一个不等式；
--    任务书提示的 Real.pi_lt_four 类有理夹逼实测不需要）。 -/
theorem PACKING_BALL_BOUNDARY (V : Set V3) (p : V3) (k1 k2 : ℝ) (hp : Packing V) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      (((Nat.card ↥((V ∩ Metric.ball p (r + k1)) \ (V ∩ Metric.ball p (r - k2))) : ℕ) : ℝ))
        ≤ C * r ^ 2 := sorry

/-- marchal3.hl:831 `MCELL_SUBSET_BALL_4`.
-- NEEDS: 五 case 中四个已有完整初等路线，卡 i=2 的 u0 ≠ u1 一小步（合计
-- ~180-220 行）。地图（供 KIZHLTL2 波 2C 直接施工）：
-- * X = ∅ 支：p := 0 平凡。
-- * i ∈ {0,1}：mcell0 ⊆ rogers、mcell1 ⊆ rogers（if-条件真时），而
--   rogers = hull{omegaListN j | j < 4} ⊆ closedBall (hdV ul) 2 —— 顶点界由
--   下方 `p15_omega_dist_hd`（已证，本波落地），`convexHull_min` +
--   `convex_closedBall` 收口，closedBall 2 ⊆ ball 4。
-- * i ∈ {3,4}：hull（list 点 + mxi）⊆ ball (hdV ul) 4 —— list 点由
--   `p15_barV3ImpFinite2`（已证），mxi ≤ 2 用 PA12.MXI_EXPLICIT（已证公开件；
--   其 h2/h3 恰为 mcell2/mcell3 的 if-条件；mxi 的 if-另支 = omegaListN 2 走
--   `p15_omega_dist_hd`），`convex_ball` 收口。
-- * i = 2（唯一卡点）：affGe 楔无界（`affGe_ray`），有界性只能来自 mutual
--   rconeGe：两锥成员不等式相加得 ‖u1-u0‖² ≥ (d(x,u0)+d(x,u1))·d(u0,u1)·a，
--   a = hl(trunc 1)/√2 = d(u0,u1)/(2√2)（HL_2 + truncate），故 d(x,u0)+d(x,u1)
--   ≤ 2√2 < 4 —— 但需 a > 0 即 u0 ≠ u1。u0 ≠ u1：barV 的 2 点 sublist 给
--   affDim(voronoiList [u0,u1]) = 2（voronoiNondg 取 sublist，PA25:1152 有
--   取法范本）；u0 = u1 时 voronoiList [u0,u0] = voronoiClosed V u0，而
--   voronoiClosed V u0 ⊇ ball(u0,1)（packing 2-分离）且 ⊆ ball(u0,2)
--   （saturation，有界故体积有限正）→ `volPosLtAffDim3_p17`（PA17:181 private
--   已证不可 import，需 p15 自拷 ~60 行）给 affDim = 3，矛盾。dot 线性恒等式
--   (x-u0)⬝(u1-u0) - (x-u1)⬝(u1-u0) = (u1-u0)⬝(u1-u0) 走 inner_eq_dot 分量法
--   （PA13 范本）。HOL 原证走 QZKSYKG2（PA14 GIANT 未移植），Lean 侧必须走
--   上述初等路线。 -/
theorem MCELL_SUBSET_BALL_4 (V : Set V3) (X : Set V3) (hp : Packing V) (hs : saturated V)
    (hm : mcellSet V X) : ∃ p : V3, X ⊆ Metric.ball p 4 := sorry

/-- private `p15_` helper for the future `MCELL_SUBSET_BALL_4` fill (wave 2C):
every omega point of a `barV V 3` list sits strictly within distance `2` of the
head — the Rogers hull vertices all lie in `closedBall (hdV ul) 2`. Route:
`OMEGA_LIST_N_IN_VORONOI_LIST` + `voronoiSet` as a closed-voronoi sInter over
the truncation (the `ROGERS_SUBSET_VORONOI_CLOSED` pattern) + saturation. -/
private theorem p15_omega_dist_hd (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) (j : ℕ) (hj : j ≤ 3) :
    dist (hdV ul) (omegaListN V ul j) < 2 := by
  obtain ⟨y, hyV, hyd⟩ := hs (omegaListN V ul j)
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0, omegaListN, dist_self]
    norm_num
  · have hmem := OMEGA_LIST_N_IN_VORONOI_LIST V ul 3 j hb hj
    rw [voronoiList, voronoiSet] at hmem
    have hmemF : (voronoiClosed V (hdV ul) : Set V3) ∈
        {x | ∃ v ∈ setOfList (truncateSimplex j ul), voronoiClosed V v = x} :=
      ⟨hdV ul, by
        rw [← HD_TRUNCATE_SIMPLEX ul j (by rw [hb.1]; omega)]
        exact HD_IN_SET_OF_LIST (truncateSimplex j ul)
          (by rw [LENGTH_TRUNCATE_SIMPLEX j ul (by rw [hb.1]; omega)]; omega), rfl⟩
    have has := Set.sInter_subset_of_mem hmemF hmem
    have h1 : dist (omegaListN V ul j) (hdV ul) ≤ dist (omegaListN V ul j) y := by
      simpa only [voronoiClosed, Set.mem_setOf_eq] using has y hyV
    rw [dist_comm]
    linarith

/-- marchal3.hl:1034 `HL_2` (HOL: `hl [u; v] = inv (&2) * dist (u, v)`). -/
theorem HL_2 (u v : V3) : hl [u, v] = dist u v / 2 := by
  have hset : setOfList [u, v] = ({u, v} : Set V3) := by
    ext x
    simp [setOfList]
  have hcc : circumcenter ({u, v} : Set V3) = midpoint ℝ u v := CIRCUMCENTER_2 u v
  have hexi : ∃ c : ℝ, ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter ({u, v} : Set V3)) w := by
    refine ⟨dist (midpoint ℝ u v) u, ?_⟩
    rw [hcc]
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw'
    · rfl
    · rcases Set.mem_singleton_iff.mp hw' with rfl
      simp
  have key : radV ({u, v} : Set V3) = dist (circumcenter ({u, v} : Set V3)) u :=
    (Classical.epsilon_spec (p := fun c : ℝ => ∀ w ∈ ({u, v} : Set V3),
      c = dist (circumcenter ({u, v} : Set V3)) w) hexi) u (Set.mem_insert u {v})
  have hhl : hl [u, v] = dist (circumcenter ({u, v} : Set V3)) u := by
    show radV (setOfList [u, v]) = _
    rw [hset, key]
  rw [hhl, hcc]
  simp
  ring

/-- Pythagoras on the inner product (PA12 idiom). -/
private theorem p15_pythI {u v : V3} (h : inner ℝ u v = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring

/-- Real-linearity of `inner ℝ` in the left argument. -/
private theorem p15_hsmL (t : ℝ) (u v : V3) : inner ℝ (t • u) v = t * inner ℝ u v :=
  (inner_smul_real_left u v t).trans (smul_eq_mul t (inner ℝ u v))

/-- Dot functional on `V3`（Polytope `dotRight` 私拷）. -/
private def p15_dotR (a : V3) : V3 →ₗ[ℝ] ℝ where
  toFun x := a ⬝ᵥ x
  map_add' x y := by
    show a.ofLp ⬝ᵥ (x.ofLp + y.ofLp) = a.ofLp ⬝ᵥ x.ofLp + a.ofLp ⬝ᵥ y.ofLp
    rw [dotProduct_add]
  map_smul' r x := by
    show a.ofLp ⬝ᵥ (r • x.ofLp) = (RingHom.id ℝ) r • (a.ofLp ⬝ᵥ x.ofLp)
    rw [dotProduct_smul]
    simp

/-- The squared norm as the self dot product (PA14 bridge). -/
private theorem p15_norm_sq_dot (v : V3) : ‖v‖ ^ 2 = v ⬝ᵥ v := by
  have h := real_inner_self_eq_norm_sq v
  rw [← h, inner_eq_dot]

/-- For `a ≠ 0` the kernel of the dot functional has finrank `2`
（rank-nullity：range 是 `ℝ` 的非零子空间 = `⊤`）. -/
private theorem p15_finrank_ker_dot {a : V3} (ha : a ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (p15_dotR a)) = 2 := by
  have hDpos : (0:ℝ) < a ⬝ᵥ a := by
    rw [← p15_norm_sq_dot]
    exact pow_pos (norm_pos_iff.mpr ha) 2
  have hfa : p15_dotR a a = a ⬝ᵥ a := rfl
  have hrange_ne : LinearMap.range (p15_dotR a) ≠ ⊥ := by
    intro hbot
    have hx : p15_dotR a a ∈ LinearMap.range (p15_dotR a) := ⟨a, rfl⟩
    rw [hbot] at hx
    have h0 : p15_dotR a a = 0 := (Submodule.mem_bot (R := ℝ)).mp hx
    exact hDpos.ne' (by rw [← hfa, h0])
  have hnk := LinearMap.finrank_range_add_finrank_ker (p15_dotR a)
  have h3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
  rw [h3] at hnk
  have hfrle : Module.finrank ℝ (LinearMap.range (p15_dotR a)) ≤ 1 := by
    refine le_trans (Submodule.finrank_mono (le_top : LinearMap.range (p15_dotR a) ≤ _)) ?_
    simp
  have hfrne : Module.finrank ℝ (LinearMap.range (p15_dotR a)) ≠ 0 := by
    intro h
    apply hrange_ne
    exact (Submodule.finrank_eq_zero).mp h
  omega

/-- The bisector of a nondegenerate pair is a hyperplane, `affDim = 2`
（`BIS_EQ_HYPERPLANE`（PA5 公开）+ `affDim_hyperplane`（Polytope 公开））. -/
private theorem p15_affDim_bis_pair {u0 u1 : V3} (hne : u0 ≠ u1) :
    affDim (bis u0 u1) = 2 := by
  have hsub : u1 - u0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  rw [BIS_EQ_HYPERPLANE]
  have heq : {x : V3 | 2 * ((u1 - u0) ⬝ᵥ x) = u1 ⬝ᵥ u1 - u0 ⬝ᵥ u0} =
      {x : V3 | (u1 - u0) ⬝ᵥ x = (u1 ⬝ᵥ u1 - u0 ⬝ᵥ u0) / 2} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [heq]
  exact affDim_hyperplane hsub _

/-- Segment (a) core: `affDim (voronoiList V [u0,u1]) = 2` under the
`hl < sqrt 2` margin (marchal3.hl:1054 `HL_LE_SQRT2_IMP_BARV_1`, case
`vl = [u0;u1]`).
Route: the pair cell is a convex subset of the bisector plane `bis u0 u1`
(affDim 2), and for `≥ 2`: with `p` the midpoint, `D` the 2-dim plane
direction and `R = (s - d/2)/8`, `s = sqrt(4 - (d/2)²) > d/2` (the
`hl < sqrt 2` margin, `d² < 8`), every other packing point `w` satisfies
`‖w - p‖ ≥ s` (sum-of-squares bound `‖w-p‖² = (‖w-u0‖²+‖w-u1‖²)/2 - (d/2)²`
via packing), while `p + v`, `v ∈ D`, `‖v‖ ≤ 2R`, is within
`d/2 + ‖v‖ ≤ d/2 + 2R ≤ s - 2R ≤ s - ‖v‖ ≤ ‖(p+v) - w‖` of both endpoints,
so the patch `p + v` lies in the pair cell; three patch points make two
independent directions `w1, w2 ∈ D` into differences of cell points, so the
cell's vectorSpan has finrank `≥ 2`. -/
private theorem p15_affDim_voronoiList2 (V : Set V3) (u0 u1 : V3)
    (hp : Packing V) (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1)
    (hhl : hl [u0, u1] < Real.sqrt 2) :
    affDim (voronoiList V [u0, u1]) = 2 := by
  classical
  set S : Set V3 := voronoiList V [u0, u1] with hSdef
  set p : V3 := u0 + (2:ℝ)⁻¹ • (u1 - u0) with hpdef
  set d : ℝ := dist u0 u1 with hddef
  have hdpos : (0:ℝ) ≤ d := dist_nonneg
  have hdlt : d < 2 * Real.sqrt 2 := by rw [HL_2] at hhl; linarith
  have hmid0 : p - u0 = (2:ℝ)⁻¹ • (u1 - u0) := by rw [hpdef]; module
  have hmid1 : p - u1 = -((2:ℝ)⁻¹ • (u1 - u0)) := by rw [hpdef]; module
  have hpu0 : ‖p - u0‖ = d / 2 := by
    rw [hmid0, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show (0:ℝ) < (2:ℝ)⁻¹ by norm_num), ← dist_eq_norm, dist_comm u1 u0,
      hddef]
    ring
  have hpu1 : ‖p - u1‖ = d / 2 := by
    rw [hmid1, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show (0:ℝ) < (2:ℝ)⁻¹ by norm_num), ← dist_eq_norm, dist_comm u1 u0,
      hddef]
    ring
  -- direction space `D` of the bisector plane and its dimension
  set D : Submodule ℝ V3 := LinearMap.ker (p15_dotR (u1 - u0)) with hDdef
  have hD2 : Module.finrank ℝ D = 2 :=
    p15_finrank_ker_dot (a := u1 - u0) (sub_ne_zero.mpr (Ne.symm hne))
  have hDax : ∀ v ∈ D, (u1 - u0) ⬝ᵥ v = 0 := fun v hv => LinearMap.mem_ker.mp hv
  have hDmid0 : ∀ v ∈ D, inner ℝ (p - u0) v = 0 := by
    intro v hv
    rw [hmid0, p15_hsmL, inner_eq_dot, hDax v hv]
    ring
  have hDmid1 : ∀ v ∈ D, inner ℝ (p - u1) v = 0 := by
    intro v hv
    rw [hmid1, inner_neg_left, p15_hsmL, inner_eq_dot, hDax v hv]
    ring
  -- the margin scale `s` and patch radius `R`
  set d2 : ℝ := d / 2 with hd2def
  have hd2pos : (0:ℝ) ≤ d2 := by positivity
  have hsqd : d ^ 2 < 8 := by
    have h4 : (0:ℝ) ≤ 2 * Real.sqrt 2 := by positivity
    have hsq1 : d ^ 2 < (2 * Real.sqrt 2) ^ 2 := by
      nlinarith [hdlt, hdpos, h4]
    have h82 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)]
      norm_num
    rw [h82] at hsq1
    exact hsq1
  have hd2sq : d2 ^ 2 < 2 := by nlinarith
  set s : ℝ := Real.sqrt (4 - d2 ^ 2) with hsdef
  have hsnn : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have h4pos : (0:ℝ) ≤ 4 - d2 ^ 2 := by linarith
  have hsd2 : d2 < s := by
    have h1 : d2 ^ 2 < s ^ 2 := by
      rw [hsdef, Real.sq_sqrt h4pos]
      nlinarith
    by_contra hcon
    have h2 : s ^ 2 ≤ d2 ^ 2 := by nlinarith [hsnn, hd2pos, hcon]
    linarith
  set R : ℝ := (s - d2) / 8 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRkey : d2 + 2 * R ≤ s - 2 * R := by
    have h1 : 4 * R ≤ s - d2 := by rw [hRdef]; field_simp; linarith
    linarith
  -- margin: every other packing point sits outside the radius-`s` ball at `p`
  have hmargin : ∀ w ∈ V, w ≠ u0 → w ≠ u1 → s ≤ ‖w - p‖ := by
    intro w hw hw0 hw1
    have hsep0 : (2:ℝ) ≤ ‖w - u0‖ := by
      have h := hp.dist_ge_two hw hu0 hw0
      rwa [dist_eq_norm] at h
    have hsep1 : (2:ℝ) ≤ ‖w - u1‖ := by
      have h := hp.dist_ge_two hw hu1 hw1
      rwa [dist_eq_norm] at h
    have hsplit0 : ‖w - u0‖ ^ 2 = ‖w - p‖ ^ 2 + 2 * inner ℝ (w - p) (p - u0)
        + ‖p - u0‖ ^ 2 := by
      rw [show (w - u0 : V3) = (w - p) + (p - u0) from by abel, norm_add_sq_real]
    have hsplit1 : ‖w - u1‖ ^ 2 = ‖w - p‖ ^ 2 + 2 * inner ℝ (w - p) (p - u1)
        + ‖p - u1‖ ^ 2 := by
      rw [show (w - u1 : V3) = (w - p) + (p - u1) from by abel, norm_add_sq_real]
    have hcross : inner ℝ (w - p) (p - u0) + inner ℝ (w - p) (p - u1) = 0 := by
      have hsum : (p - u0) + (p - u1) = 0 := by rw [hmid0, hmid1]; abel
      have hadd : inner ℝ (w - p) ((p - u0) + (p - u1))
          = inner ℝ (w - p) (p - u0) + inner ℝ (w - p) (p - u1) :=
        inner_add_right _ _ _
      rw [hsum] at hadd
      have hz : inner ℝ (w - p) (0:V3) = 0 := inner_zero_right _
      rw [hz] at hadd
      linarith
    rw [hpu0] at hsplit0
    rw [hpu1] at hsplit1
    have h4u0 : (4:ℝ) ≤ ‖w - u0‖ ^ 2 := by
      nlinarith [sq_nonneg (‖w - u0‖ - 2)]
    have h4u1 : (4:ℝ) ≤ ‖w - u1‖ ^ 2 := by
      nlinarith [sq_nonneg (‖w - u1‖ - 2)]
    have hpara : ‖w - u0‖ ^ 2 + ‖w - u1‖ ^ 2 = 2 * ‖w - p‖ ^ 2 + 2 * d2 ^ 2 := by
      rw [hsplit0, hsplit1]
      nlinarith
    have hsq : s ^ 2 ≤ ‖w - p‖ ^ 2 := by
      rw [hsdef, Real.sq_sqrt h4pos]
      nlinarith
    have h1 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsnn, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)] at h1
    exact h1
  -- the pair-cell set form
  have hpair : S = voronoiClosed V u1 ∩ voronoiClosed V u0 := by
    rw [hSdef]
    show voronoiSet V (setOfList [u0, u1]) = _
    rw [show (setOfList [u0, u1] : Set V3) = {u0, u1} from by
      ext x; simp [setOfList], VORONOI_SET_2]
  -- distances from patch points to the pair endpoints
  have hdu1 : ∀ v ∈ D, ‖(p + v) - u1‖ ≤ d2 + ‖v‖ := by
    intro v hv
    rw [show ((p + v) - u1 : V3) = (p - u1) + v from by abel]
    exact le_trans (norm_add_le _ _) (by rw [hpu1])
  have hdu0 : ∀ v ∈ D, ‖(p + v) - u0‖ ≤ d2 + ‖v‖ := by
    intro v hv
    rw [show ((p + v) - u0 : V3) = (p - u0) + v from by abel]
    exact le_trans (norm_add_le _ _) (by rw [hpu0])
  have hdeq : ∀ v ∈ D, ‖(p + v) - u0‖ = ‖(p + v) - u1‖ := by
    intro v hv
    have hq0 : ‖(p + v) - u0‖ ^ 2 = d2 ^ 2 + ‖v‖ ^ 2 := by
      rw [show ((p + v) - u0 : V3) = (p - u0) + v from by abel,
        p15_pythI (hDmid0 v hv), hpu0]
    have hq1 : ‖(p + v) - u1‖ ^ 2 = d2 ^ 2 + ‖v‖ ^ 2 := by
      rw [show ((p + v) - u1 : V3) = (p - u1) + v from by abel,
        p15_pythI (hDmid1 v hv), hpu1]
    have hsqeq : ‖(p + v) - u0‖ ^ 2 = ‖(p + v) - u1‖ ^ 2 := by rw [hq0, hq1]
    have h1 : Real.sqrt (‖(p + v) - u0‖ ^ 2) = Real.sqrt (‖(p + v) - u1‖ ^ 2) := by
      rw [hsqeq]
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (norm_nonneg _)] at h1
  -- membership of the patch in the pair cell
  have hmem : ∀ v ∈ D, ‖v‖ ≤ 2 * R → p + v ∈ S := by
    intro v hv hvR
    rw [hpair]
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · -- the cell of `u1`
      show dist (p + v) u1 ≤ dist (p + v) w
      rcases eq_or_ne w u1 with rfl | hw1
      · exact le_refl _
      rcases eq_or_ne w u0 with rfl | hw0
      · have he := hdeq v hv
        rw [← dist_eq_norm, ← dist_eq_norm] at he
        rw [he]
      · have h1 := hdu1 v hv
        have h3 := dist_triangle w (p + v) p
        have h4 : dist (p + v) p = ‖v‖ := by
          rw [dist_eq_norm]; congr 1; abel
        have h5 : dist w p = ‖w - p‖ := dist_eq_norm w p
        rw [h4, h5] at h3
        have h6 := hmargin w hw hw0 hw1
        have h7 : dist w (p + v) = ‖(p + v) - w‖ := by
          rw [dist_comm, dist_eq_norm]
        rw [h7] at h3
        rw [dist_eq_norm, dist_eq_norm]
        linarith
    · -- the cell of `u0`
      show dist (p + v) u0 ≤ dist (p + v) w
      rcases eq_or_ne w u1 with rfl | hw1
      · have he := hdeq v hv
        rw [← dist_eq_norm, ← dist_eq_norm] at he
        rw [he]
      rcases eq_or_ne w u0 with rfl | hw0
      · exact le_refl _
      · have h1 := hdu0 v hv
        have h3 := dist_triangle w (p + v) p
        have h4 : dist (p + v) p = ‖v‖ := by
          rw [dist_eq_norm]; congr 1; abel
        have h5 : dist w p = ‖w - p‖ := dist_eq_norm w p
        rw [h4, h5] at h3
        have h6 := hmargin w hw hw0 hw1
        have h7 : dist w (p + v) = ‖(p + v) - w‖ := by
          rw [dist_comm, dist_eq_norm]
        rw [h7] at h3
        rw [dist_eq_norm, dist_eq_norm]
        linarith
  -- pick two independent directions, scaled into the patch
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h] at hD2
    simp at hD2
  obtain ⟨v1, hv1D, hv1ne⟩ : ∃ v ∈ D, v ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ v ∈ D, v = 0 := fun v hv => by
      by_contra hh
      exact hcon ⟨v, hv, hh⟩
    refine hDne (Submodule.ext fun x => ?_)
    constructor
    · intro hx
      have hx0 : x = 0 := hcon' x hx
      rw [hx0]
      exact (Submodule.mem_bot (R := ℝ)).2 rfl
    · intro hx
      rw [Submodule.mem_bot] at hx
      exact hx.symm ▸ Submodule.zero_mem D
  have hv1pos : 0 < ‖v1‖ := norm_pos_iff.mpr hv1ne
  have hD1 : (Submodule.span ℝ {v1}) ≤ D := Submodule.span_le.2
    (Set.singleton_subset_iff.2 hv1D)
  have hfr1 : Module.finrank ℝ (Submodule.span ℝ {v1}) = 1 := finrank_span_singleton hv1ne
  have hDne1 : D ≠ (Submodule.span ℝ {v1}) := by
    intro h
    rw [h, hfr1] at hD2
    simp at hD2
  obtain ⟨v2, hv2D, hv2s⟩ : ∃ v2 ∈ D, v2 ∉ (Submodule.span ℝ {v1}) := by
    by_contra hcon
    have hcon' : ∀ v ∈ D, v ∈ (Submodule.span ℝ {v1}) := fun v hv => by
      by_contra hh
      exact hcon ⟨v, hv, hh⟩
    refine hDne1 (Submodule.ext fun x => ?_)
    exact ⟨fun hx => hcon' x hx, fun hx => hD1 hx⟩
  have hv2ne : v2 ≠ 0 := by
    intro h
    apply hv2s
    rw [h]
    exact Submodule.mem_span_singleton.2 ⟨0, by simp⟩
  have hv2pos : 0 < ‖v2‖ := norm_pos_iff.mpr hv2ne
  set c1 : ℝ := R / ‖v1‖ with hc1def
  set c2 : ℝ := R / ‖v2‖ with hc2def
  have hc1pos : 0 < c1 := by rw [hc1def]; positivity
  have hc2pos : 0 < c2 := by rw [hc2def]; positivity
  set w1 : V3 := c1 • v1 with hw1def
  set w2 : V3 := c2 • v2 with hw2def
  have hw1D : w1 ∈ D := Submodule.smul_mem _ _ hv1D
  have hw2D : w2 ∈ D := Submodule.smul_mem _ _ hv2D
  have hw1n : ‖w1‖ = R := by
    rw [hw1def, norm_smul, Real.norm_eq_abs, abs_of_pos hc1pos, hc1def]
    field_simp
  have hw2n : ‖w2‖ = R := by
    rw [hw2def, norm_smul, Real.norm_eq_abs, abs_of_pos hc2pos, hc2def]
    field_simp
  have hw1ne : w1 ≠ 0 := by
    intro h
    rw [hw1def] at h
    exact hv1ne (smul_right_injective V3 (ne_of_gt hc1pos)
      (show (c1:ℝ) • v1 = c1 • 0 from by rw [h]; simp))
  have hw2ne : w2 ≠ 0 := by
    intro h
    rw [hw2def] at h
    exact hv2ne (smul_right_injective V3 (ne_of_gt hc2pos)
      (show (c2:ℝ) • v2 = c2 • 0 from by rw [h]; simp))
  have hspanw1 : Submodule.span ℝ {w1} = Submodule.span ℝ {v1} := by
    rw [hw1def, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (ne_of_gt hc1pos))]
  have hw2n1 : w2 ∉ Submodule.span ℝ {w1} := by
    rw [hspanw1, hw2def]
    intro hcon
    rcases Submodule.mem_span_singleton.mp hcon with ⟨t, ht⟩
    refine hv2s (Submodule.mem_span_singleton.2 ⟨t / c2, ?_⟩)
    refine (smul_right_injective V3 (ne_of_gt hc2pos)) ?_
    show c2 • ((t / c2) • v1) = c2 • v2
    rw [smul_smul]
    have hrat : c2 * (t / c2) = t := by field_simp
    rw [hrat, ht]
  -- the three patch points
  set z1 : V3 := p + w1 with hz1def
  set z2 : V3 := p + w2 with hz2def
  set z3 : V3 := p + (w1 + w2) with hz3def
  have hz1S : z1 ∈ S := hmem w1 hw1D (by rw [hw1n]; linarith)
  have hz2S : z2 ∈ S := hmem w2 hw2D (by rw [hw2n]; linarith)
  have hz3S : z3 ∈ S := hmem (w1 + w2) (Submodule.add_mem _ hw1D hw2D)
    (by have := norm_add_le w1 w2; rw [hw1n, hw2n] at this; linarith)
  -- linear independence of the two scaled directions
  have hli : LinearIndependent ℝ ![w1, w2] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    fin_cases i
    · by_contra hg0
      rcases eq_or_ne (g 1) 0 with hg1 | hg1
      · rw [hg1, zero_smul, add_zero] at hg
        exact hg0 ((smul_eq_zero.mp hg).resolve_right hw1ne)
      · apply hw2n1
        refine Submodule.mem_span_singleton.2 ⟨-g 0 / g 1, ?_⟩
        have hkey : g 1 • ((-g 0 / g 1) • w1) = g 1 • w2 := by
          rw [smul_smul]
          have hrat : g 1 * (-g 0 / g 1) = -g 0 := by field_simp
          rw [hrat, neg_smul, neg_eq_iff_add_eq_zero]
          exact hg
        exact smul_right_injective V3 hg1 hkey
    · by_contra hg1
      rcases eq_or_ne (g 0) 0 with hg0 | hg0
      · rw [hg0, zero_smul, zero_add] at hg
        exact hg1 ((smul_eq_zero.mp hg).resolve_right hw2ne)
      · apply hw2n1
        have hkey : g 0 • ((-g 1 / g 0) • w2) = g 0 • w1 := by
          rw [smul_smul]
          have hrat : g 0 * (-g 1 / g 0) = -g 1 := by field_simp
          rw [hrat, neg_smul, neg_eq_iff_add_eq_zero, add_comm]
          exact hg
        have hwt : w1 = (-g 1 / g 0) • w2 :=
          smul_right_injective V3 hg0 (by
            show g 0 • w1 = g 0 • ((-g 1 / g 0) • w2)
            rw [hkey])
        refine Submodule.mem_span_singleton.2 ⟨1 / (-g 1 / g 0), ?_⟩
        rw [hwt, smul_smul]
        have hng : (-g 1 / g 0) ≠ 0 :=
          div_ne_zero (neg_ne_zero.2 hg1) hg0
        have hrat : (1 / (-g 1 / g 0)) * (-g 1 / g 0) = 1 := by
          field_simp
          exact div_self hg1
        rw [hrat, one_smul]
  -- the span of the two directions sits inside the vectorSpan of the cell
  have hsuble : (Submodule.span ℝ {w1, w2}) ≤ vectorSpan ℝ S := by
    rw [vectorSpan_def, Submodule.span_le]
    intro t ht
    have hw1in : w1 ∈ (vectorSpan ℝ S : Set V3) :=
      Submodule.subset_span (Set.mem_vsub.2 ⟨z3, hz3S, z2, hz2S, by
        show z3 -ᵥ z2 = w1
        rw [vsub_eq_sub, hz3def, hz2def]
        abel⟩)
    have hw1w2 : w1 - w2 ∈ (vectorSpan ℝ S : Set V3) :=
      Submodule.subset_span (Set.mem_vsub.2 ⟨z1, hz1S, z2, hz2S, by
        show z1 -ᵥ z2 = w1 - w2
        rw [vsub_eq_sub, hz1def, hz2def]
        abel⟩)
    have hw2in : w2 ∈ (vectorSpan ℝ S : Set V3) := by
      have hsub := Submodule.sub_mem (vectorSpan ℝ S) hw1in hw1w2
      rwa [show (w1 - (w1 - w2) : V3) = w2 from by abel] at hsub
    rcases Set.mem_insert_iff.mp ht with rfl | rfl
    · exact hw1in
    · exact hw2in
  have hfrS : (2:ℕ) ≤ Module.finrank ℝ (vectorSpan ℝ S) := by
    have h1 := Submodule.finrank_mono hsuble
    have hrange : Set.range ![w1, w2] = {w1, w2} := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
    have h2 : Module.finrank ℝ (Submodule.span ℝ {w1, w2}) = 2 := by
      rw [show (Submodule.span ℝ {w1, w2}) = Submodule.span ℝ
        (Set.range ![w1, w2]) from by rw [hrange], finrank_span_eq_card hli]
      norm_num
    rw [h2] at h1
    exact h1
  -- conclusion
  have hneS : S.Nonempty := ⟨z1, hz1S⟩
  have hSsub : S ⊆ bis u0 u1 := by
    intro x hx
    rw [hpair] at hx
    rw [bis, Set.mem_setOf_eq]
    exact le_antisymm (hx.2 u1 hu1) (hx.1 u0 hu0)
  have hd_le : affDim S ≤ 2 := by
    refine le_trans (affDim_mono hSsub hneS) ?_
    exact le_of_eq (p15_affDim_bis_pair hne)
  have hd_ge : (2:ℤ) ≤ affDim S := by
    rw [affDim, if_neg (Set.nonempty_iff_ne_empty.mp hneS)]
    norm_cast
  exact le_antisymm hd_le hd_ge

/- PA15-private transcription of PackingAuto24's `p24_barV1` support chain
(`HL_LE_SQRT2_IMP_BARV_1`, marchal3.hl:1054; PA24 holds the first genuine
copy but cannot be imported here — `Kepler.Text.wedge` clash, PA24:263 note).
All helpers verbatim; `HL_2` (this file, public) plays the role of PA24's
`p24_hl_pair`. -/

/-- marchal3.hl:1054 `HL_LE_SQRT2_IMP_BARV_1`. -/
theorem HL_LE_SQRT2_IMP_BARV_1 (V : Set V3) (u0 u1 : V3) (hs : saturated V) (hp : Packing V)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1) (h : hl [u0, u1] < Real.sqrt 2) :
    barV V 1 [u0, u1] := by
  refine ⟨by norm_num, ?_⟩
  rintro vl ⟨⟨yl, hyl⟩, hpos⟩
  cases vl with
  | nil => exact absurd hpos (by simp)
  | cons a tl =>
    have hcon : u0 = a ∧ [u1] = tl ++ yl := List.cons.inj hyl
    have ha : a = u0 := hcon.1.symm
    cases tl with
    | nil =>
      have hy1 : yl = [u1] := by
        simpa using hcon.2.symm
      rw [ha]
      refine ⟨by norm_num, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hu0
        · exact absurd hx' (by simp)
      · have hsing : voronoiList V [u0] = voronoiClosed V u0 := by
          show voronoiSet V (setOfList [u0]) = _
          rw [show (setOfList [u0] : Set V3) = {u0} from by
            ext x; simp [setOfList], VORONOI_SET_SING]
        rw [hsing, AFF_DIM_VORONOI_CLOSED V u0 hp]
        norm_num
    | cons b tl2 =>
      have hcon2 : u1 = b ∧ [] = tl2 ++ yl := List.cons.inj hcon.2
      have hb : b = u1 := hcon2.1.symm
      have htl2 : tl2 = [] := by
        cases tl2 with
        | nil => rfl
        | cons c tl3 => exact absurd hcon2.2 (by simp)
      rw [ha, hb, htl2]
      refine ⟨by norm_num, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hu0
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact hu1
        · exact absurd hx' (by simp)
      · have h2 := p15_affDim_voronoiList2 V u0 u1 hp hu0 hu1 hne h
        rw [h2]
        norm_num

/-! ## marchal3.hl:1142-1330: cone/boundedness/division kit -/

/-- marchal3.hl:1142 `RCONE_GT_SUBSET`. -/
theorem RCONE_GT_SUBSET (u0 u1 : V3) (a b : ℝ) (h : a ≤ b) :
    rconeGt u0 u1 b ⊆ rconeGt u0 u1 a := by
  intro x hx
  simp only [rconeGt, Set.mem_setOf_eq] at hx ⊢
  have h1 : dist x u0 * dist u1 u0 * a ≤ dist x u0 * dist u1 u0 * b :=
    mul_le_mul_of_nonneg_left h (by positivity)
  exact lt_of_le_of_lt h1 hx

/-- marchal3.hl:1164 `BOUNDED_SING` (HOL is over `real^N`; V3 is all this
chapter needs). -/
theorem BOUNDED_SING (a : V3) : Bornology.IsBounded ({a} : Set V3) :=
  Bornology.isBounded_singleton


/-! ## marchal3.hl:1168-1300: subspace / dihedral / division kit -/

/-- marchal3.hl:1168 `SUBSPACE_BOUNDED_EQ_TRIVIAL` (HOL `real^N`). -/
theorem SUBSPACE_BOUNDED_EQ_TRIVIAL (s : Submodule ℝ V3) :
    Bornology.IsBounded (s : Set V3) ↔ (s : Set V3) = {0} := by
  constructor
  · intro hb
    by_contra hne
    have hx0 : ∃ x ∈ (s : Set V3), x ≠ 0 := by
      by_contra hall
      push_neg at hall
      refine hne ?_
      ext x
      simp only [Set.mem_singleton_iff]
      refine ⟨fun hx => hall x hx, fun hx => ?_⟩
      rw [hx]
      exact Submodule.zero_mem s
    obtain ⟨x, hx, hxne⟩ := hx0
    obtain ⟨r, hrb⟩ := (Metric.isBounded_iff_subset_ball 0).mp hb
    have hrpos : (0:ℝ) < r := by
      have := Metric.mem_ball.mp (hrb hx)
      have : (0:ℝ) < dist x 0 := by
        rw [dist_eq_norm, sub_zero]
        exact norm_pos_iff.mpr hxne
      linarith
    have hxin : (((r + 1) / norm x) • x : V3) ∈ (s : Set V3) :=
      SetLike.mem_coe.mpr (Submodule.smul_mem s _ hx)
    have hlt : dist (((r + 1) / norm x) • x) (0:V3) < r :=
      Metric.mem_ball.mp (hrb hxin)
    have hnorm : dist (((r + 1) / norm x) • x) (0:V3) = r + 1 := by
      rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (by linarith) (norm_nonneg x)),
        div_mul_eq_mul_div]
      have hxne' : norm x ≠ 0 := ne_of_gt (norm_pos_iff.mpr hxne)
      field_simp
    rw [hnorm] at hlt
    linarith
  · intro h
    rw [h]
    exact Bornology.isBounded_singleton

/-- marchal3.hl:1220 `DIHV_SYM_2`. -/
theorem DIHV_SYM_2 (x y z t : V3) : dihV x y z t = dihV x y t z := by
  unfold dihV
  exact p15_arcV_sym 0 _ _

/-- marchal3.hl:1229 `REAL_DIV_LE_1_TACTICS`. -/
theorem REAL_DIV_LE_1_TACTICS (m n : ℝ) (hn : 0 < n) (h : m ≤ n) : m / n ≤ 1 :=
  (div_le_one hn).mpr h

/-- marchal3.hl:1244 `REAL_DIV_LT_1_TACTICS`. -/
theorem REAL_DIV_LT_1_TACTICS (m n : ℝ) (hn : 0 < n) (h : m < n) : m / n < 1 :=
  (div_lt_one hn).mpr h

/-! ## marchal3.hl:1264-2300: cell rigidity (skeletons) -/

/-! ## Private helpers: finite index permutations (copied from PA14 private kit) -/

private noncomputable def p15_natEquiv (n : ℕ) : Fin n ⊕ ℕ ≃ ℕ :=
  Equiv.ofBijective
    (Sum.elim (fun i : Fin n => (i : ℕ)) (fun k : ℕ => n + k)) <| by
    constructor
    · intro a b h
      cases a with
      | inl i =>
        cases b with
        | inl j =>
          simp only [Sum.elim_inl, Fin.val_eq_val] at h
          exact congrArg Sum.inl h
        | inr j =>
          simp only [Sum.elim_inl, Sum.elim_inr] at h
          have hi : (i : ℕ) < n := i.isLt
          omega
      | inr i =>
        cases b with
        | inl j =>
          simp only [Sum.elim_inl, Sum.elim_inr] at h
          have hj : (j : ℕ) < n := j.isLt
          omega
        | inr j =>
          simp only [Sum.elim_inr] at h
          exact congrArg Sum.inr (Nat.add_left_cancel h)
    · intro m
      by_cases hm : m < n
      · exact ⟨Sum.inl ⟨m, hm⟩, by simp [Sum.elim]⟩
      · exact ⟨Sum.inr (m - n), by simp [Sum.elim]; omega⟩

private theorem p15_natEquiv_apply_inl (n : ℕ) (i : Fin n) :
    p15_natEquiv n (Sum.inl i) = (i : ℕ) := rfl

private theorem p15_natEquiv_apply_inr (n : ℕ) (k : ℕ) :
    p15_natEquiv n (Sum.inr k) = n + k := rfl

private theorem p15_natEquiv_symm_apply_lt (n : ℕ) (i : Fin n) :
    (p15_natEquiv n).symm (i : ℕ) = Sum.inl i := by
  rw [← p15_natEquiv_apply_inl n i, Equiv.symm_apply_apply]

private theorem p15_natEquiv_symm_apply_ge (n : ℕ) {j : ℕ} (hj : n ≤ j) :
    (p15_natEquiv n).symm j = Sum.inr (j - n) := by
  have h : p15_natEquiv n (Sum.inr (j - n)) = j := by
    rw [p15_natEquiv_apply_inr, Nat.add_sub_cancel' hj]
  calc (p15_natEquiv n).symm j
      = (p15_natEquiv n).symm (p15_natEquiv n (Sum.inr (j - n))) := by rw [h]
    _ = Sum.inr (j - n) := Equiv.symm_apply_apply _ _

private noncomputable def p15_natPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm ℕ :=
  ((p15_natEquiv n).symm.trans (σ.sumCongr (Equiv.refl ℕ))).trans (p15_natEquiv n)

private theorem p15_natPerm_apply_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    p15_natPerm σ (i : ℕ) = (σ i : ℕ) := by
  rw [p15_natPerm, Equiv.trans_apply, Equiv.trans_apply, p15_natEquiv_symm_apply_lt,
    Equiv.sumCongr_apply, Sum.map_inl, p15_natEquiv_apply_inl]

private theorem p15_natPerm_apply_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {j : ℕ}
    (hj : n ≤ j) : p15_natPerm σ j = j := by
  rw [p15_natPerm, Equiv.trans_apply, Equiv.trans_apply, p15_natEquiv_symm_apply_ge n hj,
    Equiv.sumCongr_apply, Sum.map_inr, p15_natEquiv_apply_inr]
  simp only [Equiv.refl_apply]
  omega

private theorem p15_natPerm_permutes {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permutes (p15_natPerm σ) {j : ℕ | j < n} := by
  intro j
  constructor
  · intro hj
    have := p15_natPerm_apply_lt σ ⟨j, hj⟩
    rw [this]
    exact (σ ⟨j, hj⟩).isLt
  · intro hj
    by_contra hcon
    have hge : n ≤ j := Nat.le_of_not_lt hcon
    rw [p15_natPerm_apply_ge σ hge] at hj
    exact absurd hj (Nat.not_lt.mpr hge)

private theorem p15_Icc_eq_Iio (n : ℕ) (hn : 1 ≤ n) :
    Set.Icc 0 (n - 1) = {j : ℕ | j < n} := by
  ext j
  simp only [Set.mem_Icc, Set.mem_setOf_eq]
  omega

/-- Finitely many tail-fixing permutations of `0..n-1`. -/
private theorem p15_finite_tailfix_perms (n : ℕ) (hn : 1 ≤ n) :
    {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (n - 1)) ∧ ∀ j : ℕ, n ≤ j → p j = j}.Finite := by
  have hIcc : Set.Icc 0 (n - 1) = {j : ℕ | j < n} := p15_Icc_eq_Iio n hn
  have hsub : {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (n - 1)) ∧
      ∀ j : ℕ, n ≤ j → p j = j} ⊆
      Set.range (fun σ : Equiv.Perm (Fin n) => p15_natPerm σ) := by
    rintro p ⟨hp, hfix⟩
    have hp' : permutes p {j : ℕ | j < n} := by rw [← hIcc]; exact hp
    -- the induced permutation of Fin n
    let f : Fin n → Fin n := fun i => ⟨p i, (hp' i).1 i.isLt⟩
    have hinj : Function.Injective f := by
      intro a b h
      apply Fin.ext
      have := congrArg Fin.val h
      simpa [f] using p.injective (Fin.ext_iff.mp h)
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    have hσ : ∀ i : Fin n, (σ i : ℕ) = p i := fun i => rfl
    refine ⟨σ, ?_⟩
    apply Equiv.ext
    intro j
    by_cases hj : j < n
    · have h1 : p15_natPerm σ j = (σ ⟨j, hj⟩ : ℕ) := p15_natPerm_apply_lt σ ⟨j, hj⟩
      rw [h1]
      exact hσ ⟨j, hj⟩
    · have hge : n ≤ j := Nat.le_of_not_lt hj
      rw [p15_natPerm_apply_ge σ hge, hfix j hge]
  exact Set.Finite.subset (Set.finite_range _) hsub




private theorem p15_finrank_span_pair_le_two (a b : V3) :
    Module.finrank ℝ (Submodule.span ℝ ({a, b} : Set V3)) ≤ 2 := by
  have h2 := finrank_span_finset_le_card (R := ℝ) ({a, b} : Finset V3)
  unfold Set.finrank at h2
  rw [show (({a, b} : Finset V3) : Set V3) = ({a, b} : Set V3) from by simp] at h2
  refine h2.trans ?_
  calc ({a, b} : Finset V3).card ≤ ({b} : Finset V3).card + 1 := Finset.card_insert_le a {b}
    _ = 2 := by simp

private theorem p15_coplanar_null {s t : Set V3} (hcop : Coplanar s) (hsub : t ⊆ s) :
    volume t = 0 := by
  obtain ⟨u, v, w, hsp⟩ := hcop
  have hvs : vectorSpan ℝ ({u, v, w} : Set V3)
      = Submodule.span ℝ ({v - u, w - u} : Set V3) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (show u ∈ ({u, v, w} : Set V3) from by simp)]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨q, hq, rfl⟩
      rcases hq with rfl | rfl | rfl
      · simp
      · exact Submodule.subset_span (by left; rfl)
      · exact Submodule.subset_span (by right; rfl)
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact Submodule.subset_span ⟨v, by simp, rfl⟩
      · exact Submodule.subset_span ⟨w, by simp, rfl⟩
  have hne : (affineSpan ℝ ({u, v, w} : Set V3) : AffineSubspace ℝ V3) ≠ ⊤ := by
    intro htop
    have hdir : (affineSpan ℝ ({u, v, w} : Set V3)).direction = ⊤ := by
      rw [htop]; exact AffineSubspace.direction_top ℝ V3 V3
    have hle : Module.finrank ℝ (affineSpan ℝ ({u, v, w} : Set V3)).direction ≤ 2 := by
      rw [direction_affineSpan, hvs]
      exact p15_finrank_span_pair_le_two (v - u) (w - u)
    rw [hdir, finrank_top] at hle
    exact absurd hle (by norm_num)
  exact measure_mono_null (hsub.trans hsp)
    (Measure.addHaar_affineSubspace volume _ hne)

private theorem p15_sUnion_null {fam : Set (Set V3)} (hfin : fam.Finite)
    (h : ∀ T ∈ fam, volume T = 0) : volume (⋃₀ fam) = 0 := by
  have hle : volume (⋃₀ fam) ≤ ∑ T ∈ Set.Finite.toFinset hfin, volume T := by
    refine le_trans (measure_mono ?_) (measure_biUnion_finset_le _ _)
    intro x hx
    obtain ⟨T, hT, hxT⟩ := Set.mem_sUnion.1 hx
    exact Set.mem_biUnion (by simpa using hT) hxT
  rw [Finset.sum_eq_zero (fun T hT => h T (by simpa using hT))] at hle
  simpa using le_antisymm hle zero_le

private theorem p15_pick_pos {X : Set V3} {fam : Set (Set V3)}
    (hcover : X ⊆ ⋃₀ fam) (hfin : fam.Finite) (hpos : 0 < volume X) :
    ∃ T ∈ fam, 0 < volume T := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ T ∈ fam, volume T = 0 := fun T hT =>
    le_antisymm (hcon T hT) zero_le
  have h1 : volume X ≤ 0 := (measure_mono hcover).trans_eq (p15_sUnion_null hfin hzero)
  have h2 : volume X = 0 := le_antisymm h1 zero_le
  exact absurd h2 (ne_of_gt hpos)

private theorem p15_volPosLtAffDim3 (S : Set V3) (hs : MeasurableSet S)
    (hv : 0 < volume S) : affDim S = 3 := by
  rcases Set.eq_empty_or_nonempty S with rfl | hne
  · rw [measure_empty] at hv
    exact absurd hv (by norm_num)
  · by_contra hcon
    have hne' : S ≠ ∅ := (Set.nonempty_iff_ne_empty).mp hne
    have hfr : (Module.finrank ℝ (vectorSpan ℝ S) : ℤ) = affDim S := by
      rw [affDim, if_neg hne']
    have hV3 : Module.finrank ℝ V3 = 3 := finrank_euclideanSpace_fin
    have hle : Module.finrank ℝ (vectorSpan ℝ S) ≤ 3 := by
      simpa [hV3] using Submodule.finrank_le (vectorSpan ℝ S)
    rcases Nat.lt_or_ge (Module.finrank ℝ (vectorSpan ℝ S)) 3 with hlt' | h3
    · have htop : (vectorSpan ℝ S : Submodule ℝ V3) ≠ ⊤ := by
        intro htop
        rw [htop] at hlt'
        simp [finrank_top, hV3] at hlt'
      have htop_aff : (affineSpan ℝ S : AffineSubspace ℝ V3) ≠ ⊤ := by
        intro hE
        exact htop (AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ V3 V3 hE)
      have h0 : volume ((affineSpan ℝ S : AffineSubspace ℝ V3) : Set V3) = 0 :=
        MeasureTheory.Measure.addHaar_affineSubspace volume (affineSpan ℝ S) htop_aff
      have hmono : volume S ≤ volume ((affineSpan ℝ S : AffineSubspace ℝ V3) : Set V3) :=
        measure_mono (subset_affineSpan ℝ S)
      rw [h0] at hmono
      exact absurd hmono (not_le.mpr hv)
    · exact hcon (by rw [← hfr]; exact_mod_cast le_antisymm hle h3)

/-- Common-permutation Rogers simplex extracted from a non-null cell. -/
private theorem p15_rogers_common (V : Set V3) (i : ℕ) (ul vl : List V3)
    (hp : Packing V) (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (hcell : mcell i V ul = mcell i V vl) (hnull : ¬nullSet (mcell i V ul))
    (hi : i ∈ ({2, 3, 4} : Set ℕ)) :
    ∃ p q : Equiv.Perm ℕ,
      permutes p (Set.Icc 0 (i - 1)) ∧ (∀ n : ℕ, i ≤ n → p n = n) ∧
      permutes q (Set.Icc 0 (i - 1)) ∧ (∀ n : ℕ, i ≤ n → q n = n) ∧
      barV V 3 (leftActionList p ul) ∧ barV V 3 (leftActionList q vl) ∧
      rogers V (leftActionList p ul) = rogers V (leftActionList q vl) ∧
      affDim (rogers V (leftActionList p ul)) = 3 := by
  have hi4 : i ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
    omega
  have hpos : 0 < volume (mcell i V ul) :=
    lt_of_le_of_ne zero_le (Ne.symm hnull)
  have hne : mcell i V ul ≠ ∅ := by
    intro hc; exact hnull (by rw [hc]; exact measure_empty)
  have hne' : mcell i V vl ≠ ∅ := by
    intro hc; exact hne (by rw [hcell]; exact hc)
  -- finiteness of the two tail-fixing permutation families
  have hPfinu : {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (i - 1)) ∧
      ∀ j : ℕ, i ≤ j → p j = j}.Finite :=
    p15_finite_tailfix_perms i (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega)
  have hfamu : ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p ul)) ''
      {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (i - 1)) ∧
        ∀ j : ℕ, i ≤ j → p j = j}).Finite := hPfinu.image _
  have hfamv : ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p vl)) ''
      {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (i - 1)) ∧
        ∀ j : ℕ, i ≤ j → p j = j}).Finite := hPfinu.image _
  -- coverage on the ul side
  have hcovu := QZKSYKG2 (V := V) (ul := ul) (k := i) hs hp hul hi4
  have hcovu' : mcell i V ul ⊆
      ⋃₀ ((fun R : Set V3 => mcell i V ul ∩ R) ''
        ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p ul)) ''
          {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (i - 1)) ∧
            ∀ j : ℕ, i ≤ j → p j = j})) := by
    intro x hx
    obtain ⟨R, hR, hxR⟩ := Set.mem_sUnion.1 (hcovu hx)
    exact Set.mem_sUnion.2 ⟨mcell i V ul ∩ R, Set.mem_image_of_mem _ hR, ⟨hx, hxR⟩⟩
  have hfamu' : ((fun R : Set V3 => mcell i V ul ∩ R) ''
      ((fun p : Equiv.Perm ℕ => rogers V (leftActionList p ul)) ''
        {p : Equiv.Perm ℕ | permutes p (Set.Icc 0 (i - 1)) ∧
          ∀ j : ℕ, i ≤ j → p j = j})).Finite := hfamu.image _
  obtain ⟨S1, ⟨R_u, ⟨p, hpu, rfl⟩, hS1eq⟩, hS1pos⟩ :=
    p15_pick_pos hcovu' hfamu' hpos
  -- S1 = X ∩ R_u, positive measure
  have hS1subX : S1 ⊆ mcell i V ul := by rw [← hS1eq]; exact Set.inter_subset_left
  have hS1subR : S1 ⊆ rogers V (leftActionList p ul) := by rw [← hS1eq]; exact Set.inter_subset_right
  -- coverage on the vl side, restricted to S1
  have hcovv := QZKSYKG2 (V := V) (ul := vl) (k := i) hs hp hvl hi4
  have hcovv' : S1 ⊆
      ⋃₀ ((fun R : Set V3 => S1 ∩ R) ''
        ((fun q : Equiv.Perm ℕ => rogers V (leftActionList q vl)) ''
          {q : Equiv.Perm ℕ | permutes q (Set.Icc 0 (i - 1)) ∧
            ∀ j : ℕ, i ≤ j → q j = j})) := by
    intro x hx
    have hxX : x ∈ mcell i V vl := by rw [← hcell]; exact hS1subX hx
    obtain ⟨R, hR, hxR⟩ := Set.mem_sUnion.1 (hcovv hxX)
    exact Set.mem_sUnion.2 ⟨S1 ∩ R, Set.mem_image_of_mem _ hR, ⟨hx, hxR⟩⟩
  have hfamv' : ((fun R : Set V3 => S1 ∩ R) ''
      ((fun q : Equiv.Perm ℕ => rogers V (leftActionList q vl)) ''
        {q : Equiv.Perm ℕ | permutes q (Set.Icc 0 (i - 1)) ∧
          ∀ j : ℕ, i ≤ j → q j = j})).Finite := hfamv.image _
  obtain ⟨S2, ⟨R_v, ⟨q, hqv, rfl⟩, hS2eq⟩, hS2pos⟩ :=
    p15_pick_pos hcovv' hfamv' hS1pos
  -- barV persistence of the two permuted lists
  have hbaru : barV V 3 (leftActionList p ul) :=
    QZKSYKG1 hs hp hul hi4 hne hpu.1 hpu.2 rfl
  have hbarv : barV V 3 (leftActionList q vl) :=
    QZKSYKG1 hs hp hvl hi4 hne' hqv.1 hqv.2 rfl
  -- the two Rogers simplices must agree
  have hReq : rogers V (leftActionList p ul) = rogers V (leftActionList q vl) := by
    by_contra hneR
    have hcop : Coplanar (rogers V (leftActionList p ul) ∩
        rogers V (leftActionList q vl)) :=
      DUUNHOR V _ _ hp hs hbaru hbarv hneR
    have hsub2 : S2 ⊆ rogers V (leftActionList p ul) ∩ rogers V (leftActionList q vl) := by
      rw [← hS2eq]
      refine Set.subset_inter ?_ Set.inter_subset_right
      exact (Set.inter_subset_left).trans hS1subR
    have hzero : volume S2 = 0 := p15_coplanar_null hcop hsub2
    rw [hzero] at hS2pos
    exact absurd hS2pos (lt_irrefl 0)
  -- positive measure and dimension of the common Rogers simplex
  have hRpos : 0 < volume (rogers V (leftActionList p ul)) :=
    lt_of_lt_of_le hS1pos (measure_mono hS1subR)
  have hdim : affDim (rogers V (leftActionList p ul)) = 3 :=
    p15_volPosLtAffDim3 _ (MEASURABLE_ROGERS V _ hs hp hbaru) hRpos
  exact ⟨p, q, hpu.1, hpu.2, hqv.1, hqv.2, hbaru, hbarv, hReq, hdim⟩



/-- Main proof body for `MCELL_ID_OMEGA_LIST_N`. -/
private theorem p15_mcell_omega_main
    (V : Set V3) (i j : ℕ) (ul vl : List V3) (hp : Packing V)
    (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (heq : mcell i V ul = mcell j V vl) (hnel : ¬nullSet (mcell i V ul))
    (hi : i ∈ ({2, 3, 4} : Set ℕ)) (hj : j ∈ ({2, 3, 4} : Set ℕ)) :
    i = j ∧ ∀ k : ℕ, i - 1 ≤ k ∧ k ≤ 3 → omegaListN V ul k = omegaListN V vl k := by
  have hi4 : i ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
    omega
  have hj4 : j ∈ ({0, 1, 2, 3, 4} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj ⊢
    omega
  have hvol : ¬nullSet (mcell i V ul ∩ mcell j V vl) := by
    simpa [heq] using hnel
  obtain ⟨hij, hcell⟩ :=
    AJRIPQN V ul vl i j hs hp hul hvl hi4 hj4 hvol
  subst j
  refine ⟨rfl, ?_⟩
  have hne : mcell i V ul ≠ ∅ := by
    intro hc
    exact hnel (by rw [hc]; exact measure_empty)
  have hne' : mcell i V vl ≠ ∅ := by
    intro hc
    exact hne (by rw [hcell]; exact hc)
  -- branch conditions forced by non-nullness of the cell
  have hbr2u : i = 2 → hl (truncateSimplex 1 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul := by
    intro h2
    subst i
    by_contra hc
    have hE : mcell 2 V ul = ∅ := by
      rw [(MCELL_EXPLICIT 2 V ul).2.2.1]
      simp only [mcell2]
      rw [if_neg hc]
    exact hne hE
  have hbr3u : i = 3 → hl (truncateSimplex 2 ul) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl ul := by
    intro h3
    subst i
    by_contra hc
    have hE : mcell 3 V ul = ∅ := by
      rw [(MCELL_EXPLICIT 3 V ul).2.2.2.1]
      simp only [mcell3]
      rw [if_neg hc]
    exact hne hE
  have hbr4u : i = 4 → hl ul < Real.sqrt 2 := by
    intro h4
    subst i
    by_contra hc
    have hE : mcell 4 V ul = ∅ := by
      rw [(MCELL_EXPLICIT 4 V ul).2.2.2.2 (le_refl 4)]
      simp only [mcell4]
      rw [if_neg hc]
    exact hne hE
  have hbr2v : i = 2 → hl (truncateSimplex 1 vl) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl vl := by
    intro h2
    subst i
    by_contra hc
    have hE : mcell 2 V vl = ∅ := by
      rw [(MCELL_EXPLICIT 2 V vl).2.2.1]
      simp only [mcell2]
      rw [if_neg hc]
    exact hne' hE
  have hbr3v : i = 3 → hl (truncateSimplex 2 vl) < Real.sqrt 2 ∧ Real.sqrt 2 ≤ hl vl := by
    intro h3
    subst i
    by_contra hc
    have hE : mcell 3 V vl = ∅ := by
      rw [(MCELL_EXPLICIT 3 V vl).2.2.2.1]
      simp only [mcell3]
      rw [if_neg hc]
    exact hne' hE
  have hbr4v : i = 4 → hl vl < Real.sqrt 2 := by
    intro h4
    subst i
    by_contra hc
    have hE : mcell 4 V vl = ∅ := by
      rw [(MCELL_EXPLICIT 4 V vl).2.2.2.2 (le_refl 4)]
      simp only [mcell4]
      rw [if_neg hc]
    exact hne' hE
  -- common Rogers simplex for the two lists
  obtain ⟨p, q, hperm_p, hfix_p, hperm_q, hfix_q, hbar_p, hbar_q, hrog, hdim⟩ :=
    p15_rogers_common V i ul vl hp hs hul hvl hcell hnel hi
  have homegpq : ∀ k : ℕ, k ≤ 3 →
      omegaListN V (leftActionList p ul) k = omegaListN V (leftActionList q vl) k :=
    NJIUTIU V (leftActionList p ul) (leftActionList q vl) hs hp hbar_p hbar_q hrog hdim
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl | rfl
  · -- ===================== i = 2 =====================
    have hbru := hbr2u rfl
    have hbrv := hbr2v rfl
    have hperm_p' : permutes p ({0, 1} : Set ℕ) := by
      have hI : Set.Icc 0 (2 - 1) = ({0, 1} : Set ℕ) := by
        ext x
        simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      rwa [hI] at hperm_p
    have hperm_q' : permutes q ({0, 1} : Set ℕ) := by
      have hI : Set.Icc 0 (2 - 1) = ({0, 1} : Set ℕ) := by
        ext x
        simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
        omega
      rwa [hI] at hperm_q
    have hPu := LEFT_ACTION_LIST_1_PROPERTIES_ALT V ul (leftActionList p ul) p hp hs hul
      hperm_p' hfix_p hbru.1 hbru.2 rfl
    have hQv := LEFT_ACTION_LIST_1_PROPERTIES_ALT V vl (leftActionList q vl) q hp hs hvl
      hperm_q' hfix_q hbrv.1 hbrv.2 rfl
    intro k hk
    have hk1 : 1 ≤ k := by omega
    have hk3 : k ≤ 3 := hk.2
    interval_cases k
    · exact hPu.2.1.symm.trans ((homegpq 1 (by norm_num)).trans hQv.2.1)
    · exact hPu.2.2.1.symm.trans ((homegpq 2 (by norm_num)).trans hQv.2.2.1)
    · exact hPu.2.2.2.1.symm.trans ((homegpq 3 (by norm_num)).trans hQv.2.2.2.1)
  · -- ===================== i = 3 =====================
    have hbru := hbr3u rfl
    have hbrv := hbr3v rfl
    have hPu := ynhyjit_i3_p14 (V := V) (ul := ul) (vl := leftActionList p ul) (p := p)
      hs hp hul hbru.1 hbru.2 hperm_p hfix_p rfl
    have hQv := ynhyjit_i3_p14 (V := V) (ul := vl) (vl := leftActionList q vl) (p := q)
      hs hp hvl hbrv.1 hbrv.2 hperm_q hfix_q rfl
    intro k hk
    have hk2 : 2 ≤ k := by omega
    have hk3 : k ≤ 3 := hk.2
    interval_cases k
    · exact hPu.2 2 (by norm_num) (by norm_num) |>.symm.trans
        ((homegpq 2 (by norm_num)).trans (hQv.2 2 (by norm_num) (by norm_num)))
    · exact hPu.2 3 (by norm_num) (by norm_num) |>.symm.trans
        ((homegpq 3 (by norm_num)).trans (hQv.2 3 (by norm_num) (by norm_num)))
  · -- ===================== i = 4 =====================
    have hbru := hbr4u rfl
    have hbrv := hbr4v rfl
    have hlen_p : (leftActionList p ul).length = 4 := by
      simp [leftActionList, hul.1]
    have hlen_q : (leftActionList q vl).length = 4 := by
      simp [leftActionList, hvl.1]
    have hpermLen_p : permutes p {n : ℕ | n < ul.length} := by
      rw [hul.1]
      have hI : Set.Icc 0 (4 - 1) = {n : ℕ | n < 4} := by
        ext x
        simp only [Set.mem_Icc, Set.mem_setOf_eq]
        omega
      rwa [hI] at hperm_p
    have hpermLen_q : permutes q {n : ℕ | n < vl.length} := by
      rw [hvl.1]
      have hI : Set.Icc 0 (4 - 1) = {n : ℕ | n < 4} := by
        ext x
        simp only [Set.mem_Icc, Set.mem_setOf_eq]
        omega
      rwa [hI] at hperm_q
    have hset_p : setOfList (leftActionList p ul) = setOfList ul :=
      SET_OF_LIST_LEFT_ACTION_LIST ul p hpermLen_p
    have hset_q : setOfList (leftActionList q vl) = setOfList vl :=
      SET_OF_LIST_LEFT_ACTION_LIST vl q hpermLen_q
    have hhl_p : hl (leftActionList p ul) = hl ul := by
      show radV (setOfList (leftActionList p ul)) = radV (setOfList ul)
      rw [hset_p]
    have htr_p : truncateSimplex 3 (leftActionList p ul) = leftActionList p ul :=
      TRUNCATE_SIMPLEX_REFL 3 _ (by rw [hlen_p])
    have htr_q : truncateSimplex 3 (leftActionList q vl) = leftActionList q vl :=
      TRUNCATE_SIMPLEX_REFL 3 _ (by rw [hlen_q])
    have hltp : hl (truncateSimplex 3 (leftActionList p ul)) < Real.sqrt 2 := by
      rw [htr_p, hhl_p]
      exact hbru
    have htr := TEZFFSK V (leftActionList p ul) (leftActionList q vl) 3 hs hp
      hbar_p hbar_q hrog hdim (by norm_num) hltp
    have hlist : leftActionList p ul = leftActionList q vl := by
      rw [← htr_p, ← htr_q]
      exact htr
    have hset_eq : setOfList ul = setOfList vl := by
      rw [← hset_p, ← hset_q, hlist]
    have homega3 : omegaListN V ul 3 = omegaListN V vl 3 := by
      have hu : omegaList V ul = circumcenter (setOfList ul) :=
        XNHPWAB1 V ul 3 hp hul hbru
      have hv : omegaList V vl = circumcenter (setOfList vl) :=
        XNHPWAB1 V vl 3 hp hvl hbrv
      rw [show omegaListN V ul 3 = omegaList V ul from by
            show omegaListN V ul 3 = omegaListN V ul (ul.length - 1)
            rw [hul.1],
          show omegaListN V vl 3 = omegaList V vl from by
            show omegaListN V vl 3 = omegaListN V vl (vl.length - 1)
            rw [hvl.1],
          hu, hv, hset_eq]
    intro k hk
    have hk3 : k = 3 := by omega
    subst k
    exact homega3


/-- marchal3.hl:1264 `MCELL_ID_OMEGA_LIST_N`. -/
theorem MCELL_ID_OMEGA_LIST_N (V : Set V3) (i j : ℕ) (ul vl : List V3) (hp : Packing V)
    (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (heq : mcell i V ul = mcell j V vl) (hnel : ¬nullSet (mcell i V ul))
    (hi : i ∈ ({2, 3, 4} : Set ℕ)) (hj : j ∈ ({2, 3, 4} : Set ℕ)) :
    i = j ∧ ∀ k : ℕ, i - 1 ≤ k ∧ k ≤ 3 → omegaListN V ul k = omegaListN V vl k := by
  exact p15_mcell_omega_main V i j ul vl hp hs hul hvl heq hnel hi hj

/-- marchal3.hl:1636 `MCELL_ID_MXI`. -/
theorem MCELL_ID_MXI (V : Set V3) (i j : ℕ) (ul vl : List V3) (hp : Packing V)
    (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl) (hhd : hdV ul = hdV vl)
    (heq : mcell i V ul = mcell j V vl) (hnel : ¬nullSet (mcell i V ul))
    (hi : i ∈ ({2, 3} : Set ℕ)) (hj : j ∈ ({2, 3} : Set ℕ)) :
    mxi V ul = mxi V vl := sorry

/-- marchal3.hl:2172 `AFFINE_HULL_3_INSERT`. -/
theorem AFFINE_HULL_3_INSERT (a : V3) (S : Set V3) (h : a ∈ (affineSpan ℝ S : Set V3)) :
    (affineSpan ℝ (insert a S) : Set V3) = (affineSpan ℝ S : Set V3) :=
  congrArg (fun t : AffineSubspace ℝ V3 => (t : Set V3))
    (affineSpan_insert_eq_affineSpan ℝ (SetLike.mem_coe.mp h))

/-! ### GT-2 lane private kit: translated-packing finiteness + cell boundedness

These feed `FINITE_EDGE_X2` and `MCELL_SUBSET_BALL8_1` (both consumed by the
GRUTOTI chain, PackingAuto23). -/

/-- A translate of a packing is a packing (rigidity of `dist`). -/
private theorem p15_packing_translate (V : Set V3) (t : V3) (hp : Packing V) :
    Packing ((fun w => w - t) '' V) := by
  intro a ha b hb hdist
  obtain ⟨u, huV, rfl⟩ := ha
  obtain ⟨v, hvV, rfl⟩ := hb
  simp only [] at hdist ⊢
  have hd : dist (u - t) (v - t) = dist u v := by
    simp only [dist_eq_norm]
    congr 1
    abel
  rw [hd] at hdist
  have huv := hp u huV v hvV hdist
  rw [huv]

/-- Finiteness of the packing points in a ball centered at an arbitrary point
(`Packing.finite_inter_ball` is stated for balls centered at `0`). -/
private theorem p15_finite_inter_ball_at (V : Set V3) (c : V3) (r : ℝ) (hp : Packing V) :
    (V ∩ Metric.ball c r).Finite := by
  classical
  have hfin : ((fun w : V3 => w - c) '' V ∩ Metric.ball 0 r).Finite :=
    (p15_packing_translate V c hp).finite_inter_ball r
  have hsub : V ∩ Metric.ball c r ⊆
      (fun w : V3 => w + c) '' ((fun w : V3 => w - c) '' V ∩ Metric.ball 0 r) := by
    rintro x ⟨hxV, hxb⟩
    refine ⟨x - c, ⟨⟨x, hxV, rfl⟩, ?_⟩, by simp⟩
    rw [Metric.mem_ball, dist_zero_right]
    have hxc : dist x c < r := Metric.mem_ball.mp hxb
    rw [dist_eq_norm] at hxc
    exact hxc
  exact (hfin.image (fun w : V3 => w + c)).subset hsub

/-- Every point of a `voronoiClosed` set is within `2` of its center
(saturation). -/
private theorem p15_voronoi_dist_lt2 {V : Set V3} {s x : V3} (hs : saturated V)
    (hx : x ∈ voronoiClosed V s) : dist x s < 2 := by
  obtain ⟨y, hyV, hyd⟩ := hs x
  have h1 : dist x s ≤ dist x y := by
    simpa only [voronoiClosed, Set.mem_setOf_eq] using hx y hyV
  linarith

/-- Mutual-cone cancellation for the `j = 2` edge cells: two points obeying the
mutual `rconeGe` inequalities at parameter `A` with `A·(2√2) = L`, `L > 0`, are
endpoint-distance-sum bounded by `2√2` (adding the two cone inequalities gives
`‖u1-u0‖² ≥ (d(x,u0)+d(x,u1))·‖u1-u0‖·A`, and `A = hl [u0;u1]/√2` by `HL_2`). -/
private theorem p15_cone_pair_bound {x u0 u1 : V3} {A : ℝ}
    (hLpos : 0 < dist u0 u1)
    (hself : inner ℝ (u1 - u0) (u1 - u0) = dist u0 u1 * dist u0 u1)
    (hA : A * (2 * Real.sqrt 2) = dist u0 u1)
    (hc1 : (x - u0) ⬝ᵥ (u1 - u0) ≥ dist x u0 * dist u1 u0 * A)
    (hc2 : (x - u1) ⬝ᵥ (u0 - u1) ≥ dist x u1 * dist u0 u1 * A) :
    dist x u0 + dist x u1 ≤ 2 * Real.sqrt 2 := by
  have hk : (0:ℝ) < 2 * Real.sqrt 2 := by positivity
  have hApos : (0:ℝ) < A := by
    rcases le_or_gt A 0 with h | h
    · exfalso
      have h1 : A * (2 * Real.sqrt 2) ≤ (0:ℝ) * (2 * Real.sqrt 2) :=
        mul_le_mul_of_nonneg_right h (le_of_lt hk)
      rw [zero_mul] at h1
      linarith
    · exact h
  have hc1' : inner ℝ (x - u0) (u1 - u0) ≥ dist x u0 * (dist u0 u1 * A) := by
    rw [inner_eq_dot]
    have h2 := hc1
    rw [dist_comm u1 u0, mul_assoc] at h2
    exact h2
  have hc2' : inner ℝ (x - u1) (u1 - u0) ≤ -(dist x u1 * (dist u0 u1 * A)) := by
    have h : inner ℝ (x - u1) (u0 - u1) ≥ dist x u1 * (dist u0 u1 * A) := by
      rw [inner_eq_dot]
      have h2 := hc2
      rw [mul_assoc] at h2
      exact h2
    have huv : (u0 - u1 : V3) = -(u1 - u0) := by abel
    rw [huv, inner_neg_right] at h
    linarith
  have hkey : inner ℝ (u1 - u0) (u1 - u0)
      ≥ dist x u0 * (dist u0 u1 * A) + dist x u1 * (dist u0 u1 * A) := by
    have hlin : inner ℝ (u1 - u0) (u1 - u0)
        = inner ℝ (x - u0) (u1 - u0) - inner ℝ (x - u1) (u1 - u0) := by
      have hsub := @inner_sub_left ℝ V3 _ _ _ (x - u0) (x - u1) (u1 - u0)
      have hab : (x - u0 : V3) - (x - u1) = u1 - u0 := by abel
      rwa [hab] at hsub
    rw [hlin]
    linarith
  have h1 : (dist x u0 + dist x u1) * (dist u0 u1 * A) ≤ dist u0 u1 * dist u0 u1 := by
    linarith [hkey, hself]
  -- `dist u0 u1 = A·(2√2)` turns the bound into `S·(L·A) ≤ k·(L·A)`
  have eL : dist u0 u1 * dist u0 u1 = (2 * Real.sqrt 2) * (dist u0 u1 * A) := by
    rw [hA.symm]
    ring
  rw [eL] at h1
  have hApos' : (0:ℝ) < A := by linarith [div_pos hLpos hk, hA]
  exact le_of_mul_le_mul_right h1 (mul_pos hLpos hApos')

/-- marchal3.hl:2184 `FINITE_EDGE_X2`. -/
theorem FINITE_EDGE_X2 (V : Set V3) (e : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (he : e = {u0, u1}) :
    {X : Set V3 | mcellSet V X ∧ edgeX V X e}.Finite := by
  classical
  -- the finite index tuples: 4-point lists drawn from `V ∩ ball u0 4`
  have hVb : (V ∩ Metric.ball u0 4).Finite := p15_finite_inter_ball_at V u0 4 hp
  have hT : {ul : List V3 | ∃ a b c d : V3, a ∈ V ∩ Metric.ball u0 4 ∧
      b ∈ V ∩ Metric.ball u0 4 ∧ c ∈ V ∩ Metric.ball u0 4 ∧
      d ∈ V ∩ Metric.ball u0 4 ∧ ul = [a, b, c, d]}.Finite := by
    have hsub : {ul : List V3 | ∃ a b c d : V3, a ∈ V ∩ Metric.ball u0 4 ∧
        b ∈ V ∩ Metric.ball u0 4 ∧ c ∈ V ∩ Metric.ball u0 4 ∧
        d ∈ V ∩ Metric.ball u0 4 ∧ ul = [a, b, c, d]} ⊆
        (fun q : V3 × V3 × V3 × V3 => [q.1, q.2.1, q.2.2.1, q.2.2.2]) ''
        ((V ∩ Metric.ball u0 4) ×ˢ ((V ∩ Metric.ball u0 4) ×ˢ
          ((V ∩ Metric.ball u0 4) ×ˢ (V ∩ Metric.ball u0 4)))) := by
      intro l hl
      rw [Set.mem_setOf_eq] at hl
      obtain ⟨a, b, c, d, h0, h1', h2', h3', rfl⟩ := hl
      exact ⟨(a, b, c, d),
        Set.mem_prod.mpr ⟨h0, Set.mem_prod.mpr ⟨h1', Set.mem_prod.mpr ⟨h2', h3'⟩⟩⟩, rfl⟩
    exact Set.Finite.subset ((hVb.prod (hVb.prod (hVb.prod hVb))).image _) hsub
  have hsub : {X : Set V3 | mcellSet V X ∧ edgeX V X e} ⊆
      (fun t : ℕ × List V3 => mcell t.1 V t.2) ''
        ((Set.Iic (4 : ℕ)) ×ˢ
          {ul : List V3 | ∃ a b c d : V3, a ∈ V ∩ Metric.ball u0 4 ∧
            b ∈ V ∩ Metric.ball u0 4 ∧ c ∈ V ∩ Metric.ball u0 4 ∧
            d ∈ V ∩ Metric.ball u0 4 ∧ ul = [a, b, c, d]}) := by
    intro X hX
    obtain ⟨hm, hedge⟩ := hX
    simp only [mcellSet] at hm
    obtain ⟨i, ul, hXmul, hbul⟩ := hm
    simp only [edgeX] at hedge
    obtain ⟨w0, w1, he0, hw0, hw1, hwne⟩ := hedge
    have heq : {w0, w1} = {u0, u1} := he0.symm.trans he
    have hw0in : w0 ∈ ({u0, u1} : Set V3) := by rw [← heq]; exact Set.mem_insert w0 {w1}
    have hu0in : u0 ∈ ({w0, w1} : Set V3) := by rw [heq]; exact Set.mem_insert u0 {u1}
    have hu1in : u1 ∈ ({w0, w1} : Set V3) := by
      rw [heq]
      exact Set.mem_insert_of_mem u0 (Set.mem_singleton u1)
    have hu0vx : u0 ∈ VX V X := by
      rcases Set.mem_insert_iff.mp hu0in with h | h
      · rw [h]
        exact hw0
      · rcases Set.mem_singleton_iff.mp h with h
        rw [h]
        exact hw1
    by_cases hnull : nullSet X
    · exfalso
      have hvx0 : VX V X = ∅ := by rw [VX, if_pos hnull]
      rw [hvx0] at hu0vx
      simp at hu0vx
    -- extract the cell parameters chosen by `cellParams`
    have hwit : ∃ p : ℕ × List V3, p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2 := by
      refine ⟨(if i ≤ 4 then i else 4, ul), ?_, hbul, ?_⟩
      · by_cases hle : i ≤ 4 <;> simp [hle]
      · by_cases hle : i ≤ 4
        · rw [if_pos hle, hXmul]
        · rw [if_neg hle]
          exact hXmul.trans ((MCELL_EXPLICIT i V ul).2.2.2.2 (by omega))
    have hspec := Classical.epsilon_spec
      (p := fun p : ℕ × List V3 => p.1 ≤ 4 ∧ barV V 3 p.2 ∧ X = mcell p.1 V p.2) hwit
    obtain ⟨hk4, hbarp, hXp⟩ := hspec
    by_cases hk0 : (cellParams V X).1 = 0
    · exfalso
      have hvx0 : VX V X = ∅ := by rw [VX, if_neg hnull, if_pos hk0]
      rw [hvx0] at hu0vx
      simp at hu0vx
    · -- `u0` is a list point of the parameter list
      have hvx : VX V X =
          setOfList (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2) := by
        rw [VX, if_neg hnull, if_neg hk0]
      have hu0tr : u0 ∈ setOfList (truncateSimplex ((cellParams V X).1 - 1)
          (cellParams V X).2) := hvx ▸ hu0vx
      have hk4' : (cellParams V X).1 ≤ 4 := hk4
      have hk0' : (cellParams V X).1 ≠ 0 := hk0
      have hlen4 : (cellParams V X).2.length = 3 + 1 := hbarp.1
      have hinit := (TRUNCATE_SIMPLEX_INITIAL_SUBLIST ((cellParams V X).1 - 1)
        (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2)
          (cellParams V X).2).1
        ⟨rfl, by omega⟩
      obtain ⟨hsubl, -⟩ := hinit
      rcases hsubl with ⟨yl, hyl⟩
      have hu0list : u0 ∈ setOfList (cellParams V X).2 := by
        rw [hyl]
        exact List.mem_append_left _ hu0tr
      obtain ⟨a, b, c, d, hulp⟩ := BARV_3_EXPLICIT V (cellParams V X).2 hbarp
      have hball := p15_barV3ImpFinite2 hp hs hbarp hu0list
      have hpts : ∀ z ∈ setOfList (cellParams V X).2, z ∈ V ∩ Metric.ball u0 4 := by
        intro z hz
        exact ⟨BARV_SUBSET V 3 (cellParams V X).2 hbarp hz, hball hz⟩
      refine ⟨((cellParams V X).1, (cellParams V X).2),
        ⟨hk4, ⟨a, b, c, d, ?_, ?_, ?_, ?_, hulp⟩⟩, hXp.symm⟩
      · exact hpts a (by rw [hulp]; simp [setOfList])
      · exact hpts b (by rw [hulp]; simp [setOfList])
      · exact hpts c (by rw [hulp]; simp [setOfList])
      · exact hpts d (by rw [hulp]; simp [setOfList])
  exact Set.Finite.subset
    ((((Set.finite_Iic 4).prod hT).image (fun t : ℕ × List V3 => mcell t.1 V t.2))) hsub

/-! ## marchal3.hl:2304-2350: the LIFT_* continuity kit

HOL `lift : real -> real^1` is rendered as the constant `Fin 1`-vector
`fun _ : Fin 1 => f x`; domain specialized to arbitrary topological `X`
(this chapter only feeds `V3` through it). -/

/-- marchal3.hl:2304 `CONTINUOUS_ON_LIFT_DOT2`. -/
theorem CONTINUOUS_ON_LIFT_DOT2 {X : Type*} [TopologicalSpace X] {s : Set X}
    {f g : X → V3} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x : X => (fun _ : Fin 1 => f x ⬝ᵥ g x)) s := by
  show ContinuousOn (fun (x : X) (i : Fin 1) => f x ⬝ᵥ g x) s
  rw [continuousOn_pi]
  intro i
  exact p15_dot_contOn hf hg

/-- marchal3.hl:2316 `LIFT_MUL_CONTINUOUS_ON`. -/
theorem LIFT_MUL_CONTINUOUS_ON {X : Type*} [TopologicalSpace X] {s : Set X}
    {f g : X → ℝ} (hf : ContinuousOn (fun x : X => (fun _ : Fin 1 => f x)) s)
    (hg : ContinuousOn (fun x : X => (fun _ : Fin 1 => g x)) s) :
    ContinuousOn (fun x : X => (fun _ : Fin 1 => f x * g x)) s := by
  show ContinuousOn (fun (x : X) (i : Fin 1) => f x * g x) s
  rw [continuousOn_pi]
  intro i
  exact ((continuousOn_pi.mp hf) i).mul ((continuousOn_pi.mp hg) i)

/-- marchal3.hl:2324 `LIFT_DIV_CONTINUOUS_ON`. -/
theorem LIFT_DIV_CONTINUOUS_ON {X : Type*} [TopologicalSpace X] {s : Set X}
    {f g : X → ℝ} (hf : ContinuousOn (fun x : X => (fun _ : Fin 1 => f x)) s)
    (hg : ContinuousOn (fun x : X => (fun _ : Fin 1 => g x)) s)
    (h0 : ∀ x ∈ s, g x ≠ 0) :
    ContinuousOn (fun x : X => (fun _ : Fin 1 => f x / g x)) s := by
  show ContinuousOn (fun (x : X) (i : Fin 1) => f x / g x) s
  rw [continuousOn_pi]
  intro i
  exact ((continuousOn_pi.mp hf) i).div ((continuousOn_pi.mp hg) i) h0

/-- marchal3.hl:2335 `LIFT_DOT_CONTINUOUS_ON`. -/
theorem LIFT_DOT_CONTINUOUS_ON (a b : V3) (s : Set V3) :
    ContinuousOn (fun x : V3 => (fun _ : Fin 1 => (x - a) ⬝ᵥ b)) s := by
  show ContinuousOn (fun (x : V3) (i : Fin 1) => (x - a) ⬝ᵥ b) s
  rw [continuousOn_pi]
  intro i
  exact p15_dot_contOn (continuousOn_id.sub continuousOn_const) continuousOn_const

/-- marchal3.hl:2342 `LIFT_NORM_CONTINUOUS_ON`. -/
theorem LIFT_NORM_CONTINUOUS_ON (a : V3) (s : Set V3) :
    ContinuousOn (fun x : V3 => (fun _ : Fin 1 => norm (x - a))) s := by
  show ContinuousOn (fun (x : V3) (i : Fin 1) => norm (x - a)) s
  rw [continuousOn_pi]
  intro i
  exact (continuousOn_id.sub continuousOn_const).norm

/-! ## marchal3.hl:2352-2610: smallest-angle kit -/

/-- marchal3.hl:2352 `aff_ge_alt`. -/
def affGeAlt (s t : Set V3) (v : V3) : Prop :=
  ∃ f : V3 → ℝ, ∃ q : Set V3, q.Finite ∧ q ⊆ t ∧
    v = linCombo (s ∪ q) f ∧ (∀ w ∈ q, 0 ≤ f w) ∧ setSum (s ∪ q) f = 1

/-- marchal3.hl:2358 `smallest_angle_set`: the (choice of the) point of `s`
realizing the smallest angle at `u0` towards `u1`. -/
noncomputable def smallestAngleSet (s : Set V3) (u0 u1 : V3) : V3 :=
  Classical.epsilon fun x => x ∈ s ∧ ∀ y ∈ s,
    ((y - u0) ⬝ᵥ (u1 - u0)) / (norm (y - u0) * norm (u1 - u0)) ≤
      ((x - u0) ⬝ᵥ (u1 - u0)) / (norm (x - u0) * norm (u1 - u0))

/-- marchal3.hl:2367 `smallest_angle_line`. -/
noncomputable def smallestAngleLine (a b c d : V3) : V3 :=
  smallestAngleSet (convexHull ℝ {a, b}) c d


/-! ## marchal3.hl:2371-2620: smallest-angle theorems, ball8, finite mcell set 2 -/

/-- marchal3.hl:2371 `SMALLEST_ANGLE_LINE_EXISTS`. -/
theorem SMALLEST_ANGLE_LINE_EXISTS (a b u0 u1 : V3) (hu0 : u0 ≠ u1)
    (hu0K : u0 ∉ convexHull ℝ {a, b}) :
    ∃ x, x ∈ convexHull ℝ {a, b} ∧ ∀ y ∈ convexHull ℝ {a, b},
      ((y - u0) ⬝ᵥ (u1 - u0)) / (norm (y - u0) * norm (u1 - u0)) ≤
        ((x - u0) ⬝ᵥ (u1 - u0)) / (norm (x - u0) * norm (u1 - u0)) := by
  have hKfin : ({a, b} : Set V3).Finite := Set.Finite.insert a (Set.finite_singleton b)
  have hKcp : IsCompact (convexHull ℝ {a, b}) := Set.Finite.isCompact_convexHull ℝ hKfin
  have hKne : (convexHull ℝ {a, b}).Nonempty :=
    ⟨a, subset_convexHull ℝ _ (Set.mem_insert a _)⟩
  have hden : ∀ y ∈ convexHull ℝ {a, b}, norm (y - u0) * norm (u1 - u0) ≠ 0 := by
    intro y hy h0
    rcases mul_eq_zero.mp h0 with h | h
    · have hy2 : y = u0 := sub_eq_zero.mp (norm_eq_zero.mp h)
      rw [hy2] at hy
      exact hu0K hy
    · exact hu0 (sub_eq_zero.mp (norm_eq_zero.mp h)).symm
  have hcont : ContinuousOn (fun y : V3 =>
      ((y - u0) ⬝ᵥ (u1 - u0)) / (norm (y - u0) * norm (u1 - u0)))
      (convexHull ℝ {a, b}) :=
    (p15_dot_contOn (continuousOn_id.sub continuousOn_const) continuousOn_const).div
      (((continuousOn_id.sub continuousOn_const).norm).mul continuousOn_const)
      (fun y hy => hden y hy)
  obtain ⟨x, hxK, hmax⟩ := hKcp.exists_isMaxOn hKne hcont
  exact ⟨x, hxK, fun y hy => hmax hy⟩

/-- marchal3.hl:2419 `SMALLEST_ANGLE_IN_CONVEX_HULL`. -/
theorem SMALLEST_ANGLE_IN_CONVEX_HULL (m n p q x : V3) (hpq : p ≠ q)
    (hp : p ∉ convexHull ℝ {m, n}) (hx : x = smallestAngleLine m n p q) :
    x ∈ convexHull ℝ {m, n} := by
  have hex := SMALLEST_ANGLE_LINE_EXISTS m n p q hpq hp
  rw [hx, smallestAngleLine, smallestAngleSet]
  exact (Classical.epsilon_spec hex).1

/-- marchal3.hl:2438 `SMALLEST_ANGLE_LINE_PROPERTY`. -/
theorem SMALLEST_ANGLE_LINE_PROPERTY (m n u0 u1 x y : V3) (hu0 : u0 ≠ u1)
    (hu0K : u0 ∉ convexHull ℝ {m, n}) (hx : x = smallestAngleLine m n u0 u1)
    (hy : y ∈ convexHull ℝ {m, n}) :
    ((y - u0) ⬝ᵥ (u1 - u0)) / (norm (y - u0) * norm (u1 - u0)) ≤
      ((x - u0) ⬝ᵥ (u1 - u0)) / (norm (x - u0) * norm (u1 - u0)) := by
  have hex := SMALLEST_ANGLE_LINE_EXISTS m n u0 u1 hu0 hu0K
  rw [hx, smallestAngleLine, smallestAngleSet]
  exact (Classical.epsilon_spec hex).2 y hy

/-- marchal3.hl:2465 `MCELL_SUBSET_BALL8_1`. FILLED (GT-2 lane): the whole cell
lies in `ball (hdV ul) 4` — rogers cells via `ROGERS_SUBSET_VORONOI_CLOSED` +
saturation (`< 2`), the `j = 2` mutual-cone cell via `p15_cone_pair_bound`
(the cone parameter is `hl (trunc 1 ul)/√2 > 0`, `BARV_IMP_HL_1_POS_LT`), the
`j = 3` hull via `MXI_EXPLICIT` (mxi at distance `√2` from the head), and the
`j = 4` hull via `p15_barV3ImpFinite2` — then `dist v x < 4 + 4 = 8`. -/
private theorem p15_mcell_subset_ball4_hd (V : Set V3) (ul : List V3) (hp : Packing V)
    (hs : saturated V) (hb : barV V 3 ul) :
    ∀ j : ℕ, j ≤ 4 → mcell j V ul ⊆ Metric.ball (hdV ul) 4 := by
  obtain ⟨u0, u1, u2, u3, hul⟩ := BARV_3_EXPLICIT V ul hb
  have hhdmem : hdV ul ∈ setOfList ul :=
    HD_IN_SET_OF_LIST ul (by rw [hb.1]; omega)
  have hlist : setOfList ul ⊆ Metric.ball (hdV ul) 4 :=
    p15_barV3ImpFinite2 hp hs hb hhdmem
  have homega : ∀ t : ℕ, t ≤ 3 → omegaListN V ul t ∈
      Metric.ball (hdV ul) 2 := by
    intro t ht
    refine Metric.mem_ball.mpr ?_
    rw [dist_comm]
    exact p15_omega_dist_hd V ul hp hs hb t ht
  have hrogers : rogers V ul ⊆ Metric.ball (hdV ul) 2 := by
    rw [ROGERS_EXPLICIT V ul hs hp hb]
    refine convexHull_min ?_ (convex_ball _ _)
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact homega 0 (by omega)
    · rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact homega 1 (by omega)
      · rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact homega 2 (by omega)
        · rcases Set.mem_singleton_iff.mp hz with rfl
          exact homega 3 (by omega)
  have htr1 : truncateSimplex 1 ul = [u0, u1] := by
    rw [hul]
    exact (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2
  have htr2 : truncateSimplex 2 ul = [u0, u1, u2] := by
    rw [hul]
    exact (TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2
  have e0 : hdV ul = u0 := by rw [hul]; rfl
  have e1 : hdV ul.tail = u1 := by rw [hul]; rfl
  have hhl1 : 0 < hl (truncateSimplex 1 ul) := BARV_IMP_HL_1_POS_LT V ul hs hp hb
  have hHL2 : hl (truncateSimplex 1 ul) = dist u0 u1 / 2 := by rw [htr1, HL_2]
  have hLpos : 0 < dist u0 u1 := by rw [hHL2] at hhl1; linarith
  have hAeq : ∀ A : ℝ, A = hl (truncateSimplex 1 ul) / Real.sqrt 2 →
      A * (2 * Real.sqrt 2) = dist u0 u1 := by
    intro A hA
    rw [hA, hHL2]
    field_simp
  have hq : Real.sqrt 2 < 2 := by
    have hq2 := Real.sqrt_lt_sqrt (x := 2) (y := 4) (by norm_num) (by norm_num)
    rwa [show Real.sqrt 4 = 2 from by norm_num] at hq2
  intro j hj
  rcases Nat.lt_or_ge j 1 with h0 | h0
  · have hj0 : j = 0 := by omega
    rw [hj0, (MCELL_EXPLICIT 0 V ul).1]
    intro x hx
    rw [mcell0, Set.mem_sdiff] at hx
    refine Metric.mem_ball.mpr ?_
    have h2 := p15_voronoi_dist_lt2 hs
      (ROGERS_SUBSET_VORONOI_CLOSED V ul hs hp hb hx.1)
    linarith
  rcases Nat.lt_or_ge j 2 with h1 | h1
  · have hj1 : j = 1 := by omega
    rw [hj1, (MCELL_EXPLICIT 1 V ul).2.1]
    intro x hx
    rw [mcell1] at hx
    split_ifs at hx
    · rw [Set.mem_sdiff] at hx
      refine Metric.mem_ball.mpr ?_
      have h2 := p15_voronoi_dist_lt2 hs
        (ROGERS_SUBSET_VORONOI_CLOSED V ul hs hp hb hx.1.1)
      linarith
    · simp at hx
  rcases Nat.lt_or_ge j 3 with h2c | h2c
  · -- j = 2: the mutual-cone cell; bounded by cone arithmetic
    have hj2 : j = 2 := by omega
    rw [hj2, (MCELL_EXPLICIT 2 V ul).2.2.1]
    intro x hx
    rw [mcell2] at hx
    split_ifs at hx with hcond
    · simp only [] at hx
      set A : ℝ := hl (truncateSimplex 1 ul) / Real.sqrt 2 with hAdef
      obtain ⟨⟨hc1, hc2⟩, -⟩ := hx
      simp only [rconeGe, Set.mem_setOf_eq] at hc1 hc2
      rw [e0, e1] at hc1 hc2
      have hself : inner ℝ (u1 - u0) (u1 - u0) = dist u0 u1 * dist u0 u1 := by
        rw [real_inner_self_eq_norm_sq, ← dist_eq_norm (u1) (u0), dist_comm u1 u0,
          pow_two]
      have hxS : dist x u0 + dist x u1 ≤ 2 * Real.sqrt 2 :=
        p15_cone_pair_bound hLpos hself (hAeq A hAdef) hc1 hc2
      rw [e0]
      refine Metric.mem_ball.mpr ?_
      have hdn : (0:ℝ) ≤ dist x u1 := dist_nonneg
      linarith
    · simp at hx
  rcases Nat.lt_or_ge j 4 with h3 | h3
  · -- j = 3: the hull of the first three list points and `mxi`
    have hj3 : j = 3 := by omega
    rw [hj3, (MCELL_EXPLICIT 3 V ul).2.2.2.1]
    intro x hx
    rw [mcell3] at hx
    split_ifs at hx with hcond
    · obtain ⟨w1, w2⟩ := hcond
      obtain ⟨s, -, hsdist, hsmxi⟩ :=
        MXI_EXPLICIT V ul u0 u1 u2 u3 hs hp hb hul w1 w2
      have hgen : setOfList (truncateSimplex 2 ul) ∪ {mxi V ul} ⊆
          Metric.ball (hdV ul) 4 := by
        intro z hz
        rw [Set.mem_union] at hz
        rcases hz with hz | hz
        · rw [htr2, setOfList] at hz
          rcases List.mem_cons.mp hz with h | h
          · exact hlist (by rw [h]; simp [setOfList, hul])
          · rcases List.mem_cons.mp h with h | h
            · exact hlist (by rw [h]; simp [setOfList, hul])
            · rcases List.mem_cons.mp h with h | h
              · exact hlist (by rw [h]; simp [setOfList, hul])
              · exact absurd h (by simp)
        · rcases Set.mem_singleton_iff.mp hz with rfl
          rw [hsmxi] at hsdist
          rw [Metric.mem_ball, dist_comm, hsdist]
          linarith
      exact convexHull_min hgen (convex_ball _ _) hx
    · simp at hx
  · -- j = 4: the tetrahedron hull
    have hj4 : j = 4 := by omega
    rw [hj4, (MCELL_EXPLICIT 4 V ul).2.2.2.2 (le_refl 4)]
    intro x hx
    rw [mcell4] at hx
    split_ifs at hx
    · exact convexHull_min (fun z hz => hlist hz) (convex_ball _ _) hx
    · simp at hx

/-- marchal3.hl:2465 `MCELL_SUBSET_BALL8_1`. -/
theorem MCELL_SUBSET_BALL8_1 (v : V3) (ul : List V3) (i : ℕ) (V : Set V3)
    (hi : i ≤ 4) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hv : v ∈ mcell i V ul) : mcell i V ul ⊆ Metric.ball v 8 := by
  have h4 := p15_mcell_subset_ball4_hd V ul hp hs hb i hi
  intro x hx
  have hv' : dist v (hdV ul) < 4 := Metric.mem_ball.mp (h4 hv)
  have hx' : dist x (hdV ul) < 4 := Metric.mem_ball.mp (h4 hx)
  refine Metric.mem_ball.mpr ?_
  have t := dist_triangle v (hdV ul) x
  rw [dist_comm (hdV ul) x] at t
  have t2 := dist_comm x v
  linarith

/-- marchal3.hl:2585 `MCELL_SUBSET_BALL8`. -/
theorem MCELL_SUBSET_BALL8 (v : V3) (ul : List V3) (i : ℕ) (V : Set V3)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hv : v ∈ mcell i V ul) : mcell i V ul ⊆ Metric.ball v 8 := by
  rcases Nat.lt_or_ge i 4 with h4 | h4
  · exact MCELL_SUBSET_BALL8_1 v ul i V (by omega) hp hs hb hv
  · have hEq : mcell i V ul = mcell 4 V ul := by
      unfold mcell
      simp [show i ≠ 0 from by omega, show i ≠ 1 from by omega,
        show i ≠ 2 from by omega, show i ≠ 3 from by omega]
    rw [hEq]
    exact MCELL_SUBSET_BALL8_1 v ul 4 V (le_refl 4) hp hs hb (by rw [hEq] at hv; exact hv)

/-- marchal3.hl:2602 `FINITE_MCELL_SET_LEMMA_2`. HOL route verbatim: rescale
the center to the origin (`FINITE_MCELL_SET_LEMMA` with radius `‖s‖ + r`) and
shrink via `‖x‖ ≤ ‖x - s‖ + ‖s‖`. -/
theorem FINITE_MCELL_SET_LEMMA_2 (V : Set V3) (r : ℝ) (s : V3) (hp : Packing V)
    (hs : saturated V) : {X : Set V3 | X ⊆ Metric.ball s r ∧ mcellSet V X}.Finite := by
  refine Set.Finite.subset (FINITE_MCELL_SET_LEMMA V (‖s‖ + r) hp hs) ?_
  intro X hX
  refine ⟨fun x hx => ?_, hX.2⟩
  have hball : ‖x - s‖ < r := hX.1 hx
  have htri : ‖x‖ ≤ ‖x - s‖ + ‖s‖ := by
    calc ‖x‖ = ‖(x - s) + s‖ := by congr 1; abel
      _ ≤ ‖x - s‖ + ‖s‖ := norm_add_le _ _
  have hlt : dist x 0 < ‖s‖ + r := by
    rw [dist_eq_norm]
    simp only [sub_zero]
    linarith
  exact Metric.mem_ball.2 hlt

/-! ## Kit A: 共线/共面桥 -/

/-- 显式三元仿射组合入三点仿射包（LuneVolume 私件同形）。 -/
private theorem p15_span_triple {x p q y : V3} {c h : ℝ}
    (hy : y = x + c • (q - x) + h • (p - x)) :
    y ∈ (affineSpan ℝ ({x, p, q} : Set V3) : Set V3) := by
  have hxS : x ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hpS : p ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hqS : q ∈ affineSpan ℝ ({x, p, q} : Set V3) := mem_affineSpan ℝ (by simp)
  have hd3 : c • (q - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ c (AffineSubspace.vsub_mem_direction hqS hxS)
  have hd4 : h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.smul_mem _ h (AffineSubspace.vsub_mem_direction hpS hxS)
  have hd5 : c • (q - x) + h • (p - x) ∈ (affineSpan ℝ ({x, p, q} : Set V3)).direction :=
    Submodule.add_mem _ hd3 hd4
  have hval : y = h • (p - x) +ᵥ (c • (q - x) +ᵥ x) := by
    rw [hy, vadd_eq_add, vadd_eq_add]
    abel
  rw [hval]
  exact AffineSubspace.vadd_mem_of_mem_direction hd4
    (AffineSubspace.vadd_mem_of_mem_direction hd3 hxS)

/-- 两点互异时共线 ↔ 仿射包成员（LuneVolume 私件同形）。 -/
private theorem p15_coll3_iff_span {v0 v1 y : V3} (hv0v1 : v0 ≠ v1) :
    Collinear3 v0 v1 y ↔
      y ∈ (affineSpan ℝ ({v0, v1} : Set V3) : Set V3) := by
  constructor
  · intro hc
    by_cases hy0 : y = v0
    · rw [hy0]; exact left_mem_affineSpan_pair _ _ _
    by_cases hy1 : y = v1
    · rw [hy1]; exact right_mem_affineSpan_pair _ _ _
    obtain ⟨c, hsmul⟩ := (collinear3_iff_smul (w := v1) (v := v0) hv0v1.symm).mp hc
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨c, ?_⟩
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    exact (sub_eq_iff_eq_add.mp hsmul).symm
  · intro hy
    obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
    by_cases hy1 : y = v1
    · rw [hy1]; exact collinear3_pair_right (v0 := v0) (v1 := v1) rfl
    have hsmul : y - v0 = r • (v1 - v0) := by
      rw [← hr]
      simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    exact (collinear3_iff_smul (w := v1) (v := v0) hv0v1.symm).mpr ⟨r, hsmul⟩

/-- 首两点之一共线时四点共面。 -/
private theorem p15_copl_of_collL {u0 u1 w1 w2 : V3} (hc : Collinear3 u0 u1 w1) :
    Coplanar ({u0, u1, w1, w2} : Set V3) := by
  by_cases h01 : u0 = u1
  · subst h01
    have hset : ({u0, u0, w1, w2} : Set V3) = {u0, w1, w2} := by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact coplanar_triple u0 w1 w2
  · refine ⟨u0, u1, w2, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · refine affineSpan_mono ℝ (fun q hq => ?_) ((p15_coll3_iff_span h01).mp hc)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
      tauto
    · exact mem_affineSpan ℝ (by simp)

/-- 第二共线点情形（对称）。 -/
private theorem p15_copl_of_collR {u0 u1 w1 w2 : V3} (hc : Collinear3 u0 u1 w2) :
    Coplanar ({u0, u1, w1, w2} : Set V3) := by
  by_cases h01 : u0 = u1
  · subst h01
    have hset : ({u0, u0, w1, w2} : Set V3) = {u0, w1, w2} := by
      ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]
    exact coplanar_triple u0 w1 w2
  · refine ⟨u0, u1, w1, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · exact mem_affineSpan ℝ (by simp)
    · refine affineSpan_mono ℝ (fun q hq => ?_) ((p15_coll3_iff_span h01).mp hc)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
      tauto

/-- `¬Coplanar {u0,u1,w1,w2} ⟹ ¬Collinear3 u0 u1 w1`。 -/
private theorem p15_nc1 {u0 u1 w1 w2 : V3}
    (hcop : ¬ Coplanar ({u0, u1, w1, w2} : Set V3)) : ¬ Collinear3 u0 u1 w1 :=
  fun hc => hcop (p15_copl_of_collL hc)

/-- `¬Coplanar {u0,u1,w1,w2} ⟹ ¬Collinear3 u0 u1 w2`。 -/
private theorem p15_nc2 {u0 u1 w1 w2 : V3}
    (hcop : ¬ Coplanar ({u0, u1, w1, w2} : Set V3)) : ¬ Collinear3 u0 u1 w2 :=
  fun hc => hcop (p15_copl_of_collR hc)

/-- `¬Coplanar ⟹ u0 ≠ u1`。 -/
private theorem p15_u0neu1 {u0 u1 w1 w2 : V3}
    (hcop : ¬ Coplanar ({u0, u1, w1, w2} : Set V3)) : u0 ≠ u1 := by
  intro he
  apply hcop
  subst he
  have hset : ({u0, u0, w1, w2} : Set V3) = {u0, w1, w2} := by
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset]
  exact coplanar_triple u0 w1 w2

/-- `affGt {z,w}{w1} ⊆ affineSpan {z,w,w1}`（LuneVolume 私件同形）。 -/
private theorem p15_affGtPair_subset_span {z w w1 : V3}
    (h1 : ¬ Collinear3 z w w1) :
    affGt ({z, w} : Set V3) {w1} ⊆ affineSpan ℝ ({z, w, w1} : Set V3) := by
  have hzw : z ≠ w := fun he => h1 (collinear3_of_eq he.symm)
  have hw1z : w1 ≠ z := fun he => h1 (collinear3_pair_left he)
  have hw1w : w1 ≠ w := fun he => h1 (collinear3_pair_right he)
  intro p hp
  obtain ⟨c, hc, h, hpeq⟩ :=
    (affGt_pair_iff (v0 := z) (v1 := w) (x := w1) (y := p) hzw hw1z hw1w).mp hp
  refine p15_span_triple (x := z) (p := w) (q := w1) (c := c) (h := h) ?_
  rw [show p = (p - z) + z by abel, hpeq]
  abel

/-- `w2 ∈ affGt {v0,v1}{w1}` 时四点共面。 -/
private theorem p15_copl_of_affGt {v0 v1 w1 w2 : V3}
    (h1 : ¬ Collinear3 v0 v1 w1) (hmem : w2 ∈ affGt ({v0, v1} : Set V3) {w1}) :
    Coplanar ({v0, v1, w1, w2} : Set V3) := by
  refine ⟨v0, v1, w1, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact mem_affineSpan ℝ (by simp)
  · exact p15_affGtPair_subset_span h1 hmem

/-- `azim = 0` 时四点共面（经 affGt 零引理 + 平面包含）。 -/
private theorem p15_copl_of_azim_zero {v0 v1 w1 w2 : V3}
    (hcop : ¬ Coplanar ({v0, v1, w1, w2} : Set V3)) : azim v0 v1 w1 w2 ≠ 0 := by
  intro h0
  have h1 := p15_nc1 hcop
  have h2 := p15_nc2 hcop
  have hmem : w2 ∈ affGt ({v0, v1} : Set V3) {w1} :=
    (azim_eq_zero_iff_alt h1 h2).mp h0
  exact hcop (p15_copl_of_affGt h1 hmem)

/-! ## Kit B: ¬coplanar → 线性无关 -/

/-- ℝ 上非零纯量乘法在 V3 上单射。 -/
private theorem p15_smulR_inj {c : ℝ} (hc : c ≠ 0) :
    Function.Injective ((c • ·) : V3 → V3) := by
  intro x y hxy
  have h1 : (c:ℝ) • x = (c:ℝ) • y := hxy
  have h2 : c⁻¹ • ((c:ℝ) • x) = c⁻¹ • ((c:ℝ) • y) := by rw [h1]
  rw [inv_smul_smul₀ hc, inv_smul_smul₀ hc] at h2
  exact h2

/-- `¬Coplanar {u0,u1,w1,w2} ⟹ 差向量族线性无关。 -/
private theorem p15_li_of_ncopl {u0 u1 w1 w2 : V3}
    (hcop : ¬ Coplanar ({u0, u1, w1, w2} : Set V3)) :
    LinearIndependent ℝ ![u1 - u0, w1 - u0, w2 - u0] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : g 0 • (u1 - u0) + g 1 • (w1 - u0) + g 2 • (w2 - u0) = 0 := by
    simpa [Fin.sum_univ_three] using hg
  by_cases h0 : g 0 = 0
  · by_cases h1 : g 1 = 0
    · by_cases h2 : g 2 = 0
      · intro i; fin_cases i <;> assumption
      · -- w2 = u0，塌缩为三点
        rw [h0, h1] at hsum
        simp only [zero_smul, zero_add] at hsum
        have hw2 : w2 = u0 := by
          rcases smul_eq_zero.mp hsum with h | h
          · exact absurd h h2
          · exact sub_eq_zero.mp h
        have hc1 : Coplanar ({u0, u1, w1, w2} : Set V3) := by
          have hset : ({u0, u1, w1, w2} : Set V3) = {u0, u1, w1} := by
            rw [hw2]
            ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
          rw [hset]
          exact coplanar_triple u0 u1 w1
        exact absurd hc1 hcop
    · -- w1 = u0 + (−g2/g1)•(w2−u0) ∈ affineSpan {u0, u1, w2}
      rw [h0, zero_smul, zero_add] at hsum
      have hmove : g 1 • (w1 - u0) = -(g 2 • (w2 - u0)) :=
        eq_neg_of_add_eq_zero_left hsum
      have hne1 : (g 1 : ℝ) ≠ 0 := h1
      have hrel : w1 - u0 = (-g 2 / g 1) • (w2 - u0) := by
        have hsc : (g 1:ℝ) * (-g 2 / g 1) = -g 2 := by field_simp
        have hstep : (g 1:ℝ) • (w1 - u0)
            = (g 1:ℝ) • ((-g 2 / g 1) • (w2 - u0)) := by
          rw [smul_smul, hsc, neg_smul]
          exact hmove
        exact p15_smulR_inj hne1 hstep
      have hc1 : Coplanar ({u0, u1, w1, w2} : Set V3) := by
        refine ⟨u0, u1, w2, fun p hp => ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact mem_affineSpan ℝ (by simp)
        · exact mem_affineSpan ℝ (by simp)
        · refine p15_span_triple (x := u0) (p := u1) (q := w2) (c := -g 2 / g 1)
            (h := 0) ?_
          rw [zero_smul, add_zero, ← hrel]
          abel
        · exact mem_affineSpan ℝ (by simp)
      exact absurd hc1 hcop
  · -- u1 = u0 + (−g1/g0)•(w1−u0) + (−g2/g0)•(w2−u0) ∈ affineSpan {u0, w1, w2}
    have hmove : g 0 • (u1 - u0) = -(g 1 • (w1 - u0) + g 2 • (w2 - u0)) := by
      have h2 : g 0 • (u1 - u0) + (g 1 • (w1 - u0) + g 2 • (w2 - u0)) = 0 := by
        rw [← add_assoc]; exact hsum
      exact eq_neg_of_add_eq_zero_left h2
    have hne0 : (g 0 : ℝ) ≠ 0 := h0
    have hrel : u1 - u0 = (-g 1 / g 0) • (w1 - u0) + (-g 2 / g 0) • (w2 - u0) := by
      have hstep : (g 0:ℝ) • (u1 - u0)
          = (g 0:ℝ) • ((-g 1 / g 0) • (w1 - u0) + (-g 2 / g 0) • (w2 - u0)) := by
        have hsc1 : (g 0:ℝ) * (-g 1 / g 0) = -g 1 := by field_simp
        have hsc2 : (g 0:ℝ) * (-g 2 / g 0) = -g 2 := by field_simp
        rw [smul_add, smul_smul, smul_smul, hsc1, hsc2, neg_smul, neg_smul,
          ← neg_add]
        exact hmove
      exact p15_smulR_inj hne0 hstep
    have hc1 : Coplanar ({u0, u1, w1, w2} : Set V3) := by
      refine ⟨u0, w1, w2, fun p hp => ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact mem_affineSpan ℝ (by simp)
      · refine p15_span_triple (x := u0) (p := w1) (q := w2) (c := -g 2 / g 0)
          (h := -g 1 / g 0) ?_
        rw [add_assoc,
          add_comm ((-g 2 / g 0) • (w2 - u0)) ((-g 1 / g 0) • (w1 - u0)), ← hrel]
        abel
      · exact mem_affineSpan ℝ (by simp)
      · exact mem_affineSpan ℝ (by simp)
    exact absurd hc1 hcop

/-! ## Kit C: 平移桥 + 平分线点 -/

private theorem p15_coll3_zero_sub {x a b : V3} :
    Collinear3 x a b ↔ Collinear3 0 (a - x) (b - x) := by
  by_cases h : a = x
  · rw [h]
    simp only [sub_self]
    constructor <;> intro _ <;> exact collinear3_of_eq rfl
  · have h' : a - x ≠ 0 := sub_ne_zero.mpr h
    rw [collinear3_iff_smul h, collinear3_iff_smul h']
    simp only [sub_zero]

private theorem p15_azimSubSpec {x a b c : V3} {θ : ℝ} :
    AzimSpec x a b c θ ↔ AzimSpec 0 (a - x) (b - x) (c - x) θ := by
  unfold AzimSpec
  simp only [sub_zero, sub_ne_zero]
  have hd : dist a x = dist (a - x) 0 := by rw [dist_eq_norm, dist_eq_norm, sub_zero]
  rw [hd]

private theorem p15_azim_sub_self (x a b c : V3) :
    azim x a b c = azim 0 (a - x) (b - x) (c - x) := by
  unfold azim
  rw [p15_coll3_zero_sub (x := x) (a := a) (b := b),
    p15_coll3_zero_sub (x := x) (a := a) (b := c)]
  have hpred : AzimSpec x a b c = AzimSpec 0 (a - x) (b - x) (c - x) :=
    funext fun _ => propext p15_azimSubSpec
  rw [hpred]

private theorem p15_azim_zero_of_collY (v0 v1 w y : V3) (h : Collinear3 v0 v1 y) :
    azim v0 v1 w y = 0 := by
  unfold azim
  exact if_pos (Or.inr h)

private theorem p15_smul_dot (t : ℝ) (a b : V3) : (t • a) ⬝ᵥ b = t * (a ⬝ᵥ b) := by
  rw [← inner_eq_dot, ← inner_eq_dot, real_inner_smul_left]

private theorem p15_add_dot (a b c : V3) : (a + b) ⬝ᵥ c = a ⬝ᵥ c + b ⬝ᵥ c := by
  rw [← inner_eq_dot, ← inner_eq_dot, ← inner_eq_dot, inner_add_left]

private theorem p15_dot_comm (a b : V3) : a ⬝ᵥ b = b ⬝ᵥ a := by
  rw [← inner_eq_dot, ← inner_eq_dot, real_inner_comm]

/-- 平分线点：方位角 θ ∈ (0, 2π) 时存在 `b` 使 `azim v0 v1 w1 b = θ/2`、
`¬Collinear3 v0 v1 b` 且三差向量线性无关。 -/
private theorem p15_bisector_exists {v0 v1 w1 w2 : V3}
    (h1 : ¬ Collinear3 v0 v1 w1) (h2 : ¬ Collinear3 v0 v1 w2)
    (h0 : 0 < azim v0 v1 w1 w2) :
    ∃ b : V3, azim v0 v1 w1 b = azim v0 v1 w1 w2 / 2 ∧
      ¬ Collinear3 v0 v1 b ∧
      LinearIndependent ℝ ![v1 - v0, w1 - v0, b - v0] := by
  have hv0v1 : v0 ≠ v1 := fun he => h1 (collinear3_of_eq he.symm)
  have hdne : v1 - v0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hv0v1)
  have hv1ne : (v1 : V3) ≠ v0 := Ne.symm hv0v1
  obtain ⟨f1, f2, f3, hon, halign⟩ := exists_on3_eq_smul (v1 - v0) hdne
  have hax : (v1 - v0 : V3) = dist v1 v0 • f3 := by
    rw [dist_eq_norm]
    exact halign
  have hax0 : (v1 - v0 : V3) = dist (v1 - v0) 0 • f3 := by
    rw [dist_eq_norm, sub_zero]
    exact halign
  obtain ⟨ψ, r1, r2, hr1, hr2, hz1, hz2⟩ := azim_frame_spec h1 h2 hon hax hv1ne
  set b : V3 := v0 + (Real.cos (ψ + azim v0 v1 w1 w2 / 2)) • f1
    + (Real.sin (ψ + azim v0 v1 w1 w2 / 2)) • f2 with hbdef
  have hbv : b - v0 = (Real.cos (ψ + azim v0 v1 w1 w2 / 2)) • f1
      + (Real.sin (ψ + azim v0 v1 w1 w2 / 2)) • f2 := by rw [hbdef]; abel
  have hf11 : (f1 : V3) ⬝ᵥ f1 = 1 := hon.1
  have hf22 : (f2 : V3) ⬝ᵥ f2 = 1 := hon.2.1
  have hf12 : (f1 : V3) ⬝ᵥ f2 = 0 := hon.2.2.2.1
  have hf21 : (f2 : V3) ⬝ᵥ f1 = 0 := by rw [p15_dot_comm]; exact hf12
  have hdot1 : ((Real.cos (ψ + azim v0 v1 w1 w2 / 2)) • f1
      + (Real.sin (ψ + azim v0 v1 w1 w2 / 2)) • f2 : V3) ⬝ᵥ f1
      = Real.cos (ψ + azim v0 v1 w1 w2 / 2) := by
    rw [p15_add_dot, p15_smul_dot, p15_smul_dot, hf11, hf21]
    ring
  have hdot2 : ((Real.cos (ψ + azim v0 v1 w1 w2 / 2)) • f1
      + (Real.sin (ψ + azim v0 v1 w1 w2 / 2)) • f2 : V3) ⬝ᵥ f2
      = Real.sin (ψ + azim v0 v1 w1 w2 / 2) := by
    rw [p15_add_dot, p15_smul_dot, p15_smul_dot, hf12, hf22]
    ring
  have hzb : zOf f1 f2 (b - v0) = Complex.exp ((ψ + azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I) := by
    rw [hbv]
    show _ + _ * Complex.I = _
    rw [hdot1, hdot2, Complex.exp_mul_I]
    push_cast
    ring
  have hax0' : v1 - v0 - 0 = dist (v1 - v0) 0 • f3 := by rw [sub_zero]; exact hax0
  have hbnc : ¬ Collinear3 0 (v1 - v0) (b - v0) := by
    rw [← zOf_ne_zero_iff (e1 := f1) (e2 := f2) (e3 := f3) hon hax0' hdne,
      show (b - v0) - 0 = b - v0 from by rw [sub_zero], hzb]
    exact Complex.exp_ne_zero _
  have haz : azim v0 v1 w1 b = azim v0 v1 w1 w2 / 2 := by
    rw [p15_azim_sub_self v0 v1 w1 b, azim_eq_ang_of_frame f1 f2 f3 hon hax0 hdne
      (fun hc => h1 (p15_coll3_zero_sub.mpr hc)) hbnc]
    have hdiv : (zOf f1 f2 (w1 - v0))⁻¹
        * Complex.exp ((ψ + azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I)
        = ((r1 : ℝ)⁻¹ : ℂ) * Complex.exp ((azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I) := by
      rw [hz1, exp_add_I]
      have hr1c : ((r1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr1.ne'
      have hE : Complex.exp ((ψ : ℝ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      field_simp
    rw [hzb, hdiv, ← Complex.ofReal_inv, ang_ofReal_mul_of_pos (by positivity),
      ang_exp_mul_I (by linarith [azim_nonneg v0 v1 w1 w2])
        (by linarith [azim_lt_two_pi v0 v1 w1 w2])]
  refine ⟨b, haz, ?_, ?_⟩
  · intro hc
    have hzz := haz
    rw [p15_azim_zero_of_collY v0 v1 w1 b hc] at hzz
    have hz2 : azim v0 v1 w1 w2 = 0 := by linarith
    exact h0.ne' hz2
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : g 0 • (v1 - v0) + g 1 • (w1 - v0) + g 2 • (b - v0) = 0 := by
      simpa [Fin.sum_univ_three] using hg
    have hzf : (v1 - v0 : V3) ⬝ᵥ f1 = 0 ∧ (v1 - v0 : V3) ⬝ᵥ f2 = 0 :=
      axis_perp hax hon
    have hzax : zOf f1 f2 (v1 - v0) = 0 := by
      show (v1 - v0 : V3) ⬝ᵥ f1 + (v1 - v0 : V3) ⬝ᵥ f2 * Complex.I = 0
      rw [hzf.1, hzf.2]
      simp
    have hz : ((g 1 : ℝ) : ℂ) * ((r1 : ℝ) : ℂ)
        + ((g 2 : ℝ) : ℂ) * Complex.exp ((azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I) = 0 := by
      have hunit : Complex.exp ((-(ψ:ℝ)) * Complex.I)
          * Complex.exp ((ψ:ℝ) * Complex.I) = 1 := by
        rw [← Complex.exp_add]
        push_cast
        simp
      have harg : (-(ψ:ℝ)) * Complex.I
          + ((ψ + azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I)
          = (azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I := by
        rw [Complex.ofReal_add]
        push_cast
        ring
      have hsplit : Complex.exp ((-(ψ:ℝ)) * Complex.I)
          * Complex.exp ((ψ + azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I)
          = Complex.exp ((azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I) := by
        rw [← Complex.exp_add, harg]
      have hE' : Complex.exp ((-(ψ:ℝ)) * Complex.I) * zOf f1 f2 (w1 - v0)
          = ((r1 : ℝ) : ℂ) := by
        rw [hz1, mul_left_comm, hunit, mul_one]
      have hz2' : Complex.exp ((-(ψ:ℝ)) * Complex.I)
          * (((g 1 : ℝ) : ℂ) * zOf f1 f2 (w1 - v0)
            + ((g 2 : ℝ) : ℂ) * Complex.exp ((ψ + azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I))
          = ((g 1 : ℝ) : ℂ) * ((r1 : ℝ) : ℂ)
            + ((g 2 : ℝ) : ℂ) * Complex.exp ((azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I) := by
        rw [mul_add, mul_left_comm, hE', mul_left_comm, hsplit]
      have h0' := congrArg (zOf f1 f2) hsum
      rw [zOf_add, zOf_add, zOf_smul, zOf_smul, zOf_smul, hzax, hzb] at h0'
      have hr0 : zOf f1 f2 0 = 0 := by simp [zOf]
      rw [hr0, mul_zero, zero_add] at h0'
      have h0'' := congrArg (fun z : ℂ => Complex.exp ((-(ψ:ℝ)) * Complex.I) * z) h0'
      rw [mul_zero] at h0''
      exact hz2'.symm.trans h0''
    have him : (g 2 : ℝ) * Real.sin (azim v0 v1 w1 w2 / 2) = 0 := by
      have hexp2 : Complex.exp ((azim v0 v1 w1 w2 / 2 : ℝ) * Complex.I)
          = Complex.cos ((azim v0 v1 w1 w2 / 2 : ℝ) : ℂ)
            + Complex.sin ((azim v0 v1 w1 w2 / 2 : ℝ) : ℂ) * Complex.I :=
        Complex.exp_mul_I _
      have h4 := congrArg Complex.im hz
      rw [hexp2] at h4
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.cos_ofReal_im, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re,
        Complex.I_im, zero_mul, zero_add, mul_zero, add_zero] at h4
      simpa using h4
    have hthpos : 0 < azim v0 v1 w1 w2 / 2 := by linarith
    have hthlt : azim v0 v1 w1 w2 / 2 < Real.pi := by
      have h2π := azim_lt_two_pi v0 v1 w1 w2
      linarith
    have hsin : Real.sin (azim v0 v1 w1 w2 / 2) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hthpos hthlt)
    have hg2 : g 2 = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact h
      · exact absurd h hsin
    have hre : (g 1 : ℝ) * r1 = 0 := by
      have h're := congrArg Complex.re hz
      rw [hg2] at h're
      simpa [Complex.ofReal_zero, zero_mul, add_zero, Complex.I_re] using h're
    have hg1 : g 1 = 0 := by
      rcases mul_eq_zero.mp hre with h | h
      · exact h
      · exact absurd h hr1.ne'
    rw [hg1, hg2, zero_smul, zero_smul, add_zero, add_zero] at hsum
    rcases smul_eq_zero.mp hsum with h | h
    · intro i; fin_cases i <;> simp [h, hg1, hg2]
    · exact absurd h hdne


/-! ### Kit D: affine-box positivity (p15_box_pos; rebuilt from the GT-3a
continuation map, probe /tmp/gt3a_probeD.lean)

The `¬coplanar` box route: with `LinearIndependent ℝ ![u1 - u0, w1 - u0, w2 - u0]`
(Kit B) the parameter box `G = {v | coords > 0, C1, C2, ‖comboMap v‖ < r, sum < 1}`
is an open neighborhood-invariant region; `p15_mem_of_good` sends every good
parameter point into `conicCap ∩ affGt` and into `conicCap ∩ convexHull`, and the
volume of the image is `|det comboMap| * volume (ball vstar ε) > 0` by
`addHaar_image_linearMap` + `IsOpen.measure_pos` + translation invariance. -/

private def p15_bvec (u0 u1 w1 w2 : V3) : Fin 3 → V3 := ![u1 - u0, w1 - u0, w2 - u0]

private def p15_comboMap (u0 u1 w1 w2 : V3) : V3 →ₗ[ℝ] V3 where
  toFun v := ∑ i : Fin 3, (WithLp.ofLp v) i • p15_bvec u0 u1 w1 w2 i
  map_add' x y := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [WithLp.ofLp_smul, RingHom.id_apply]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, Pi.smul_apply, smul_eq_mul]

private theorem p15_comboMap_apply (u0 u1 w1 w2 : V3) (v : V3) :
    p15_comboMap u0 u1 w1 w2 v = ∑ i : Fin 3, (WithLp.ofLp v) i • p15_bvec u0 u1 w1 w2 i :=
  rfl

private theorem p15_zero_toLp : (WithLp.toLp 2 (0 : Fin 3 → ℝ) : V3) = 0 := by
  have h : (WithLp.toLp 2 (0 : Fin 3 → ℝ) : V3) = (0 : V3) := by
    ext i
    simp
  exact h

private theorem p15_comboMap_ker {u0 u1 w1 w2 : V3}
    (hli : LinearIndependent ℝ (p15_bvec u0 u1 w1 w2)) :
    LinearMap.ker (p15_comboMap u0 u1 w1 w2) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  have h1 : p15_comboMap u0 u1 w1 w2 (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [p15_comboMap_apply] at h1
  have hg := (Fintype.linearIndependent_iff.mp hli) (fun i => (WithLp.ofLp (x - y)) i) h1
  have h0 : (WithLp.ofLp (x - y)) = 0 := funext hg
  have hv : x - y = WithLp.toLp 2 (WithLp.ofLp (x - y)) := (WithLp.toLp_ofLp 2 _).symm
  exact sub_eq_zero.mp (by rw [hv, h0, p15_zero_toLp])

private theorem p15_comboMap_inj {u0 u1 w1 w2 : V3}
    (hli : LinearIndependent ℝ (p15_bvec u0 u1 w1 w2)) :
    Function.Injective (p15_comboMap u0 u1 w1 w2) :=
  LinearMap.ker_eq_bot.mp (p15_comboMap_ker hli)

private theorem p15_comboMap_det {u0 u1 w1 w2 : V3}
    (hli : LinearIndependent ℝ (p15_bvec u0 u1 w1 w2)) :
    LinearMap.det (p15_comboMap u0 u1 w1 w2) ≠ 0 := by
  have hinj := p15_comboMap_inj hli
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  have hbij : Function.Bijective (p15_comboMap u0 u1 w1 w2) := ⟨hinj, hsurj⟩
  have he : IsUnit (LinearMap.det (p15_comboMap u0 u1 w1 w2)) :=
    LinearEquiv.isUnit_det' (LinearEquiv.ofBijective (p15_comboMap u0 u1 w1 w2) hbij)
  exact he.ne_zero

/-! ## scalar prelude: κ, c, distinctness -/

private theorem p15_kappa_exists {D E F a : ℝ} (hD : 0 < D) (hEF : 0 < E + F) (ha : a < 1) :
    ∃ κ : ℝ, 0 < κ ∧ κ * D > E + F ∧ κ * D * (1 - a) > (1 + a) * (E + F) := by
  by_cases h1a : 0 < 1 + a
  · have hT : 0 < (1 - a) * D := by nlinarith
    have hTne : (1 - a) * D ≠ 0 := ne_of_gt hT
    have hnum : 0 < (2 * ((1 + a) * (E + F)) + (1 - a) * (D + 2 * (E + F))) := by
      have hA : 0 < (1 + a) * (E + F) := by nlinarith
      nlinarith
    refine ⟨(2 * ((1 + a) * (E + F)) + (1 - a) * (D + 2 * (E + F))) / ((1 - a) * D),
      div_pos hnum hT, ?_, ?_⟩
    · have hkey : (E + F) * (1 - a)
            < (2 * ((1 + a) * (E + F)) + (1 - a) * (D + 2 * (E + F)))
              / ((1 - a) * D) * D * (1 - a) := by
        rw [mul_assoc, mul_comm D (1 - a), div_mul_cancel₀ _ hTne]
        nlinarith
      exact lt_of_mul_lt_mul_right hkey (le_of_lt (by linarith))
    · rw [mul_assoc, mul_comm D (1 - a), div_mul_cancel₀ _ hTne]
      nlinarith
  · have hDne : (D:ℝ) ≠ 0 := ne_of_gt hD
    have hnum2 : 0 < D + E + F := by linarith
    have hκD : (D + E + F) / D * D = D + E + F := div_mul_cancel₀ _ hDne
    refine ⟨(D + E + F) / D, div_pos hnum2 hD, ?_, ?_⟩
    · rw [hκD]
      linarith
    · rw [hκD]
      have hn : (1 + a) * (E + F) ≤ 0 := by nlinarith
      have hp : 0 < (D + E + F) * (1 - a) := by nlinarith
      linarith

private theorem p15_c_exists {P Q r : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ c * P < 1 ∧ c * Q < r := by
  refine ⟨min (1 / (2 * P)) (r / (2 * Q)), lt_min (div_pos (by nlinarith) (by nlinarith))
    (div_pos (by nlinarith) (by nlinarith)), ?_, ?_⟩
  · have hle : min (1 / (2 * P)) (r / (2 * Q)) ≤ 1 / (2 * P) := min_le_left _ _
    have h1 : min (1 / (2 * P)) (r / (2 * Q)) * P ≤ (1 / (2 * P)) * P :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hP)
    have h2 : (1 / (2 * P)) * P = 1 / 2 := by field_simp
    rw [h2] at h1
    linarith
  · have hle : min (1 / (2 * P)) (r / (2 * Q)) ≤ r / (2 * Q) := min_le_right _ _
    have h1 : min (1 / (2 * P)) (r / (2 * Q)) * Q ≤ (r / (2 * Q)) * Q :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hQ)
    have h2 : (r / (2 * Q)) * Q = r / 2 := by field_simp
    rw [h2] at h1
    linarith

private theorem p15_ne_of_li {u0 u1 w1 w2 : V3}
    (hli : LinearIndependent ℝ (p15_bvec u0 u1 w1 w2)) :
    u0 ≠ u1 ∧ w1 ≠ u0 ∧ w1 ≠ u1 ∧ w2 ≠ u0 ∧ w2 ≠ u1 ∧ w1 ≠ w2 := by
  have hg := Fintype.linearIndependent_iff.mp hli
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    have hz : ∑ j : Fin 3, (![1, 0, 0] : Fin 3 → ℝ) j • p15_bvec u0 u1 w1 w2 j = 0 := by
      rw [Fin.sum_univ_three]
      simp [p15_bvec, he]
    exact absurd (hg ![1, 0, 0] hz 0) (by simp)
  · intro he
    have hz : ∑ j : Fin 3, (![0, 1, 0] : Fin 3 → ℝ) j • p15_bvec u0 u1 w1 w2 j = 0 := by
      rw [Fin.sum_univ_three]
      simp [p15_bvec, he]
    exact absurd (hg ![0, 1, 0] hz 1) (by simp)
  · intro he
    have hz : ∑ j : Fin 3, (![1, -1, 0] : Fin 3 → ℝ) j • p15_bvec u0 u1 w1 w2 j = 0 := by
      rw [Fin.sum_univ_three]
      simp [p15_bvec, he]
    exact absurd (hg ![1, -1, 0] hz 0) (by simp)
  · intro he
    have hz : ∑ j : Fin 3, (![0, 0, 1] : Fin 3 → ℝ) j • p15_bvec u0 u1 w1 w2 j = 0 := by
      rw [Fin.sum_univ_three]
      simp [p15_bvec, he]
    exact absurd (hg ![0, 0, 1] hz 2) (by simp)
  · intro he
    have hz : ∑ j : Fin 3, (![1, 0, -1] : Fin 3 → ℝ) j • p15_bvec u0 u1 w1 w2 j = 0 := by
      rw [Fin.sum_univ_three]
      simp [p15_bvec, he]
    exact absurd (hg ![1, 0, -1] hz 0) (by simp)
  · intro he
    have hz : ∑ j : Fin 3, (![0, 1, -1] : Fin 3 → ℝ) j • p15_bvec u0 u1 w1 w2 j = 0 := by
      rw [Fin.sum_univ_three]
      simp [p15_bvec, he]
    exact absurd (hg ![0, 1, -1] hz 1) (by simp)

/-! ## affGt membership by explicit f-sum -/

private theorem p15_mem_affGt {u0 u1 w1 w2 : V3} {x y z : ℝ} (hy : 0 < y) (hz : 0 < z)
    (h1 : u0 ≠ u1) (h2 : w1 ≠ u0) (h3 : w1 ≠ u1) (h4 : w2 ≠ u0) (h5 : w2 ≠ u1) (h6 : w1 ≠ w2) :
    (1 - x - y - z) • u0 + x • u1 + y • w1 + z • w2 ∈
      affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3) := by
  have hfin : (({u0, u1} : Set V3) ∪ {w1, w2}).Finite :=
    ((Set.finite_singleton u1).insert u0).union ((Set.finite_singleton w2).insert w1)
  set f : V3 → ℝ := fun p => if p = u0 then 1 - x - y - z else if p = u1 then x
    else if p = w1 then y else if p = w2 then z else 0 with hfdef
  have hTF : hfin.toFinset = ({u0, u1, w1, w2} : Finset V3) := by
    apply Finset.ext
    intro p
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hU0 : u0 ∉ insert u1 (insert w1 ({w2} : Finset V3)) := by
    simp [h1, Ne.symm h2, Ne.symm h4]
  have hU1 : u1 ∉ insert w1 ({w2} : Finset V3) := by
    simp [Ne.symm h3, Ne.symm h5]
  have hU2 : w1 ∉ ({w2} : Finset V3) := by simp [h6]
  have hifev : ∀ p : V3, f p = (if p = u0 then 1 - x - y - z else if p = u1 then x
    else if p = w1 then y else if p = w2 then z else 0) := fun p => rfl
  refine ⟨f, hfin, ?_, ?_, ?_⟩
  · rw [hTF, Finset.sum_insert hU0, Finset.sum_insert hU1, Finset.sum_insert hU2,
      Finset.sum_singleton]
    simp only [hifev]
    simp [h2, h3, h4, h5, Ne.symm h1, Ne.symm h6]
    abel
  · intro w hw
    have hw1 : 0 < f w1 := by
      rw [hifev]
      simp only [h2, h3]
      exact hy
    have hw2 : 0 < f w2 := by
      rw [hifev]
      simp only [h4, h5, Ne.symm h6]
      exact hz
    rcases Set.mem_insert_iff.mp hw with he | he
    · rw [he]; exact hw1
    · rw [Set.mem_singleton_iff.mp he]; exact hw2
  · rw [hTF, Finset.sum_insert hU0, Finset.sum_insert hU1, Finset.sum_insert hU2,
      Finset.sum_singleton]
    simp only [hifev]
    simp [h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h6]
    ring

/-! ## convex hull membership -/

private theorem p15_mem_convexHull {u0 u1 w1 w2 : V3} {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hsum : x + y + z < 1) :
    (1 - x - y - z) • u0 + x • u1 + y • w1 + z • w2 ∈
      convexHull ℝ ({u0, u1, w1, w2} : Set V3) := by
  have hσpos : 0 < y + z := by linarith
  have hden : (1:ℝ) - (y + z) ≠ 0 := by linarith
  have hA : ((1 - x - y - z) / (1 - (y + z))) • u0 + (x / (1 - (y + z))) • u1
      ∈ segment ℝ u0 u1 := by
    refine ⟨(1 - x - y - z) / (1 - (y + z)), x / (1 - (y + z)),
      div_nonneg (by linarith) (by linarith), div_nonneg (by linarith) (by linarith),
      ?_, rfl⟩
    rw [← add_div, show (1 - x - y - z) + x = 1 - (y + z) from by ring, div_self hden]
  have hB : (y / (y + z)) • w1 + (z / (y + z)) • w2 ∈ segment ℝ w1 w2 := by
    refine ⟨y / (y + z), z / (y + z), div_nonneg (le_of_lt hy) hσpos.le,
      div_nonneg (le_of_lt hz) hσpos.le, ?_, rfl⟩
    rw [← add_div]
    exact div_self (by linarith)
  have hconv : Convex ℝ (convexHull ℝ ({u0, u1, w1, w2} : Set V3)) := convex_convexHull _ _
  have hAin : ((1 - x - y - z) / (1 - (y + z))) • u0 + (x / (1 - (y + z))) • u1 ∈
      convexHull ℝ ({u0, u1, w1, w2} : Set V3) :=
    (segment_subset_convexHull (by simp) (by simp)) hA
  have hBin : (y / (y + z)) • w1 + (z / (y + z)) • w2 ∈
      convexHull ℝ ({u0, u1, w1, w2} : Set V3) :=
    (segment_subset_convexHull (by simp) (by simp)) hB
  have hq : (1 - x - y - z) • u0 + x • u1 + y • w1 + z • w2
      = (1 - (y + z)) • (((1 - x - y - z) / (1 - (y + z))) • u0
          + (x / (1 - (y + z))) • u1)
        + (y + z) • ((y / (y + z)) • w1 + (z / (y + z)) • w2) := by
    rw [smul_add, smul_smul, smul_smul, smul_add, smul_smul, smul_smul,
      mul_comm (1 - (y + z)) ((1 - x - y - z) / (1 - (y + z))), div_mul_cancel₀ _ hden,
      mul_comm (1 - (y + z)) (x / (1 - (y + z))), div_mul_cancel₀ _ hden,
      mul_comm (y + z) (y / (y + z)), div_mul_cancel₀ _ hσpos.ne',
      mul_comm (y + z) (z / (y + z)), div_mul_cancel₀ _ hσpos.ne']
    abel
  have hseg : (1 - x - y - z) • u0 + x • u1 + y • w1 + z • w2
      ∈ segment ℝ (((1 - x - y - z) / (1 - (y + z))) • u0 + (x / (1 - (y + z))) • u1)
          ((y / (y + z)) • w1 + (z / (y + z)) • w2) :=
    ⟨1 - (y + z), y + z, by linarith, by linarith, by ring, hq.symm⟩
  exact (hconv.segment_subset hAin hBin) hseg


/-! ## membership of a good-coordinate point in cap/affGt/hull -/

private theorem p15_mem_of_good {u0 u1 w1 w2 v : V3} {r a x y z : ℝ} (hr : 0 < r)
    (h1 : u0 ≠ u1) (h2 : w1 ≠ u0) (h3 : w1 ≠ u1) (h4 : w2 ≠ u0) (h5 : w2 ≠ u1) (h6 : w1 ≠ w2)
    (hx : (WithLp.ofLp v) 0 = x) (hy : (WithLp.ofLp v) 1 = y) (hz : (WithLp.ofLp v) 2 = z)
    (hx0 : 0 < x) (hy0 : 0 < y) (hz0 : 0 < z)
    (hC1 : x * dist u0 u1 > y * dist u0 w1 + z * dist u0 w2)
    (hC2 : x * dist u0 u1 * (1 - a) > (1 + a) * (y * dist u0 w1 + z * dist u0 w2))
    (hball : ‖p15_comboMap u0 u1 w1 w2 v‖ < r) (hsum : x + y + z < 1) :
    u0 + p15_comboMap u0 u1 w1 w2 v ∈
        conicCap u0 u1 r a ∩ affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3) ∧
      u0 + p15_comboMap u0 u1 w1 w2 v ∈
        conicCap u0 u1 r a ∩ convexHull ℝ ({u0, u1, w1, w2} : Set V3) := by
  have hD : 0 < dist u0 u1 := dist_pos.mpr h1
  have hE : 0 < dist u0 w1 := dist_pos.mpr (Ne.symm h2)
  have hF : 0 < dist u0 w2 := dist_pos.mpr (Ne.symm h4)
  have hδ1low : -(dist u0 w1 * dist u0 u1) ≤ (w1 - u0) ⬝ᵥ (u1 - u0) := by
    have hcs : |(w1 - u0) ⬝ᵥ (u1 - u0)| ≤ dist u0 w1 * dist u0 u1 := by
      have h2 : (w1 - u0) ⬝ᵥ (u1 - u0) = inner ℝ (w1 - u0) (u1 - u0) :=
        (inner_eq_dot _ _).symm
      calc |(w1 - u0) ⬝ᵥ (u1 - u0)|
          = |inner ℝ (w1 - u0) (u1 - u0)| := by rw [h2]
        _ ≤ ‖(w1 - u0 : V3)‖ * ‖(u1 - u0 : V3)‖ := abs_real_inner_le_norm _ _
        _ = dist w1 u0 * dist u1 u0 := by rw [← dist_eq_norm, ← dist_eq_norm]
        _ = dist u0 w1 * dist u0 u1 := by rw [dist_comm w1 u0, dist_comm u1 u0]
    have hneg := neg_abs_le ((w1 - u0) ⬝ᵥ (u1 - u0))
    linarith
  have hδ2low : -(dist u0 w2 * dist u0 u1) ≤ (w2 - u0) ⬝ᵥ (u1 - u0) := by
    have hcs : |(w2 - u0) ⬝ᵥ (u1 - u0)| ≤ dist u0 w2 * dist u0 u1 := by
      have h2 : (w2 - u0) ⬝ᵥ (u1 - u0) = inner ℝ (w2 - u0) (u1 - u0) :=
        (inner_eq_dot _ _).symm
      calc |(w2 - u0) ⬝ᵥ (u1 - u0)|
          = |inner ℝ (w2 - u0) (u1 - u0)| := by rw [h2]
        _ ≤ ‖(w2 - u0 : V3)‖ * ‖(u1 - u0 : V3)‖ := abs_real_inner_le_norm _ _
        _ = dist w2 u0 * dist u1 u0 := by rw [← dist_eq_norm, ← dist_eq_norm]
        _ = dist u0 w2 * dist u0 u1 := by rw [dist_comm w2 u0, dist_comm u1 u0]
    have hneg := neg_abs_le ((w2 - u0) ⬝ᵥ (u1 - u0))
    linarith
  have h11 : (u1 - u0) ⬝ᵥ (u1 - u0) = dist u0 u1 * dist u0 u1 := by
    calc (u1 - u0) ⬝ᵥ (u1 - u0) = ‖(u1 - u0 : V3)‖ ^ 2 := (norm_sq_eq_dot _).symm
      _ = ‖u1 - u0‖ * ‖u1 - u0‖ := pow_two _
      _ = dist u1 u0 * dist u1 u0 := by rw [← dist_eq_norm]
      _ = dist u0 u1 * dist u0 u1 := by rw [dist_comm]
  have hcmb : p15_comboMap u0 u1 w1 w2 v = x • (u1 - u0) + y • (w1 - u0) + z • (w2 - u0) := by
    rw [p15_comboMap_apply, Fin.sum_univ_three, hx, hy, hz]
    simp [p15_bvec]
  have hdoteq : (p15_comboMap u0 u1 w1 w2 v) ⬝ᵥ (u1 - u0)
      = x * ((u1 - u0) ⬝ᵥ (u1 - u0)) + y * ((w1 - u0) ⬝ᵥ (u1 - u0))
        + z * ((w2 - u0) ⬝ᵥ (u1 - u0)) := by
    rw [hcmb, p15_add_dot, p15_add_dot, p15_smul_dot, p15_smul_dot, p15_smul_dot]
  have hnormUB : ‖p15_comboMap u0 u1 w1 w2 v‖
      ≤ x * dist u0 u1 + (y * dist u0 w1 + z * dist u0 w2) := by
    calc ‖p15_comboMap u0 u1 w1 w2 v‖
        = ‖x • (u1 - u0) + (y • (w1 - u0) + z • (w2 - u0))‖ := by rw [hcmb, add_assoc]
      _ ≤ ‖x • (u1 - u0)‖ + ‖y • (w1 - u0) + z • (w2 - u0)‖ := norm_add_le _ _
      _ ≤ ‖x • (u1 - u0)‖ + (‖y • (w1 - u0)‖ + ‖z • (w2 - u0)‖) :=
            add_le_add_right (norm_add_le _ _) _
      _ = x * dist u0 u1 + (y * dist u0 w1 + z * dist u0 w2) := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hx0,
            Real.norm_eq_abs, abs_of_pos hy0, Real.norm_eq_abs, abs_of_pos hz0,
            ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm, dist_comm u0 u1,
            dist_comm u0 w1, dist_comm u0 w2]
  -- hoisted shared facts
  have hδ1ge : -(y * dist u0 w1 * dist u0 u1) ≤ y * ((w1 - u0) ⬝ᵥ (u1 - u0)) := by
    have h := mul_le_mul_of_nonneg_left
      (show -(dist u0 w1 * dist u0 u1) ≤ (w1 - u0) ⬝ᵥ (u1 - u0) from hδ1low)
      (le_of_lt hy0)
    rwa [mul_neg, ← mul_assoc] at h
  have hδ2ge : -(z * dist u0 w2 * dist u0 u1) ≤ z * ((w2 - u0) ⬝ᵥ (u1 - u0)) := by
    have h := mul_le_mul_of_nonneg_left
      (show -(dist u0 w2 * dist u0 u1) ≤ (w2 - u0) ⬝ᵥ (u1 - u0) from hδ2low)
      (le_of_lt hz0)
    rwa [mul_neg, ← mul_assoc] at h
  rw [h11] at hdoteq
  -- cone membership
  have hconemem : u0 + p15_comboMap u0 u1 w1 w2 v ∈ rconeGt u0 u1 a := by
    have hdist : dist (u0 + p15_comboMap u0 u1 w1 w2 v) u0
        = ‖p15_comboMap u0 u1 w1 w2 v‖ := by
      rw [dist_eq_norm, add_sub_cancel_left]
    have hsub : u0 + p15_comboMap u0 u1 w1 w2 v - u0 = p15_comboMap u0 u1 w1 w2 v := by
      rw [add_sub_cancel_left]
    show (u0 + p15_comboMap u0 u1 w1 w2 v - u0) ⬝ᵥ (u1 - u0)
      > dist (u0 + p15_comboMap u0 u1 w1 w2 v) u0 * dist u1 u0 * a
    rw [hsub, hdist, dist_comm u1 u0]
    by_cases ha0 : 0 ≤ a
    · have hR : ‖p15_comboMap u0 u1 w1 w2 v‖ * dist u0 u1 * a
          ≤ (x * dist u0 u1 + (y * dist u0 w1 + z * dist u0 w2)) * dist u0 u1 * a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnormUB (le_of_lt hD))
          ha0
      have hs : 0 < x * dist u0 u1 - y * dist u0 w1 - z * dist u0 w2
          - a * (x * dist u0 u1 + (y * dist u0 w1 + z * dist u0 w2)) := by linarith
      have hkey := mul_pos hD hs
      have hprod : x * (dist u0 u1 * dist u0 u1)
          - y * dist u0 w1 * dist u0 u1 - z * dist u0 w2 * dist u0 u1
          - (x * dist u0 u1 + (y * dist u0 w1 + z * dist u0 w2)) * dist u0 u1 * a
          = dist u0 u1 * (x * dist u0 u1 - y * dist u0 w1 - z * dist u0 w2
            - a * (x * dist u0 u1 + (y * dist u0 w1 + z * dist u0 w2))) := by ring
      linarith
    · have ha0lt : a < 0 := lt_of_not_ge ha0
      have hDa : dist u0 u1 * a < 0 := by nlinarith
      have hR : ‖p15_comboMap u0 u1 w1 w2 v‖ * dist u0 u1 * a ≤ 0 := by
        nlinarith [norm_nonneg (p15_comboMap u0 u1 w1 w2 v), hDa]
      have hp : 0 < dist u0 u1 * (x * dist u0 u1 - y * dist u0 w1 - z * dist u0 w2) :=
        by nlinarith
      have hprod : x * (dist u0 u1 * dist u0 u1)
          - y * dist u0 w1 * dist u0 u1 - z * dist u0 w2 * dist u0 u1
          = dist u0 u1 * (x * dist u0 u1 - y * dist u0 w1 - z * dist u0 w2) := by ring
      linarith
  have hballmem : u0 + p15_comboMap u0 u1 w1 w2 v ∈ Metric.closedBall u0 r :=
    Metric.mem_closedBall.mpr (le_of_lt (by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact hball))
  have hqform : u0 + p15_comboMap u0 u1 w1 w2 v
      = (1 - x - y - z) • u0 + x • u1 + y • w1 + z • w2 := by
    rw [hcmb]
    module
  have hcap : u0 + p15_comboMap u0 u1 w1 w2 v ∈ conicCap u0 u1 r a :=
    Set.mem_inter hballmem hconemem
  have haffmem : u0 + p15_comboMap u0 u1 w1 w2 v ∈
      affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3) := by
    rw [hqform]
    exact p15_mem_affGt hy0 hz0 h1 h2 h3 h4 h5 h6
  have hhullmem : u0 + p15_comboMap u0 u1 w1 w2 v ∈
      convexHull ℝ ({u0, u1, w1, w2} : Set V3) := by
    rw [hqform]
    exact p15_mem_convexHull hx0 hy0 hz0 hsum
  exact ⟨Set.mem_inter hcap haffmem, Set.mem_inter hcap hhullmem⟩


/-! ## the box-positivity main lemma -/

private theorem p15_norm_triple (b1 b2 b3 : V3) (x y z : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) :
    ‖x • b1 + y • b2 + z • b3‖ ≤ x * ‖b1‖ + (y * ‖b2‖ + z * ‖b3‖) := by
  calc ‖x • b1 + y • b2 + z • b3‖
      = ‖x • b1 + (y • b2 + z • b3)‖ := by rw [add_assoc]
    _ ≤ ‖x • b1‖ + ‖y • b2 + z • b3‖ := norm_add_le _ _
    _ ≤ ‖x • b1‖ + (‖y • b2‖ + ‖z • b3‖) := add_le_add_right (norm_add_le _ _) _
    _ = x * ‖b1‖ + (y * ‖b2‖ + z * ‖b3‖) := by
        rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hx,
          Real.norm_eq_abs, abs_of_pos hy, Real.norm_eq_abs, abs_of_pos hz]

private theorem p15_box_pos {u0 u1 w1 w2 : V3} {r a : ℝ} (hr : 0 < r) (ha : a < 1)
    (hli : LinearIndependent ℝ (p15_bvec u0 u1 w1 w2)) :
    0 < volume.real (conicCap u0 u1 r a ∩ affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3)) ∧
    0 < volume.real (conicCap u0 u1 r a ∩ convexHull ℝ ({u0, u1, w1, w2} : Set V3)) := by
  -- distinctness
  obtain ⟨hu0u1, hw1u0, hw1u1, hw2u0, hw2u1, hw1w2⟩ := p15_ne_of_li hli
  have hD : 0 < dist u0 u1 := dist_pos.mpr hu0u1
  have hE : 0 < dist u0 w1 := dist_pos.mpr (Ne.symm hw1u0)
  have hF : 0 < dist u0 w2 := dist_pos.mpr (Ne.symm hw2u0)
  -- scalar parameters
  obtain ⟨κ, hκ0, hκ1, hκ2⟩ :=
    p15_kappa_exists (D := dist u0 u1) (E := dist u0 w1) (F := dist u0 w2) hD
      (by linarith) ha
  obtain ⟨c, hc0, hc1, hc2⟩ :=
    p15_c_exists (P := κ + 2) (Q := κ * dist u0 u1 + dist u0 w1 + dist u0 w2)
      (by nlinarith) (by nlinarith) hr
  -- witness coordinates
  set vstar : V3 := WithLp.toLp 2 ![c * κ, c, c] with hvdef
  have hv0 : (WithLp.ofLp vstar) 0 = c * κ := by rw [hvdef]; simp
  have hv1 : (WithLp.ofLp vstar) 1 = c := by rw [hvdef]; simp
  have hv2 : (WithLp.ofLp vstar) 2 = c := by rw [hvdef]; simp
  -- the good region and its openness
  have hcont : ∀ i : Fin 3, Continuous fun v : V3 => (WithLp.ofLp v) i := fun i =>
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  have hc0c : Continuous fun v : V3 => (WithLp.ofLp v) 0 * dist u0 u1 :=
    (hcont 0).mul continuous_const
  have hc1c : Continuous fun v : V3 => (WithLp.ofLp v) 1 * dist u0 w1 :=
    (hcont 1).mul continuous_const
  have hc2c : Continuous fun v : V3 => (WithLp.ofLp v) 2 * dist u0 w2 :=
    (hcont 2).mul continuous_const
  set G : Set V3 := (fun v : V3 => (WithLp.ofLp v) 0) ⁻¹' Set.Ioi (0:ℝ) ∩
    (fun v : V3 => (WithLp.ofLp v) 1) ⁻¹' Set.Ioi (0:ℝ) ∩
    (fun v : V3 => (WithLp.ofLp v) 2) ⁻¹' Set.Ioi (0:ℝ) ∩
    (fun v : V3 => (WithLp.ofLp v) 0 * dist u0 u1 -
      ((WithLp.ofLp v) 1 * dist u0 w1 + (WithLp.ofLp v) 2 * dist u0 w2)) ⁻¹'
      Set.Ioi (0:ℝ) ∩
    (fun v : V3 => (WithLp.ofLp v) 0 * dist u0 u1 * (1 - a) -
      (1 + a) * ((WithLp.ofLp v) 1 * dist u0 w1 + (WithLp.ofLp v) 2 * dist u0 w2)) ⁻¹'
      Set.Ioi (0:ℝ) ∩
    (fun v : V3 => (WithLp.ofLp v) 0 + (WithLp.ofLp v) 1 + (WithLp.ofLp v) 2) ⁻¹'
      Set.Ioo (0:ℝ) (1:ℝ) ∩
    (p15_comboMap u0 u1 w1 w2) ⁻¹' Metric.ball (0:V3) r with hGdef
  have hGeq : ∀ v : V3, v ∈ G ↔ 0 < (WithLp.ofLp v) 0 ∧ 0 < (WithLp.ofLp v) 1 ∧
      0 < (WithLp.ofLp v) 2 ∧
      (WithLp.ofLp v) 1 * dist u0 w1 + (WithLp.ofLp v) 2 * dist u0 w2 <
        (WithLp.ofLp v) 0 * dist u0 u1 ∧
      (1 + a) * ((WithLp.ofLp v) 1 * dist u0 w1 + (WithLp.ofLp v) 2 * dist u0 w2) <
        (WithLp.ofLp v) 0 * dist u0 u1 * (1 - a) ∧
      0 < (WithLp.ofLp v) 0 + (WithLp.ofLp v) 1 + (WithLp.ofLp v) 2 ∧
      (WithLp.ofLp v) 0 + (WithLp.ofLp v) 1 + (WithLp.ofLp v) 2 < 1 ∧
      ‖p15_comboMap u0 u1 w1 w2 v‖ < r := by
    intro v
    simp only [hGdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, Set.mem_Ioo,
      sub_pos, Metric.mem_ball, dist_zero_right, sub_zero, and_assoc]
  have hcmbv : p15_comboMap u0 u1 w1 w2 vstar
      = (c * κ) • (u1 - u0) + c • (w1 - u0) + c • (w2 - u0) := by
    rw [p15_comboMap_apply, Fin.sum_univ_three, hv0, hv1, hv2]
    simp [p15_bvec]
  have hnb : ‖p15_comboMap u0 u1 w1 w2 vstar‖
      ≤ c * κ * dist u0 u1 + (c * dist u0 w1 + c * dist u0 w2) := by
    have h := p15_norm_triple (u1 - u0) (w1 - u0) (w2 - u0) (c * κ) c c
      (mul_pos hc0 hκ0) hc0 hc0
    have hD1 : ‖(u1 - u0 : V3)‖ = dist u0 u1 := by rw [norm_sub_rev, dist_eq_norm]
    have hE1 : ‖(w1 - u0 : V3)‖ = dist u0 w1 := by rw [norm_sub_rev, dist_eq_norm]
    have hF1 : ‖(w2 - u0 : V3)‖ = dist u0 w2 := by rw [norm_sub_rev, dist_eq_norm]
    rw [hD1, hE1, hF1] at h
    rw [hcmbv]
    exact h
  have hGopen : IsOpen G := by
    have p1 : IsOpen ((fun v : V3 => (WithLp.ofLp v) 0) ⁻¹' Set.Ioi (0:ℝ)) :=
      isOpen_Ioi.preimage (hcont 0)
    have p2 : IsOpen ((fun v : V3 => (WithLp.ofLp v) 1) ⁻¹' Set.Ioi (0:ℝ)) :=
      isOpen_Ioi.preimage (hcont 1)
    have p3 : IsOpen ((fun v : V3 => (WithLp.ofLp v) 2) ⁻¹' Set.Ioi (0:ℝ)) :=
      isOpen_Ioi.preimage (hcont 2)
    have p4 : IsOpen ((fun v : V3 => (WithLp.ofLp v) 0 * dist u0 u1 -
        ((WithLp.ofLp v) 1 * dist u0 w1 + (WithLp.ofLp v) 2 * dist u0 w2)) ⁻¹'
        Set.Ioi (0:ℝ)) :=
      isOpen_Ioi.preimage (hc0c.sub (hc1c.add hc2c))
    have p5 : IsOpen ((fun v : V3 => (WithLp.ofLp v) 0 * dist u0 u1 * (1 - a) -
        (1 + a) * ((WithLp.ofLp v) 1 * dist u0 w1 + (WithLp.ofLp v) 2 * dist u0 w2)) ⁻¹'
        Set.Ioi (0:ℝ)) :=
      isOpen_Ioi.preimage ((hc0c.mul (continuous_const (y := 1 - a))).sub
        ((continuous_const (y := 1 + a)).mul (hc1c.add hc2c)))
    have p6 : IsOpen ((fun v : V3 => (WithLp.ofLp v) 0 + (WithLp.ofLp v) 1 +
        (WithLp.ofLp v) 2) ⁻¹' Set.Ioo (0:ℝ) (1:ℝ)) :=
      isOpen_Ioo.preimage (((hcont 0).add (hcont 1)).add (hcont 2))
    have p7 : IsOpen (p15_comboMap u0 u1 w1 w2 ⁻¹' Metric.ball (0:V3) r) :=
      Metric.isOpen_ball.preimage (LinearMap.continuous_of_finiteDimensional
        (p15_comboMap u0 u1 w1 w2))
    exact IsOpen.inter (IsOpen.inter (IsOpen.inter (IsOpen.inter (IsOpen.inter
      (IsOpen.inter p1 p2) p3) p4) p5) p6) p7
  have hvG : vstar ∈ G := by
    rw [hGeq vstar, hv0, hv1, hv2]
    refine ⟨mul_pos hc0 hκ0, hc0, hc0, ?_, ?_, ?_, ?_, ?_⟩
    · nlinarith [hκ1, hc0, hE, hF]
    · nlinarith [hκ2, hc0, hE, hF]
    · nlinarith [hc0, hκ0]
    · have hre : c * κ + c + c = c * (κ + 2) := by ring
      rw [hre]
      linarith
    · rw [hcmbv]
      refine lt_of_le_of_lt (p15_norm_triple (u1 - u0) (w1 - u0) (w2 - u0) (c * κ) c c
        (mul_pos hc0 hκ0) hc0 hc0) ?_
      have hD1 : ‖(u1 - u0 : V3)‖ = dist u0 u1 := by rw [norm_sub_rev, dist_eq_norm]
      have hE1 : ‖(w1 - u0 : V3)‖ = dist u0 w1 := by rw [norm_sub_rev, dist_eq_norm]
      have hF1 : ‖(w2 - u0 : V3)‖ = dist u0 w2 := by rw [norm_sub_rev, dist_eq_norm]
      have hre : c * κ * dist u0 u1 + (c * dist u0 w1 + c * dist u0 w2)
          = c * (κ * dist u0 u1 + dist u0 w1 + dist u0 w2) := by ring
      rw [hD1, hE1, hF1, hre]
      linarith
  -- the open box
  obtain ⟨ε, hε0, hεsub⟩ := Metric.isOpen_iff.mp hGopen vstar hvG
  have hposB : 0 < volume.real (Metric.ball vstar ε) := by
    rw [Measure.real_def]
    refine ENNReal.toReal_pos (ne_of_gt (IsOpen.measure_pos volume Metric.isOpen_ball
      ⟨vstar, Metric.mem_ball_self hε0⟩)) ?_
    exact ne_of_lt (measure_ball_lt_top (x := vstar) (r := ε))
  have hdet : LinearMap.det (p15_comboMap u0 u1 w1 w2) ≠ 0 := p15_comboMap_det hli
  have hvolB : volume.real (p15_comboMap u0 u1 w1 w2 '' Metric.ball vstar ε)
      = |LinearMap.det (p15_comboMap u0 u1 w1 w2)| * volume.real (Metric.ball vstar ε) := by
    rw [Measure.real_def, Measure.real_def, Measure.addHaar_image_linearMap,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  have himg : (fun v : V3 => u0 + p15_comboMap u0 u1 w1 w2 v) '' Metric.ball vstar ε
      = (fun p : V3 => u0 + p) ''
        (p15_comboMap u0 u1 w1 w2 '' Metric.ball vstar ε) := by
    rw [← Set.image_comp]
    rfl
  have hposI : 0 < volume.real
      ((fun v : V3 => u0 + p15_comboMap u0 u1 w1 w2 v) '' Metric.ball vstar ε) := by
    rw [himg, volume_real_add_left u0, hvolB]
    exact mul_pos (abs_pos.mpr hdet) hposB
  -- containment of the image
  have hsub1 : ∀ v ∈ Metric.ball vstar ε,
      u0 + p15_comboMap u0 u1 w1 w2 v ∈
        conicCap u0 u1 r a ∩ affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3) := by
    intro v hv
    have hvG : v ∈ G := hεsub hv
    rw [hGeq v] at hvG
    obtain ⟨hx0, hy0, hz0, hC1, hC2, hsum0, hsum, hball⟩ := hvG
    exact (p15_mem_of_good hr hu0u1 hw1u0 hw1u1 hw2u0 hw2u1 hw1w2 rfl rfl rfl
      hx0 hy0 hz0 hC1 hC2 hball hsum).1
  have hsub2 : ∀ v ∈ Metric.ball vstar ε,
      u0 + p15_comboMap u0 u1 w1 w2 v ∈
        conicCap u0 u1 r a ∩ convexHull ℝ ({u0, u1, w1, w2} : Set V3) := by
    intro v hv
    have hvG : v ∈ G := hεsub hv
    rw [hGeq v] at hvG
    obtain ⟨hx0, hy0, hz0, hC1, hC2, hsum0, hsum, hball⟩ := hvG
    exact (p15_mem_of_good hr hu0u1 hw1u0 hw1u1 hw2u0 hw2u1 hw1w2 rfl rfl rfl
      hx0 hy0 hz0 hC1 hC2 hball hsum).2
  -- volume transport
  have hTfin : ∀ T : Set V3, T ⊆ Metric.closedBall u0 r → volume T ≠ ⊤ := by
    intro T hT htop
    have h1 : volume T ≤ volume (Metric.ball u0 (r + 1)) :=
      measure_mono (fun p hp => Metric.mem_ball.mpr (by
        have hd := Metric.mem_closedBall.mp (hT hp)
        linarith))
    exact absurd htop (ne_of_lt (h1.trans_lt measure_ball_lt_top))
  have hmonofin : volume
      ((fun v : V3 => u0 + p15_comboMap u0 u1 w1 w2 v) '' Metric.ball vstar ε) ≠ ⊤ :=
    hTfin _ (by
      rintro p ⟨v, hv, rfl⟩
      have hvG : v ∈ G := hεsub hv
      rw [hGeq v] at hvG
      obtain ⟨hx0, hy0, hz0, hC1, hC2, hsum0, hsum, hball⟩ := hvG
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact le_of_lt hball)
  have hsubimg1 : (fun v : V3 => u0 + p15_comboMap u0 u1 w1 w2 v) '' Metric.ball vstar ε ⊆
      conicCap u0 u1 r a ∩ affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3) := by
    rintro p ⟨v, hv, rfl⟩
    exact hsub1 v hv
  have hsubimg2 : (fun v : V3 => u0 + p15_comboMap u0 u1 w1 w2 v) '' Metric.ball vstar ε ⊆
      conicCap u0 u1 r a ∩ convexHull ℝ ({u0, u1, w1, w2} : Set V3) := by
    rintro p ⟨v, hv, rfl⟩
    exact hsub2 v hv
  have hfin1 : volume (conicCap u0 u1 r a ∩ affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3))
      ≠ ⊤ :=
    hTfin _ ((Set.inter_subset_left (s := conicCap u0 u1 r a)
      (t := affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3))).trans
      (Set.inter_subset_left (s := Metric.closedBall u0 r) (t := rconeGt u0 u1 a)))
  have hfin2 : volume
      (conicCap u0 u1 r a ∩ convexHull ℝ ({u0, u1, w1, w2} : Set V3)) ≠ ⊤ :=
    hTfin _ ((Set.inter_subset_left (s := conicCap u0 u1 r a)
      (t := convexHull ℝ ({u0, u1, w1, w2} : Set V3))).trans
      (Set.inter_subset_left (s := Metric.closedBall u0 r) (t := rconeGt u0 u1 a)))
  have hmono1 : volume.real
      ((fun v : V3 => u0 + p15_comboMap u0 u1 w1 w2 v) '' Metric.ball vstar ε) ≤
      volume.real (conicCap u0 u1 r a ∩ affGt ({u0, u1} : Set V3) ({w1, w2} : Set V3)) := by
    rw [Measure.real_def, Measure.real_def]
    exact (ENNReal.toReal_le_toReal hmonofin hfin1).mpr (measure_mono hsubimg1)
  have hmono2 : volume.real
      ((fun v : V3 => u0 + p15_comboMap u0 u1 w1 w2 v) '' Metric.ball vstar ε) ≤
      volume.real (conicCap u0 u1 r a ∩ convexHull ℝ ({u0, u1, w1, w2} : Set V3)) := by
    rw [Measure.real_def, Measure.real_def]
    exact (ENNReal.toReal_le_toReal hmonofin hfin2).mpr (measure_mono hsubimg2)
  exact ⟨lt_of_lt_of_le hposI hmono1, lt_of_lt_of_le hposI hmono2⟩

/-- Mathlib's `Coplanar` (vectorSpan rank ≤ 2) is implied by the chapter's
`Kepler.Geom.Coplanar` (`s ⊆ affineSpan {u, v, w}`): `vectorSpan s` is spanned by
the differences of points of `s`, all of which lie in the direction of
`affineSpan {u, v, w} = span {u - v, w - v}` (≤ 2-dim). -/
private theorem p15_coplML {s : Set V3} (h : Coplanar s) : Coplanar ℝ s := by
  obtain ⟨u, v, w, hsub⟩ := h
  have hdir : vectorSpan ℝ s ≤ Submodule.span ℝ ({u - v, w - v} : Set V3) := by
    have hstep : ∀ z ∈ s, z - v ∈ Submodule.span ℝ ({u - v, w - v} : Set V3) := by
      intro z hz
      refine affineSpan_induction (h := hsub hz) ?mem ?smul_vsub_vadd
      · intro p hp
        rcases Set.mem_insert_iff.mp hp with rfl | hp
        · exact Submodule.subset_span (by simp)
        · rcases Set.mem_insert_iff.mp hp with rfl | hp
          · rw [sub_self]
            exact Submodule.zero_mem _
          · rcases Set.mem_singleton_iff.mp hp with rfl
            exact Submodule.subset_span (by simp)
      · intro c u' v' w' hu' hv' hw'
        have h1' : c • (u' -ᵥ v') ∈ Submodule.span ℝ ({u - v, w - v} : Set V3) := by
          have heq : u' -ᵥ v' = (u' -ᵥ v) - (v' -ᵥ v) := by
            rw [vsub_eq_sub, vsub_eq_sub, vsub_eq_sub]
            module
          rw [heq, smul_sub]
          exact Submodule.sub_mem _ (Submodule.smul_mem _ c hu')
            (Submodule.smul_mem _ c hv')
        rw [show (c • (u' -ᵥ v') +ᵥ w') - v
            = c • (u' - v') + (w' - v) from by
            rw [vadd_eq_add, vsub_eq_sub]
            module]
        exact Submodule.add_mem _ h1' hw'
    rw [vectorSpan_def, Submodule.span_le]
    rintro p hp
    rw [Set.mem_vsub] at hp
    obtain ⟨x, hx, y, hy, rfl⟩ := hp
    have hxv := hstep x hx
    have hyv := hstep y hy
    have hab : x - y = (x - v) - (y - v) := by abel
    rw [vsub_eq_sub, hab]
    exact Submodule.sub_mem _ hxv hyv
  have hmono : Module.finrank ℝ (vectorSpan ℝ s) ≤
      Module.finrank ℝ (Submodule.span ℝ ({u - v, w - v} : Set V3)) :=
    Submodule.finrank_mono hdir
  have hspan2 : Module.finrank ℝ (Submodule.span ℝ ({u - v, w - v} : Set V3)) ≤ 2 := by
    have h2 := finrank_span_finset_le_card (R := ℝ) ({u - v, w - v} : Finset V3)
    unfold Set.finrank at h2
    rcases eq_or_ne (u - v) (w - v) with he | he
    · rw [he] at h2 ⊢
      have hco : (({w - v, w - v} : Finset V3) : Set V3)
          = ({w - v, w - v} : Set V3) := by simp
      rw [hco] at h2
      have hc : (({w - v, w - v} : Finset V3).card : ℕ) = 1 := by simp
      rw [hc] at h2
      exact le_trans h2 (by norm_num)
    · have hnm : u - v ∉ ({w - v} : Finset V3) := by
        intro hcon
        exact he (by simpa using hcon)
      rw [Finset.card_insert_of_notMem hnm] at h2
      have hco : (({u - v, w - v} : Finset V3) : Set V3)
          = ({u - v, w - v} : Set V3) := by simp
      rw [hco] at h2
      have hc : (({w - v} : Finset V3).card : ℕ) = 1 := by simp
      rw [hc] at h2
      omega
  rw [coplanar_iff_finrank_le_two]
  exact le_trans hmono hspan2

/-! ## marchal3.hl:2623-3671: conic caps, measurability, pair calculus -/

/-- marchal3.hl:2623 `CONIC_CAP_WEDGE_EQ_0`. -/
theorem CONIC_CAP_WEDGE_EQ_0 (v0 v1 : V3) (a r : ℝ) (w1 w2 : V3) (ha : a < 1) (hr : 0 < r)
    (h : volume.real (conicCap v0 v1 r a ∩ wedge v0 v1 w1 w2) = 0) :
    Coplanar ℝ ({v0, v1, w1, w2} : Set V3) := by
  by_contra hcop
  have hcopG : ¬ Coplanar ({v0, v1, w1, w2} : Set V3) := fun hc => hcop (p15_coplML hc)
  have h1 : ¬ Collinear3 v0 v1 w1 := p15_nc1 hcopG
  have h2 : ¬ Collinear3 v0 v1 w2 := p15_nc2 hcopG
  have hθ0 : 0 < azim v0 v1 w1 w2 :=
    lt_of_le_of_ne (azim_nonneg v0 v1 w1 w2) (Ne.symm (p15_copl_of_azim_zero hcopG))
  have hθlt : azim v0 v1 w1 w2 < 2 * Real.pi := azim_lt_two_pi v0 v1 w1 w2
  obtain ⟨b, hbz, hbnc, hbli⟩ := p15_bisector_exists h1 h2 hθ0
  have hθ2pos : 0 < azim v0 v1 w1 w2 / 2 := by linarith
  have hθ2lt : azim v0 v1 w1 w2 / 2 < Real.pi := by linarith
  have hbw : wedge v0 v1 w1 b = affGt ({v0, v1} : Set V3) ({w1, b} : Set V3) := by
    refine wedge_eq_affGt h1 hbnc ?_ ?_
    · rw [hbz]; exact hθ2pos
    · rw [hbz]; exact hθ2lt
  have hsub : wedge v0 v1 w1 b ⊆ wedge v0 v1 w1 w2 := by
    intro y hy
    obtain ⟨hnc, hpos, hlt⟩ := hy
    rw [hbz] at hlt
    exact ⟨hnc, hpos, by linarith⟩
  have hbox := (p15_box_pos hr ha hbli).1
  rw [← hbw] at hbox
  have hBne : volume (conicCap v0 v1 r a ∩ wedge v0 v1 w1 w2) ≠ ⊤ := by
    intro htop
    have h1 : volume (conicCap v0 v1 r a ∩ wedge v0 v1 w1 w2) ≤
        volume (Metric.ball v0 (r + 1)) :=
      measure_mono (fun p hp => Metric.mem_ball.mpr (by
        have hd := Metric.mem_closedBall.mp hp.1.1
        linarith))
    exact absurd htop (ne_of_lt (h1.trans_lt measure_ball_lt_top))
  have hB0 : volume (conicCap v0 v1 r a ∩ wedge v0 v1 w1 w2) = 0 := by
    by_contra hB0'
    have hpos : 0 < (volume (conicCap v0 v1 r a ∩ wedge v0 v1 w1 w2)).toReal := by
      refine ENNReal.toReal_pos (Ne.symm ?_) hBne
      exact Ne.symm hB0'
    exact absurd h hpos.ne'
  have hle' : volume (conicCap v0 v1 r a ∩ wedge v0 v1 w1 b) ≤
      volume (conicCap v0 v1 r a ∩ wedge v0 v1 w1 w2) :=
    measure_mono (fun p hp => ⟨hp.1, hsub hp.2⟩)
  rw [hB0] at hle'
  have hA0 : volume (conicCap v0 v1 r a ∩ wedge v0 v1 w1 b) = 0 :=
    le_antisymm hle' bot_le
  exact absurd hbox (by rw [Measure.real_def, hA0]; simp)

/-- marchal3.hl:2657 `CONIC_CAP_AFF_GT_EQ_0`. -/
theorem CONIC_CAP_AFF_GT_EQ_0 (v0 v1 : V3) (a r : ℝ) (w1 w2 : V3) (ha : a < 1) (hr : 0 < r)
    (h : volume.real (conicCap v0 v1 r a ∩ affGt {v0, v1} {w1, w2}) = 0) :
    Coplanar ℝ ({v0, v1, w1, w2} : Set V3) := by
  by_contra hcop
  have hcopG : ¬ Coplanar ({v0, v1, w1, w2} : Set V3) := fun hc => hcop (p15_coplML hc)
  have hli := p15_li_of_ncopl hcopG
  exact absurd (p15_box_pos hr ha hli).1 (by rw [h]; exact lt_irrefl 0)

/-- marchal3.hl:2708 `CONIC_CAP_INTER_CONVEX_HULL_4_GT_0`. -/
theorem CONIC_CAP_INTER_CONVEX_HULL_4_GT_0 (u0 u1 w1 w2 : V3) (r a : ℝ) (hr : 0 < r)
    (ha : a < 1) (ha0 : 0 ≤ a) (hcop : ¬Coplanar ℝ ({u0, u1, w1, w2} : Set V3)) :
    0 < volume.real (conicCap u0 u1 r a ∩ convexHull ℝ {u0, u1, w1, w2}) := by
  have hcopG : ¬ Coplanar ({u0, u1, w1, w2} : Set V3) := fun hc => hcop (p15_coplML hc)
  have hli := p15_li_of_ncopl hcopG
  exact (p15_box_pos hr ha hli).2

/-- `affGe s t` is convex (this chapter needs it for `MEASURABLE_BALL_AFF_GE`;
the PackingAuto12 copy `p12_convex_affGe` is private). -/
private theorem p15_convex_affGe (s t : Set V3) : Convex ℝ (affGe s t) := by
  intro x hx y hy a b ha hb hab
  simp only [affGe, Set.mem_setOf_eq, Affsign] at hx hy ⊢
  obtain ⟨f1, h1fin, h1sum, h1pos, h1lin⟩ := hx
  obtain ⟨f2, h2fin, h2sum, h2pos, h2lin⟩ := hy
  have hsup : (s ∪ t).Finite := by
    have h := h1fin.union h2fin
    rwa [Set.union_self] at h
  have hU1 : h1fin.toFinset ⊆ hsup.toFinset := by
    intro x hx
    have hx' : x ∈ s ∪ t := (Set.Finite.mem_toFinset h1fin).mp hx
    rw [Set.Finite.mem_toFinset]
    exact hx'
  have hU2 : h2fin.toFinset ⊆ hsup.toFinset := by
    intro x hx
    have hx' : x ∈ s ∪ t := (Set.Finite.mem_toFinset h2fin).mp hx
    rw [Set.Finite.mem_toFinset]
    exact hx'
  have g1 : ∀ g : V3 → ℝ,
      ∑ w ∈ hsup.toFinset,
        (fun w => (if w ∈ h1fin.toFinset then g w else 0) • w) w =
        ∑ w ∈ h1fin.toFinset, g w • w := by
    intro g
    refine Eq.trans ?_ (Finset.sum_congr rfl fun w hw => by
      show (if w ∈ h1fin.toFinset then g w else 0) • w = g w • w
      rw [if_pos hw])
    exact (Finset.sum_subset hU1 (fun w _ hw' => by rw [if_neg hw', zero_smul])).symm
  have g2 : ∀ g : V3 → ℝ,
      ∑ w ∈ hsup.toFinset,
        (fun w => (if w ∈ h2fin.toFinset then g w else 0) • w) w =
        ∑ w ∈ h2fin.toFinset, g w • w := by
    intro g
    refine Eq.trans ?_ (Finset.sum_congr rfl fun w hw => by
      show (if w ∈ h2fin.toFinset then g w else 0) • w = g w • w
      rw [if_pos hw])
    exact (Finset.sum_subset hU2 (fun w _ hw' => by rw [if_neg hw', zero_smul])).symm
  have g3 : ∀ g : V3 → ℝ,
      ∑ w ∈ hsup.toFinset,
        (fun w => (if w ∈ h1fin.toFinset then g w else 0)) w =
        ∑ w ∈ h1fin.toFinset, g w := by
    intro g
    refine Eq.trans ?_ (Finset.sum_congr rfl fun w hw => by
      show (if w ∈ h1fin.toFinset then g w else 0) = g w
      rw [if_pos hw])
    exact (Finset.sum_subset hU1 (fun w _ hw' => by rw [if_neg hw'])).symm
  have g4 : ∀ g : V3 → ℝ,
      ∑ w ∈ hsup.toFinset,
        (fun w => (if w ∈ h2fin.toFinset then g w else 0)) w =
        ∑ w ∈ h2fin.toFinset, g w := by
    intro g
    refine Eq.trans ?_ (Finset.sum_congr rfl fun w hw => by
      show (if w ∈ h2fin.toFinset then g w else 0) = g w
      rw [if_pos hw])
    exact (Finset.sum_subset hU2 (fun w _ hw' => by rw [if_neg hw'])).symm
  have hE : ∀ w ∈ hsup.toFinset,
      (fun w => a * (if w ∈ h1fin.toFinset then f1 w else 0) +
        b * (if w ∈ h2fin.toFinset then f2 w else 0)) w • w =
      (a * (if w ∈ h1fin.toFinset then f1 w else 0)) • w +
        (b * (if w ∈ h2fin.toFinset then f2 w else 0)) • w := by
    intro w _
    rw [add_smul]
  refine ⟨fun w => a * (if w ∈ h1fin.toFinset then f1 w else 0) +
    b * (if w ∈ h2fin.toFinset then f2 w else 0), hsup, ?_, ?_, ?_⟩
  · have hchain : ∑ w ∈ hsup.toFinset,
          (fun w => a * (if w ∈ h1fin.toFinset then f1 w else 0) +
            b * (if w ∈ h2fin.toFinset then f2 w else 0)) w • w = a • x + b • y := by
      calc ∑ w ∈ hsup.toFinset,
            (fun w => a * (if w ∈ h1fin.toFinset then f1 w else 0) +
              b * (if w ∈ h2fin.toFinset then f2 w else 0)) w • w
        _ = ∑ w ∈ hsup.toFinset,
              ((a * (if w ∈ h1fin.toFinset then f1 w else 0)) • w +
                (b * (if w ∈ h2fin.toFinset then f2 w else 0)) • w) :=
            Finset.sum_congr rfl fun w hw => hE w hw
        _ = ∑ w ∈ hsup.toFinset,
              (a * (if w ∈ h1fin.toFinset then f1 w else 0)) • w +
              ∑ w ∈ hsup.toFinset,
                (b * (if w ∈ h2fin.toFinset then f2 w else 0)) • w :=
            Finset.sum_add_distrib
        _ = a • ∑ w ∈ hsup.toFinset,
              (fun w => (if w ∈ h1fin.toFinset then f1 w else 0) • w) w +
              b • ∑ w ∈ hsup.toFinset,
                (fun w => (if w ∈ h2fin.toFinset then f2 w else 0) • w) w := by
            have hC : ∑ w ∈ hsup.toFinset,
                (fun w => (a * (if w ∈ h1fin.toFinset then f1 w else 0)) • w) w =
                a • ∑ w ∈ hsup.toFinset,
                  (fun w => (if w ∈ h1fin.toFinset then f1 w else 0) • w) w := by
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun w _ => by rw [smul_smul]
            have hD : ∑ w ∈ hsup.toFinset,
                (fun w => (b * (if w ∈ h2fin.toFinset then f2 w else 0)) • w) w =
                b • ∑ w ∈ hsup.toFinset,
                  (fun w => (if w ∈ h2fin.toFinset then f2 w else 0) • w) w := by
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun w _ => by rw [smul_smul]
            rw [hC, hD]
        _ = a • ∑ w ∈ h1fin.toFinset, f1 w • w +
              b • ∑ w ∈ h2fin.toFinset, f2 w • w := by
            rw [g1 f1, g2 f2]
        _ = a • x + b • y := by rw [h1sum, h2sum]
    rw [hchain]
  · intro w hw
    have q1 : 0 ≤ (if w ∈ h1fin.toFinset then f1 w else 0) := by
      split_ifs with hm
      · exact h1pos w hw
      · exact le_refl 0
    have q2 : 0 ≤ (if w ∈ h2fin.toFinset then f2 w else 0) := by
      split_ifs with hm
      · exact h2pos w hw
      · exact le_refl 0
    refine add_nonneg (mul_nonneg ha q1) (mul_nonneg hb q2)
  · calc ∑ w ∈ hsup.toFinset,
          (fun w => a * (if w ∈ h1fin.toFinset then f1 w else 0) +
            b * (if w ∈ h2fin.toFinset then f2 w else 0)) w
        _ = ∑ w ∈ hsup.toFinset,
              (fun w => a * (if w ∈ h1fin.toFinset then f1 w else 0)) w +
            ∑ w ∈ hsup.toFinset,
              (fun w => b * (if w ∈ h2fin.toFinset then f2 w else 0)) w :=
          Finset.sum_add_distrib
        _ = a * ∑ w ∈ h1fin.toFinset, f1 w + b * ∑ w ∈ h2fin.toFinset, f2 w := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, g3 f1, g4 f2]
        _ = 1 := by
          rw [h1lin, h2lin, mul_one, mul_one, ← hab]

/-- marchal3.hl:3573 `MEASURABLE_BALL_AFF_GE`. HOL `measurable` is rendered
as `NullMeasurableSet · volume`: the unconditional Mathlib fact for convex
sets is `Convex.nullMeasurableSet` and no `Measure.IsComplete volume`
instance exists to upgrade it to `MeasurableSet`. -/
theorem MEASURABLE_BALL_AFF_GE (z : V3) (r : ℝ) (s t : Set V3) :
    NullMeasurableSet (Metric.ball z r ∩ affGe s t) volume :=
  Convex.nullMeasurableSet (μ := volume)
    ((convex_ball z r).inter (p15_convex_affGe s t))

/-- marchal3.hl:3582 `FINITE_LIST_KY_LEMMA_2`. -/
theorem FINITE_LIST_KY_LEMMA_2 {α : Type*} (s : Set α) (hs : s.Finite) :
    {y : List α | ∃ u0 ∈ s, ∃ u1 ∈ s, y = [u0, u1]}.Finite := by
  have heq : {y : List α | ∃ u0 ∈ s, ∃ u1 ∈ s, y = [u0, u1]}
      = (fun p : α × α => [p.1, p.2]) '' (s ×ˢ s) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨u0, hu0, u1, hu1, rfl⟩
      exact ⟨(u0, u1), ⟨hu0, hu1⟩, rfl⟩
    · rintro ⟨p, ⟨hu0, hu1⟩, rfl⟩
      exact ⟨p.1, hu0, p.2, hu1, rfl⟩
  rw [heq]
  exact (hs.prod hs).image _

/-- marchal3.hl:3597 `FINITE_SET_PRODUCT_KY_LEMMA`. -/
theorem FINITE_SET_PRODUCT_KY_LEMMA {α : Type*} (s : Set α) (hs : s.Finite) :
    {e : Set α | ∃ u0 ∈ s, ∃ u1 ∈ s, e = {u0, u1}}.Finite := by
  have heq : {e : Set α | ∃ u0 ∈ s, ∃ u1 ∈ s, e = {u0, u1}}
      = (fun p : α × α => {p.1, p.2}) '' (s ×ˢ s) := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨u0, hu0, u1, hu1, rfl⟩
      exact ⟨(u0, u1), ⟨hu0, hu1⟩, rfl⟩
    · rintro ⟨p, ⟨hu0, hu1⟩, rfl⟩
      exact ⟨p.1, hu0, p.2, hu1, rfl⟩
  rw [heq]
  exact (hs.prod hs).image _

/-! ## marchal3.hl:3608-3899: `\{u,v}` pattern-lambda calculus, DIHX bounds -/

/-- marchal3.hl:3608 `pre_beta` (the HOL `\{u,v}. g u v` beta lemma, rendered
for `patternPair`). -/
theorem pre_beta {β : Type*} [Nonempty β] (g : V3 → V3 → β) (u' v' : V3)
    (h : ∃ f : Set V3 → β, ∀ u v : V3, f {u, v} = g u v) :
    patternPair g {u', v'} = g u' v' := by
  obtain ⟨f, hf⟩ := h
  have hpc : ∀ u v : V3, ({u, v} : Set V3) = {v, u} := by
    intro u v
    simp [Set.pair_eq_pair_iff]
  have hsym : ∀ u v : V3, g u v = g v u := by
    intro u v
    rw [← hf u v, ← hf v u, hpc u v]
  obtain ⟨u, v, he, hg⟩ := Classical.epsilon_spec
    (p := fun x : β => ∃ a b : V3, {u', v'} = ({a, b} : Set V3) ∧ g a b = x)
    ⟨g u' v', u', v', rfl, rfl⟩
  rcases Set.pair_eq_pair_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hg.symm
  · exact hg.symm.trans (hsym _ _)

/-- marchal3.hl:3615 `WELLDEFINED_FUNCTION_2`. -/
theorem WELLDEFINED_FUNCTION_2 {A B C D : Type*} [Nonempty D] (s : A → B → C)
    (t : A → B → D) :
    (∃ f : C → D, ∀ x y, f (s x y) = t x y) ↔
      ∀ x x' y y', s x y = s x' y' → t x y = t x' y' := by
  constructor
  · rintro ⟨f, hf⟩ x x' y y' hxy
    rw [← hf x y, ← hf x' y', hxy]
  · intro h
    refine ⟨fun z => Classical.epsilon fun d : D => ∃ p q, s p q = z ∧ t p q = d,
      fun x y => ?_⟩
    obtain ⟨p0, q0, hp0, ht0⟩ := Classical.epsilon_spec
      (p := fun d : D => ∃ p q, s p q = s x y ∧ t p q = d) ⟨t x y, x, y, rfl, rfl⟩
    show Classical.epsilon (fun d : D => ∃ p q, s p q = s x y ∧ t p q = d) = t x y
    exact Eq.trans ht0.symm (h p0 x q0 y hp0)


/-- marchal3.hl:3625 `well_defined_unordered_pair`. -/
theorem well_defined_unordered_pair {β : Type*} [Nonempty β] (g : V3 → V3 → β) :
    (∃ f : Set V3 → β, ∀ u v : V3, f {u, v} = g u v) ↔ ∀ u v : V3, g u v = g v u := by
  constructor
  · rintro ⟨f, hf⟩ u v
    rw [← hf u v, ← hf v u]
    congr 1
    simp [Set.pair_eq_pair_iff]
  · intro hsym
    refine ⟨patternPair g, fun u v => ?_⟩
    obtain ⟨u0, v0, he, hg⟩ := Classical.epsilon_spec
      (p := fun x : β => ∃ a b : V3, {u, v} = ({a, b} : Set V3) ∧ g a b = x)
      ⟨g u v, u, v, rfl, rfl⟩
    rcases Set.pair_eq_pair_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hg.symm
    · exact hg.symm.trans (hsym _ _)

/-- marchal3.hl:3635 `BETA_PAIR_THM`. -/
theorem BETA_PAIR_THM {β : Type*} [Nonempty β] (g : V3 → V3 → β) (u' v' : V3)
    (h : ∀ u v : V3, g u v = g v u) : patternPair g {u', v'} = g u' v' := by
  obtain ⟨u, v, he, hg⟩ := Classical.epsilon_spec
    (p := fun x : β => ∃ a b : V3, {u', v'} = ({a, b} : Set V3) ∧ g a b = x)
    ⟨g u' v', u', v', rfl, rfl⟩
  rcases Set.pair_eq_pair_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hg.symm
  · exact hg.symm.trans (h _ _)

/-- marchal3.hl:3646 `DIHX_RANGE` (via the `arcV`-range of `dihV`, through the
`dihu2`/`dihu3`/`dihu4` case split of `dihX`). -/
theorem DIHX_RANGE (V : Set V3) (X : Set V3) (u v : V3) :
    0 ≤ dihX V X (u, v) ∧ dihX V X (u, v) ≤ Real.pi := by
  simp only [dihX]
  split_ifs with _ h2 h3 h4
  · exact ⟨le_refl 0, le_of_lt Real.pi_pos⟩
  · rw [show dihu2 V (cellParamsD V X [u, v]).2 = dihV (elV (cellParamsD V X [u, v]).2 0)
          (elV (cellParamsD V X [u, v]).2 1) (mxi V (cellParamsD V X [u, v]).2)
            (omegaListN V (cellParamsD V X [u, v]).2 3) from rfl]
    exact p15_dihV_range _ _ _ _
  · rw [show dihu3 V (cellParamsD V X [u, v]).2 = dihV (elV (cellParamsD V X [u, v]).2 0)
          (elV (cellParamsD V X [u, v]).2 1) (elV (cellParamsD V X [u, v]).2 2)
            (mxi V (cellParamsD V X [u, v]).2) from rfl]
    exact p15_dihV_range _ _ _ _
  · rw [show dihu4 (cellParamsD V X [u, v]).2 = dihV (elV (cellParamsD V X [u, v]).2 0)
          (elV (cellParamsD V X [u, v]).2 1) (elV (cellParamsD V X [u, v]).2 2)
            (elV (cellParamsD V X [u, v]).2 3) from rfl]
    exact p15_dihV_range _ _ _ _
  · exact ⟨le_refl 0, le_of_lt Real.pi_pos⟩

/-- marchal3.hl:3659 `DIHX_LE_PI`. -/
theorem DIHX_LE_PI (V : Set V3) (X : Set V3) (u v : V3) : dihX V X (u, v) ≤ Real.pi :=
  (DIHX_RANGE V X u v).2

/-- marchal3.hl:3670 `LEFT_ACTION_LIST_2_EXISTS` (HOL `0..2` ↔ `Set.Iic 2`;
`permutes` is the PackingAuto2 pointwise-membership encoding). -/
theorem LEFT_ACTION_LIST_2_EXISTS {α : Type*} [Inhabited α] (u0 u1 u2 d x y z : α)
    (hcard : Nat.card ({u0, u1, u2, d} : Set α) = 4) (hset : ({x, y, z} : Set α) = {u0, u1, u2}) :
    ∃ p : Equiv.Perm ℕ, permutes p (Set.Iic 2) ∧
      [x, y, z, d] = leftActionList p [u0, u1, u2, d] := sorry

/-- marchal3.hl:3838 `LEFT_ACTION_LIST_3_EXISTS` (HOL `0..3` ↔ `Set.Iic 3`). -/
theorem LEFT_ACTION_LIST_3_EXISTS {α : Type*} [Inhabited α] (u0 u1 u2 u3 x y z t : α)
    (hcard : Nat.card ({u0, u1, u2, u3} : Set α) = 4)
    (hset : ({x, y, z, t} : Set α) = {u0, u1, u2, u3}) :
    ∃ p : Equiv.Perm ℕ, permutes p (Set.Iic 3) ∧
      [x, y, z, t] = leftActionList p [u0, u1, u2, u3] := sorry

/-- marchal3.hl:4135 `lmfun_bounded`. -/
theorem lmfun_bounded {h : ℝ} (hh : 0 ≤ h) : lmfun h ≤ h0 / (h0 - 1) := by
  unfold lmfun
  split_ifs with hi
  · have hp : (0:ℝ) ≤ h0 - 1 := by norm_num [h0]
    exact div_le_div_of_nonneg_right (by linarith) hp
  · exact div_nonneg (by norm_num [h0]) (by norm_num [h0])

/-- marchal3.hl:4148 `lmfun_pos_le`. -/
theorem lmfun_pos_le (h : ℝ) : 0 ≤ lmfun h := by
  unfold lmfun
  split_ifs with hi
  · exact div_nonneg (by linarith) (by norm_num [h0])
  · exact le_refl 0

private theorem p15_leftActionList_four_explicit (p : Equiv.Perm ℕ) (u0 u1 u2 u3 : V3) :
    leftActionList p [u0, u1, u2, u3] =
      [[u0, u1, u2, u3].getD (p.symm 0) default, [u0, u1, u2, u3].getD (p.symm 1) default,
       [u0, u1, u2, u3].getD (p.symm 2) default, [u0, u1, u2, u3].getD (p.symm 3) default] :=
  rfl

private theorem p15_symm_mem_lt {p : Equiv.Perm ℕ} {n j : ℕ}
    (hperm : permutes p (Set.Icc 0 (n - 1))) (hj : j < n) : p.symm j < n := by
  have hjI : j ∈ Set.Icc 0 (n - 1) := by
    simp only [Set.mem_Icc]
    omega
  have hmem : p.symm j ∈ Set.Icc 0 (n - 1) := by
    have := (hperm (p.symm j)).2 (by simpa using hjI)
    simpa using this
  simp only [Set.mem_Icc] at hmem
  omega

private theorem p15_getD_mem_lt (u0 u1 u2 u3 : V3) {j : ℕ} (hj : j < 4) :
    [u0, u1, u2, u3].getD j default ∈ ({u0, u1, u2, u3} : Set V3) := by
  interval_cases j <;> simp

private theorem p15_trunc1_leftAction (p : Equiv.Perm ℕ) (u0 u1 u2 u3 : V3)
    (hperm : permutes p (Set.Icc 0 (2 - 1))) (hfix : ∀ j : ℕ, 2 ≤ j → p j = j) :
    setOfList (truncateSimplex 1 (leftActionList p [u0, u1, u2, u3])) = ({u0, u1} : Set V3) := by
  rw [p15_leftActionList_four_explicit,
    (TRUNCATE_SIMPLEX_EXPLICIT_1
      ([u0, u1, u2, u3].getD (p.symm 0) default) ([u0, u1, u2, u3].getD (p.symm 1) default)
      ([u0, u1, u2, u3].getD (p.symm 2) default)
      ([u0, u1, u2, u3].getD (p.symm 3) default)).2.2]
  have hmem : ∀ j, j < 2 → [u0, u1, u2, u3].getD (p.symm j) default ∈ ({u0, u1} : Set V3) := by
    intro j hj
    have hlt : p.symm j < 2 := p15_symm_mem_lt hperm hj
    have hc : p.symm j = 0 ∨ p.symm j = 1 := by omega
    rcases hc with h | h <;> simp [h]
  have heach : ∀ i, i < 2 → ∃ j, j < 2 ∧ p.symm j = i := by
    intro i hi
    have hiI : i ∈ Set.Icc 0 (2 - 1) := by
      simp only [Set.mem_Icc]; omega
    have hpi : p i < 2 := by
      have := (hperm i).1 hiI
      simp only [Set.mem_Icc] at this
      omega
    exact ⟨p i, hpi, by simp⟩
  ext x
  simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq]
  constructor
  · intro hx
    rcases hx with hx | hx
    · rw [hx]; exact hmem 0 (by norm_num)
    · rw [hx]; exact hmem 1 (by norm_num)
  · intro hx
    rcases hx with hx | hx
    · have hA0 : p.symm 0 < 2 := p15_symm_mem_lt hperm (by norm_num)
      have hA1 : p.symm 1 < 2 := p15_symm_mem_lt hperm (by norm_num)
      have hne : p.symm 0 ≠ p.symm 1 := by
        intro h
        have := p.symm.injective h
        norm_num at this
      rcases (show p.symm 0 = 0 ∨ p.symm 1 = 0 by omega) with h | h
      · left; rw [hx, h]; rfl
      · right; rw [hx, h]; rfl
    · have hA0 : p.symm 0 < 2 := p15_symm_mem_lt hperm (by norm_num)
      have hA1 : p.symm 1 < 2 := p15_symm_mem_lt hperm (by norm_num)
      have hne : p.symm 0 ≠ p.symm 1 := by
        intro h
        have := p.symm.injective h
        norm_num at this
      rcases (show p.symm 0 = 1 ∨ p.symm 1 = 1 by omega) with h | h
      · left; rw [hx, h]; rfl
      · right; rw [hx, h]; rfl

private theorem p15_trunc2_leftAction (p : Equiv.Perm ℕ) (u0 u1 u2 u3 : V3)
    (hperm : permutes p (Set.Icc 0 (3 - 1))) (hfix : ∀ j : ℕ, 3 ≤ j → p j = j) :
    setOfList (truncateSimplex 2 (leftActionList p [u0, u1, u2, u3])) = ({u0, u1, u2} : Set V3) := by
  rw [p15_leftActionList_four_explicit,
    (TRUNCATE_SIMPLEX_EXPLICIT_2
      ([u0, u1, u2, u3].getD (p.symm 0) default) ([u0, u1, u2, u3].getD (p.symm 1) default)
      ([u0, u1, u2, u3].getD (p.symm 2) default)
      ([u0, u1, u2, u3].getD (p.symm 3) default)).2]
  have hmem : ∀ j, j < 3 → [u0, u1, u2, u3].getD (p.symm j) default ∈ ({u0, u1, u2} : Set V3) := by
    intro j hj
    have hlt : p.symm j < 3 := p15_symm_mem_lt hperm hj
    have hc : p.symm j = 0 ∨ p.symm j = 1 ∨ p.symm j = 2 := by omega
    rcases hc with h | h | h <;> simp [h]
  have heach : ∀ i, i < 3 → ∃ j, j < 3 ∧ p.symm j = i := by
    intro i hi
    have hiI : i ∈ Set.Icc 0 (3 - 1) := by
      simp only [Set.mem_Icc]; omega
    have hpi : p i < 3 := by
      have := (hperm i).1 hiI
      simp only [Set.mem_Icc] at this
      omega
    exact ⟨p i, hpi, by simp⟩
  ext x
  simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq]
  constructor
  · intro hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact hmem 0 (by norm_num)
    · rw [hx]; exact hmem 1 (by norm_num)
    · rw [hx]; exact hmem 2 (by norm_num)
  · intro hx
    rcases hx with hx | hx | hx
    · have hA0 : p.symm 0 < 3 := p15_symm_mem_lt hperm (by norm_num)
      have hA1 : p.symm 1 < 3 := p15_symm_mem_lt hperm (by norm_num)
      have hA2 : p.symm 2 < 3 := p15_symm_mem_lt hperm (by norm_num)
      have h01 : p.symm 0 ≠ p.symm 1 := by
        intro h; have := p.symm.injective h; norm_num at this
      have h02 : p.symm 0 ≠ p.symm 2 := by
        intro h; have := p.symm.injective h; norm_num at this
      have h12 : p.symm 1 ≠ p.symm 2 := by
        intro h; have := p.symm.injective h; norm_num at this
      rcases (show p.symm 0 = 0 ∨ p.symm 1 = 0 ∨ p.symm 2 = 0 by omega) with h | h | h
      · left; rw [hx, h]; rfl
      · right; left; rw [hx, h]; rfl
      · right; right; rw [hx, h]; rfl
    · have hA0 : p.symm 0 < 3 := p15_symm_mem_lt hperm (by norm_num)
      have hA1 : p.symm 1 < 3 := p15_symm_mem_lt hperm (by norm_num)
      have hA2 : p.symm 2 < 3 := p15_symm_mem_lt hperm (by norm_num)
      have h01 : p.symm 0 ≠ p.symm 1 := by
        intro h; have := p.symm.injective h; norm_num at this
      have h02 : p.symm 0 ≠ p.symm 2 := by
        intro h; have := p.symm.injective h; norm_num at this
      have h12 : p.symm 1 ≠ p.symm 2 := by
        intro h; have := p.symm.injective h; norm_num at this
      rcases (show p.symm 0 = 1 ∨ p.symm 1 = 1 ∨ p.symm 2 = 1 by omega) with h | h | h
      · left; rw [hx, h]; rfl
      · right; left; rw [hx, h]; rfl
      · right; right; rw [hx, h]; rfl
    · have hA0 : p.symm 0 < 3 := p15_symm_mem_lt hperm (by norm_num)
      have hA1 : p.symm 1 < 3 := p15_symm_mem_lt hperm (by norm_num)
      have hA2 : p.symm 2 < 3 := p15_symm_mem_lt hperm (by norm_num)
      have h01 : p.symm 0 ≠ p.symm 1 := by
        intro h; have := p.symm.injective h; norm_num at this
      have h02 : p.symm 0 ≠ p.symm 2 := by
        intro h; have := p.symm.injective h; norm_num at this
      have h12 : p.symm 1 ≠ p.symm 2 := by
        intro h; have := p.symm.injective h; norm_num at this
      rcases (show p.symm 0 = 2 ∨ p.symm 1 = 2 ∨ p.symm 2 = 2 by omega) with h | h | h
      · left; rw [hx, h]; rfl
      · right; left; rw [hx, h]; rfl
      · right; right; rw [hx, h]; rfl



private theorem p15_trunc_set_eq (V : Set V3) (i : ℕ) (ul vl : List V3)
    (hp : Packing V) (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (hcell : mcell i V ul = mcell i V vl) (hnull : ¬nullSet (mcell i V ul))
    (hi : i ∈ ({2, 3} : Set ℕ)) :
    setOfList (truncateSimplex (i - 1) ul) = setOfList (truncateSimplex (i - 1) vl) := by
  have hi234 : i ∈ ({2, 3, 4} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
    omega
  obtain ⟨p, q, hperm_p, hfix_p, hperm_q, hfix_q, hbar_p, hbar_q, hrog, hdim⟩ :=
    p15_rogers_common V i ul vl hp hs hul hvl hcell hnull hi234
  obtain ⟨u0, u1, u2, u3, hul4⟩ := BARV_3_EXPLICIT V ul hul
  obtain ⟨v0, v1, v2, v3, hvl4⟩ := BARV_3_EXPLICIT V vl hvl
  subst hul4
  subst hvl4
  have hne : mcell i V [u0, u1, u2, u3] ≠ ∅ := by
    intro hc
    exact hnull (by rw [hc]; exact measure_empty)
  have hi23 : i = 2 ∨ i = 3 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    exact hi
  rcases hi23 with rfl | rfl
  · -- i = 2
    have hltu : hl (truncateSimplex 1 [u0, u1, u2, u3]) < Real.sqrt 2 := by
      by_contra hc
      have hE : mcell 2 V [u0, u1, u2, u3] = ∅ := by
        rw [(MCELL_EXPLICIT 2 V [u0, u1, u2, u3]).2.2.1]
        simp only [mcell2]
        rw [if_neg (fun h => hc h.1)]
      exact hne hE
    have hsetu : setOfList (truncateSimplex 1 [u0, u1, u2, u3]) = ({u0, u1} : Set V3) := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2]
      ext x
      simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff]
    have hsetp : setOfList (truncateSimplex 1 (leftActionList p [u0, u1, u2, u3])) =
        ({u0, u1} : Set V3) :=
      p15_trunc1_leftAction p u0 u1 u2 u3 hperm_p hfix_p
    have hsetv : setOfList (truncateSimplex 1 [v0, v1, v2, v3]) = ({v0, v1} : Set V3) := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 v0 v1 v2 v3).2.2]
      ext x
      simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff]
    have hsetq : setOfList (truncateSimplex 1 (leftActionList q [v0, v1, v2, v3])) =
        ({v0, v1} : Set V3) :=
      p15_trunc1_leftAction q v0 v1 v2 v3 hperm_q hfix_q
    have hhlp : hl (truncateSimplex 1 (leftActionList p [u0, u1, u2, u3])) =
        hl (truncateSimplex 1 [u0, u1, u2, u3]) := by
      show radV (setOfList _) = radV (setOfList _)
      rw [hsetp, hsetu]
    have htr := TEZFFSK V (leftActionList p [u0, u1, u2, u3])
      (leftActionList q [v0, v1, v2, v3]) 1 hs hp hbar_p hbar_q hrog hdim
      (by norm_num) (by rwa [hhlp])
    have hpair : ({u0, u1} : Set V3) = ({v0, v1} : Set V3) := by
      have := congrArg setOfList htr
      rwa [hsetp, hsetq] at this
    rw [hsetu, hsetv, hpair]
  · -- i = 3
    have hltu : hl (truncateSimplex 2 [u0, u1, u2, u3]) < Real.sqrt 2 := by
      by_contra hc
      have hE : mcell 3 V [u0, u1, u2, u3] = ∅ := by
        rw [(MCELL_EXPLICIT 3 V [u0, u1, u2, u3]).2.2.2.1]
        simp only [mcell3]
        rw [if_neg (fun h => hc h.1)]
      exact hne hE
    have hsetu : setOfList (truncateSimplex 2 [u0, u1, u2, u3]) = ({u0, u1, u2} : Set V3) := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 u0 u1 u2 u3).2]
      ext x
      simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff]
    have hsetp : setOfList (truncateSimplex 2 (leftActionList p [u0, u1, u2, u3])) =
        ({u0, u1, u2} : Set V3) :=
      p15_trunc2_leftAction p u0 u1 u2 u3 hperm_p hfix_p
    have hsetv : setOfList (truncateSimplex 2 [v0, v1, v2, v3]) = ({v0, v1, v2} : Set V3) := by
      rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 v0 v1 v2 v3).2]
      ext x
      simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq,
        Set.mem_insert_iff, Set.mem_singleton_iff]
    have hsetq : setOfList (truncateSimplex 2 (leftActionList q [v0, v1, v2, v3])) =
        ({v0, v1, v2} : Set V3) :=
      p15_trunc2_leftAction q v0 v1 v2 v3 hperm_q hfix_q
    have hhlp : hl (truncateSimplex 2 (leftActionList p [u0, u1, u2, u3])) =
        hl (truncateSimplex 2 [u0, u1, u2, u3]) := by
      show radV (setOfList _) = radV (setOfList _)
      rw [hsetp, hsetu]
    have htr := TEZFFSK V (leftActionList p [u0, u1, u2, u3])
      (leftActionList q [v0, v1, v2, v3]) 2 hs hp hbar_p hbar_q hrog hdim
      (by norm_num) (by rwa [hhlp])
    have hpair : ({u0, u1, u2} : Set V3) = ({v0, v1, v2} : Set V3) := by
      have := congrArg setOfList htr
      rwa [hsetp, hsetq] at this
    rw [hsetu, hsetv, hpair]


private theorem p15_voronoiList_subset {V : Set V3} {ul vl : List V3}
    (h : setOfList ul ⊆ setOfList vl) : voronoiList V vl ⊆ voronoiList V ul := by
  intro x hx
  rw [voronoiList, voronoiSet] at hx ⊢
  intro T hT
  obtain ⟨v, hv, rfl⟩ := hT
  exact hx _ ⟨v, h hv, rfl⟩

private theorem p15_equidist_of_set {V : Set V3} {s : Set V3} {a b q : V3}
    (ha : a ∈ s) (hb : b ∈ s) (haV : a ∈ V) (hbV : b ∈ V)
    (hq : q ∈ voronoiSet V s) : dist q b = dist q a := by
  have h1 : q ∈ voronoiClosed V a := Set.mem_sInter.1 hq _ ⟨a, ha, rfl⟩
  have h2 : q ∈ voronoiClosed V b := Set.mem_sInter.1 hq _ ⟨b, hb, rfl⟩
  simp only [voronoiClosed, Set.mem_setOf_eq] at h1 h2
  exact le_antisymm (h2 a haV) (h1 b hbV)

private theorem p15_mxi_eq_of_lt (V : Set V3) (ul vl : List V3) (hp : Packing V)
    (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (hω2 : omegaListN V ul 2 = omegaListN V vl 2)
    (hω3 : omegaListN V ul 3 = omegaListN V vl 3)
    (hbu : hl (truncateSimplex 2 ul) < Real.sqrt 2)
    (hbv : hl (truncateSimplex 2 vl) < Real.sqrt 2)
    (humem : hdV ul ∈ setOfList (truncateSimplex 2 vl)) :
    mxi V ul = mxi V vl := by
  obtain ⟨u0, u1, u2, u3, rfl⟩ := BARV_3_EXPLICIT V ul hul
  obtain ⟨v0, v1, v2, v3, rfl⟩ := BARV_3_EXPLICIT V vl hvl
  rw [(TRUNCATE_SIMPLEX_EXPLICIT_2 v0 v1 v2 v3).2] at humem
  have hdu : hdV [u0, u1, u2, u3] = u0 := rfl
  have hdv : hdV [v0, v1, v2, v3] = v0 := rfl
  rw [hdu] at humem
  have huV : u0 ∈ V := BARV_SUBSET V 3 [u0, u1, u2, u3]
    (by simpa using hul) (by simp [setOfList])
  have hvV : v0 ∈ V := BARV_SUBSET V 3 [v0, v1, v2, v3]
    (by simpa using hvl) (by simp [setOfList])
  have hcellmem : convexHull ℝ
      ({omegaListN V [v0, v1, v2, v3] 2, omegaListN V [v0, v1, v2, v3] 3} : Set V3) ⊆
      voronoiList V [v0, v1, v2] := by
    refine convexHull_min ?_ (CONVEX_VORONOI_LIST V [v0, v1, v2])
    intro x hx
    rcases hx with rfl | rfl
    · have h2 := OMEGA_LIST_N_IN_VORONOI_LIST V [v0, v1, v2, v3] 3 2 hvl (by norm_num)
      rwa [(TRUNCATE_SIMPLEX_EXPLICIT_2 v0 v1 v2 v3).2] at h2
    · have h3 := OMEGA_LIST_N_IN_VORONOI_LIST V [v0, v1, v2, v3] 3 3 hvl (by norm_num)
      rw [TRUNCATE_SIMPLEX_EXPLICIT_3 v0 v1 v2 v3] at h3
      exact p15_voronoiList_subset (by
        intro x hx
        simp only [setOfList, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq]
          at hx ⊢
        tauto) h3
  have hpred : (fun q : V3 => q ∈ convexHull ℝ
        ({omegaListN V [u0, u1, u2, u3] 2, omegaListN V [u0, u1, u2, u3] 3} : Set V3) ∧
        dist q (hdV [u0, u1, u2, u3]) = Real.sqrt 2) =
      (fun q : V3 => q ∈ convexHull ℝ
        ({omegaListN V [v0, v1, v2, v3] 2, omegaListN V [v0, v1, v2, v3] 3} : Set V3) ∧
        dist q (hdV [v0, v1, v2, v3]) = Real.sqrt 2) := by
    funext q
    simp only [hω2, hω3, hdu, hdv]
    refine propext ⟨?_, ?_⟩
    · rintro ⟨hq, hd⟩
      have hqcell : q ∈ voronoiList V [v0, v1, v2] := hcellmem hq
      have heq : dist q u0 = dist q v0 :=
        p15_equidist_of_set (a := v0) (b := u0) (s := setOfList [v0, v1, v2])
          (by simp [setOfList]) humem hvV huV hqcell
      exact ⟨hq, by rw [← heq]; exact hd⟩
    · rintro ⟨hq, hd⟩
      have hqcell : q ∈ voronoiList V [v0, v1, v2] := hcellmem hq
      have heq : dist q u0 = dist q v0 :=
        p15_equidist_of_set (a := v0) (b := u0) (s := setOfList [v0, v1, v2])
          (by simp [setOfList]) humem hvV huV hqcell
      exact ⟨hq, by rw [heq]; exact hd⟩
  simp only [mxi, if_neg (not_le.mpr hbu), if_neg (not_le.mpr hbv)]
  exact congrArg Classical.epsilon hpred


/-- A mixed small/large `sqrt 2` regime is impossible: the level-2 omega point
is shared, and the `sqrt 2`-Voronoi equidistance makes the large side's
circumradius no larger than the small side's. -/
private theorem p15_mxi_mixed_contra (V : Set V3) (ul vl : List V3) (hp : Packing V)
    (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (hω2 : omegaListN V ul 2 = omegaListN V vl 2)
    (hhdmem : hdV vl ∈ setOfList (truncateSimplex 2 ul))
    (hlt : hl (truncateSimplex 2 ul) < Real.sqrt 2)
    (hge : Real.sqrt 2 ≤ hl (truncateSimplex 2 vl)) : False := by
  have hbaru2 : barV V 2 (truncateSimplex 2 ul) :=
    TRUNCATE_SIMPLEX_BARV V 2 3 ul hul (by norm_num)
  have hbarl2 : barV V 2 (truncateSimplex 2 vl) :=
    TRUNCATE_SIMPLEX_BARV V 2 3 vl hvl (by norm_num)
  have hxl_circ : omegaList V (truncateSimplex 2 ul) =
      circumcenter (setOfList (truncateSimplex 2 ul)) :=
    XNHPWAB1 V (truncateSimplex 2 ul) 2 hp hbaru2 hlt
  have hprop := HL_PROPERTIES V (truncateSimplex 2 ul) 2 hp hbaru2
  rw [← hxl_circ] at hprop
  have hxl_eq : hl (truncateSimplex 2 ul) =
      dist (omegaListN V vl 2) (hdV vl) := by
    calc hl (truncateSimplex 2 ul)
        = dist (omegaList V (truncateSimplex 2 ul)) (hdV vl) := (hprop _ hhdmem).symm
      _ = dist (omegaListN V ul 2) (hdV vl) := by
          rw [OMEGA_LIST_LEMMA V ul 2 (by rw [hul.1]; omega)]
      _ = dist (omegaListN V vl 2) (hdV vl) := by rw [hω2]
  have homegyl : omegaList V (truncateSimplex 2 vl) = omegaListN V vl 2 :=
    OMEGA_LIST_LEMMA V vl 2 (by rw [hvl.1]; omega)
  have hhdyl : hdV (truncateSimplex 2 vl) = hdV vl :=
    HD_TRUNCATE_SIMPLEX vl 2 (by have := hvl.1; omega)
  have hle := WAUFCHE1 V (truncateSimplex 2 vl) 2 hp hbarl2
  rw [homegyl, hhdyl] at hle
  have : hl (truncateSimplex 2 vl) ≤ hl (truncateSimplex 2 ul) := by
    calc hl (truncateSimplex 2 vl) ≤ dist (omegaListN V vl 2) (hdV vl) := hle
      _ = hl (truncateSimplex 2 ul) := hxl_eq.symm
  linarith


private theorem p15_mxi_2_main (V : Set V3) (i j : ℕ) (ul vl : List V3) (hp : Packing V)
    (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (heq : mcell i V ul = mcell j V vl) (hnel : ¬nullSet (mcell i V ul))
    (hi : i ∈ ({2, 3} : Set ℕ)) (hj : j ∈ ({2, 3} : Set ℕ)) :
    mxi V ul = mxi V vl := by
  have hi34 : i ∈ ({2, 3, 4} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
    omega
  have hj34 : j ∈ ({2, 3, 4} : Set ℕ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj ⊢
    omega
  obtain ⟨hij, homega⟩ :=
    MCELL_ID_OMEGA_LIST_N V i j ul vl hp hs hul hvl heq hnel hi34 hj34
  subst j
  have hcell : mcell i V ul = mcell i V vl := heq
  have htrunc := p15_trunc_set_eq V i ul vl hp hs hul hvl hcell hnel hi
  have hi23 : i = 2 ∨ i = 3 := by simpa using hi
  rcases hi23 with rfl | rfl
  · -- ===================== i = 2 =====================
    have hω2 : omegaListN V ul 2 = omegaListN V vl 2 :=
      homega 2 (by norm_num)
    have hω3 : omegaListN V ul 3 = omegaListN V vl 3 :=
      homega 3 (by norm_num)
    have hdul_mem1 : hdV ul ∈ setOfList (truncateSimplex 1 ul) := by
      rw [← HD_TRUNCATE_SIMPLEX ul 1 (by have := hul.1; omega)]
      exact HD_IN_SET_OF_LIST _ (by
        rw [LENGTH_TRUNCATE_SIMPLEX 1 ul (by have := hul.1; omega)]; norm_num)
    have hdvl_mem1 : hdV vl ∈ setOfList (truncateSimplex 1 vl) := by
      rw [← HD_TRUNCATE_SIMPLEX vl 1 (by have := hvl.1; omega)]
      exact HD_IN_SET_OF_LIST _ (by
        rw [LENGTH_TRUNCATE_SIMPLEX 1 vl (by have := hvl.1; omega)]; norm_num)
    have humem : hdV ul ∈ setOfList (truncateSimplex 2 vl) := by
      have h1 : hdV ul ∈ setOfList (truncateSimplex 1 vl) := by
        rw [← htrunc]
        exact hdul_mem1
      exact TRUNCATE_SIMPLEX_SUBSET vl 2 1 (by norm_num)
        (by have := hvl.1; omega) h1
    have hvdmem : hdV vl ∈ setOfList (truncateSimplex 2 ul) := by
      have h1 : hdV vl ∈ setOfList (truncateSimplex 1 ul) := by
        rw [htrunc]
        exact hdvl_mem1
      exact TRUNCATE_SIMPLEX_SUBSET ul 2 1 (by norm_num)
        (by have := hul.1; omega) h1
    by_cases hbu : hl (truncateSimplex 2 ul) < Real.sqrt 2
    · by_cases hbv : hl (truncateSimplex 2 vl) < Real.sqrt 2
      · exact p15_mxi_eq_of_lt V ul vl hp hul hvl hω2 hω3 hbu hbv humem
      · exact (p15_mxi_mixed_contra V ul vl hp hul hvl hω2 hvdmem hbu
          (le_of_not_gt hbv)).elim
    · by_cases hbv : hl (truncateSimplex 2 vl) < Real.sqrt 2
      · exact (p15_mxi_mixed_contra V vl ul hp hvl hul hω2.symm humem hbv
          (le_of_not_gt hbu)).elim
      · simp only [mxi, if_pos (le_of_not_gt hbu), if_pos (le_of_not_gt hbv), hω2]
  · -- ===================== i = 3 =====================
    have hω2 : omegaListN V ul 2 = omegaListN V vl 2 :=
      homega 2 (by norm_num)
    have hω3 : omegaListN V ul 3 = omegaListN V vl 3 :=
      homega 3 (by norm_num)
    have hhl : hl (truncateSimplex 2 ul) = hl (truncateSimplex 2 vl) := by
      show radV (setOfList (truncateSimplex 2 ul)) = radV (setOfList (truncateSimplex 2 vl))
      rw [htrunc]
    have hdul_mem2 : hdV ul ∈ setOfList (truncateSimplex 2 ul) := by
      rw [← HD_TRUNCATE_SIMPLEX ul 2 (by have := hul.1; omega)]
      exact HD_IN_SET_OF_LIST _ (by
        rw [LENGTH_TRUNCATE_SIMPLEX 2 ul (by have := hul.1; omega)]
        norm_num)
    have humem : hdV ul ∈ setOfList (truncateSimplex 2 vl) := by
      rw [← htrunc]
      exact hdul_mem2
    by_cases hbu : hl (truncateSimplex 2 ul) < Real.sqrt 2
    · by_cases hbv : hl (truncateSimplex 2 vl) < Real.sqrt 2
      · exact p15_mxi_eq_of_lt V ul vl hp hul hvl hω2 hω3 hbu hbv humem
      · exfalso
        rw [hhl] at hbu
        exact absurd hbu (not_lt.mpr (le_of_not_gt hbv))
    · by_cases hbv : hl (truncateSimplex 2 vl) < Real.sqrt 2
      · exfalso
        rw [← hhl] at hbv
        exact absurd hbv (not_lt.mpr (le_of_not_gt hbu))
      · simp only [mxi, if_pos (le_of_not_gt hbu), if_pos (le_of_not_gt hbv), hω2]


/-- marchal3.hl:4172 `MCELL_ID_MXI_2` (`MCELL_ID_MXI` without `HD ul = HD vl`). -/
theorem MCELL_ID_MXI_2 (V : Set V3) (i j : ℕ) (ul vl : List V3) (hp : Packing V)
    (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (heq : mcell i V ul = mcell j V vl) (hnel : ¬nullSet (mcell i V ul))
    (hi : i ∈ ({2, 3} : Set ℕ)) (hj : j ∈ ({2, 3} : Set ℕ)) :
    mxi V ul = mxi V vl := by
  exact p15_mxi_2_main V i j ul vl hp hs hul hvl heq hnel hi hj

/-- marchal3.hl:4942 `DIHX_SYM`. -/
theorem DIHX_SYM (V : Set V3) (X : Set V3) (u v : V3) (hp : Packing V) (hs : saturated V)
    (hm : mcellSet V X) (he : {u, v} ∈ edgeX V X) :
    dihX V X (u, v) = dihX V X (v, u) := sorry

/-! ## marchal3.hl:5833-6809: gammaY, beta bookkeeping, klemma counting kit -/

/-- marchal3.hl:5833 `gammaY`: the per-edge contribution `dihX * f (hl [u;v])`
on `edgeX V X` (zero off `edgeX`); the HOL pattern abstraction `\{u,v}. ...`
is rendered through `pairOf`. -/
noncomputable def gammaY (V : Set V3) (X : Set V3) (f : ℝ → ℝ) : Set V3 → ℝ :=
  fun e => if e ∈ edgeX V X then
    dihX V X (pairOf e) * f (hl [(pairOf e).1, (pairOf e).2])
  else 0

/-- marchal3.hl:5844 `BETA_SET_2_THM`. -/
theorem BETA_SET_2_THM {β : Type*} [Nonempty β] (g : Set V3 → β) (u0 v0 : V3) :
    patternPair (fun u v => g {u, v}) {u0, v0} = g {u0, v0} :=
  pre_beta _ _ _ ⟨g, fun _ _ => rfl⟩

/-- marchal3.hl:5854 `SUM_PAIR_2_SET` (needs a `SUM_GROUP` reindexing lemma not
yet ported). -/
theorem SUM_PAIR_2_SET (f : Set V3 → ℝ) (s : Set V3) (d : ℝ) (hs : s.Finite) :
    setSum {p : V3 × V3 | p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2 ∧ dist p.1 p.2 ≤ d}
        (fun p => f {p.1, p.2}) =
      2 * setSum {e : Set V3 | ∃ m ∈ s, ∃ n ∈ s, m ≠ n ∧ dist m n ≤ d ∧ e = {m, n}} f :=
  sorry

/-- marchal3.hl:5893 `H0_LT_SQRT2`. -/
theorem H0_LT_SQRT2 : h0 < Real.sqrt 2 := by
  have h2 : ((1.26 : ℝ) ^ 2) < 2 := by norm_num
  have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1.26 ^ 2) h2
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.26)] at this

/-- marchal3.hl:5902 `gamma_y_pos_le`. -/
theorem gamma_y_pos_le (V : Set V3) (X : Set V3) (e : Set V3) (hp : Packing V)
    (hs : saturated V) (hm : mcellSet V X) (he : edgeX V X e) :
    0 ≤ gammaY V X lmfun e := by
  unfold gammaY
  split_ifs with hX
  · exact mul_nonneg (DIHX_RANGE V X _ _).1 (lmfun_pos_le _)
  · exact le_refl 0

/-- marchal3.hl:5944 `CARD_LIST_klemma`. -/
theorem CARD_LIST_klemma {α : Type*} (s : Set α) (t : Set (List α)) (hs : s.Finite)
    (ht : t.Finite) :
    Nat.card {y : List α | ∃ u0 ∈ s, ∃ y1 ∈ t, y = u0 :: y1} = Nat.card s * Nat.card t := by
  have heq : {y : List α | ∃ u0 ∈ s, ∃ y1 ∈ t, y = u0 :: y1}
      = (fun p : α × List α => p.1 :: p.2) '' (s ×ˢ t) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨u0, hu0, y1, hy1, rfl⟩
      exact ⟨(u0, y1), ⟨hu0, hy1⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
  rw [heq, p15_card_image _ _ (fun p _ q _ h => by
    exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2)]
  rw [Nat.card_congr (Equiv.Set.prod s t), Nat.card_prod]

/-- marchal3.hl:5976 `CARD_LIST_klemma_2`. -/
theorem CARD_LIST_klemma_2 {α : Type*} (s : Set α) (t : Set (List α)) (hs : s.Finite)
    (ht : t.Finite) :
    Nat.card {y : List α | ∃ u0 ∈ s, ∃ y1 ∈ t, y = u0 :: y1} = Nat.card s * Nat.card t := by
  have heq : {y : List α | ∃ u0 ∈ s, ∃ y1 ∈ t, y = u0 :: y1}
      = (fun p : α × List α => p.1 :: p.2) '' (s ×ˢ t) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨u0, hu0, y1, hy1, rfl⟩
      exact ⟨(u0, y1), ⟨hu0, hy1⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
  rw [heq, p15_card_image _ _ (fun p _ q _ h => by
    exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2)]
  rw [Nat.card_congr (Equiv.Set.prod s t), Nat.card_prod]

/-- marchal3.hl:6019 `CARD_LIST_4_klemma`. -/
theorem CARD_LIST_4_klemma {α : Type*} (s : Set α) (hs : s.Finite) :
    Nat.card {y : List α | ∃ u0 ∈ s, ∃ u1 ∈ s, ∃ u2 ∈ s, ∃ u3 ∈ s, y = [u0, u1, u2, u3]}
      = Nat.card s * Nat.card s * Nat.card s * Nat.card s := by
  have heq : {y : List α | ∃ u0 ∈ s, ∃ u1 ∈ s, ∃ u2 ∈ s, ∃ u3 ∈ s, y = [u0, u1, u2, u3]}
      = (fun p : ((α × α) × α) × α => [p.1.1.1, p.1.1.2, p.1.2, p.2]) ''
          ((s ×ˢ s) ×ˢ s) ×ˢ s := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨u0, hu0, u1, hu1, u2, hu2, u3, hu3, rfl⟩
      exact ⟨(((u0, u1), u2), u3), ⟨⟨⟨hu0, hu1⟩, hu2⟩, hu3⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1.1.1, hp.1.1.1, p.1.1.2, hp.1.1.2, p.1.2, hp.1.2, p.2, hp.2, rfl⟩
  rw [heq, p15_card_image _ _ (fun p _ q _ h => by
    have h' : [p.1.1.1, p.1.1.2, p.1.2, p.2] = [q.1.1.1, q.1.1.2, q.1.2, q.2] := h
    have h1 := List.cons.inj h'
    have h2 := List.cons.inj h1.2
    have h3 := List.cons.inj h2.2
    have h4 := List.cons.inj h3.2
    exact Prod.ext (Prod.ext (Prod.ext h1.1 h2.1) h3.1) h4.1)]
  rw [Nat.card_congr (Equiv.Set.prod ((s ×ˢ s) ×ˢ s) s), Nat.card_prod,
    Nat.card_congr (Equiv.Set.prod (s ×ˢ s) s), Nat.card_prod,
    Nat.card_congr (Equiv.Set.prod s s), Nat.card_prod]

/-- marchal3.hl:6065 `BOUNDS_VGEN_klemma`. -/
theorem BOUNDS_VGEN_klemma (u0 : V3) (V : Set V3) (r : ℝ) (hr : 0 ≤ r) (hp : Packing V) :
    ((Nat.card ↥(V ∩ Metric.ball u0 r) : ℕ) : ℝ) ≤ (r + 1) ^ 3 := sorry

/-- marchal3.hl:6142 `BOUNDS_V4_klemma`. -/
theorem BOUNDS_V4_klemma (u0 : V3) (V : Set V3) (hp : Packing V) :
    Nat.card ↥(V ∩ Metric.ball u0 4) ≤ 125 := by
  have h := BOUNDS_VGEN_klemma u0 V 4 (by norm_num) hp
  have hle : ((Nat.card ↥(V ∩ Metric.ball u0 4) : ℕ) : ℝ) ≤ (4 + 1) ^ 3 := h
  norm_num at hle ⊢
  exact_mod_cast hle

/-- marchal3.hl:6216 `CARD_MCELL_CONTAINS_POINT_klemma`. -/
theorem CARD_MCELL_CONTAINS_POINT_klemma :
    ∃ c : ℕ, ∀ (V : Set V3) (u0 : V3), saturated V → Packing V → u0 ∈ V →
      Nat.card {X : Set V3 | mcellSet V X ∧ u0 ∈ VX V X} ≤ c := sorry

/-- marchal3.hl:6450 `MCELL_SUBSET_BALL8_2`. -/
theorem MCELL_SUBSET_BALL8_2 (V : Set V3) (X : Set V3) (v : V3) (hp : Packing V)
    (hs : saturated V) (hm : mcellSet V X) (hv : v ∈ X) : X ⊆ Metric.ball v 8 := by
  simp only [mcellSet] at hm
  obtain ⟨i, ul, rfl, hb⟩ := hm
  exact MCELL_SUBSET_BALL8 v ul i V hp hs hb hv

/-- marchal3.hl:6463 `EDGEX_SUBSET_MCELL` (via PackingAuto10 `HDTFNFZ`:
`VX V X = V ∩ X` on non-null mcells). -/
theorem EDGEX_SUBSET_MCELL (V : Set V3) (X : Set V3) (e : Set V3) (hp : Packing V)
    (hs : saturated V) (hm : mcellSet V X) (he : edgeX V X e) : e ⊆ X := by
  simp only [mcellSet] at hm
  obtain ⟨i, ul, rfl, hb⟩ := hm
  simp only [edgeX] at he
  obtain ⟨u0, u1, rfl, hu0, hu1, hne⟩ := he
  by_cases hnull : nullSet (mcell i V ul)
  · exfalso
    rw [VX, if_pos hnull] at hu0
    exact absurd hu0 (by simp)
  · have hVX : VX V (mcell i V ul) = V ∩ mcell i V ul :=
      @HDTFNFZ V ul i u0 (mcell i V ul) hs hp hb rfl hnull
    intro z hz
    rcases Set.mem_insert_iff.mp hz with hz0 | hz'
    · rw [hz0]
      exact (hVX ▸ hu0 : u0 ∈ V ∩ mcell i V ul).2
    · rcases Set.mem_singleton_iff.mp hz' with hz1
      rw [hz1]
      exact (hVX ▸ hu1 : u1 ∈ V ∩ mcell i V ul).2

/-- marchal3.hl:6474 `CRITICAL_EDGEX_SUBSET_MCELL`. -/
theorem CRITICAL_EDGEX_SUBSET_MCELL (V : Set V3) (X : Set V3) (e : Set V3) (hp : Packing V)
    (hs : saturated V) (hm : mcellSet V X) (he : criticalEdgeX V X e) : e ⊆ X := by
  simp only [criticalEdgeX] at he
  rcases he with ⟨u0, u1, rfl, hex, _, _⟩
  exact EDGEX_SUBSET_MCELL V X {u0, u1} hp hs hm hex

/-- marchal3.hl:6485 `FINITE_VX`. -/
theorem FINITE_VX (V : Set V3) (X : Set V3) (hp : Packing V) (hs : saturated V)
    (hm : mcellSet V X) : (VX V X).Finite := by
  by_cases hnull : nullSet X
  · rw [VX, if_pos hnull]
    exact Set.finite_empty
  · by_cases hp0 : (cellParams V X).1 = 0
    · have hvx : VX V X = ∅ := by rw [VX, if_neg hnull, if_pos hp0]
      rw [hvx]
      exact Set.finite_empty
    · have hvx : VX V X =
          setOfList (truncateSimplex ((cellParams V X).1 - 1) (cellParams V X).2) := by
        rw [VX, if_neg hnull, if_neg hp0]
      rw [hvx]
      exact p15_setOfList_finite _

/-- marchal3.hl:6518 `CARD_EDGEX_LE_16`. -/
theorem CARD_EDGEX_LE_16 (V : Set V3) (X : Set V3) (hp : Packing V) (hs : saturated V)
    (hm : mcellSet V X) : Nat.card (edgeX V X) ≤ 16 := sorry

/-- marchal3.hl:6616 `gamma_y_lmfun_bound2`. -/
theorem gamma_y_lmfun_bound2 :
    ∃ d : ℝ, ∀ (V : Set V3) (X : Set V3) (e : Set V3), Packing V → saturated V →
      mcellSet V X → edgeX V X e → gammaY V X lmfun e ≤ d := by
  refine ⟨Real.pi * (h0 / (h0 - 1)), ?_⟩
  intro V X e _ _ _ he
  unfold gammaY
  split_ifs with hX
  · have h1 : dihX V X (pairOf e) ≤ Real.pi := DIHX_LE_PI V X _ _
    have h2 : lmfun (hl [(pairOf e).1, (pairOf e).2]) ≤ h0 / (h0 - 1) := by
      refine lmfun_bounded ?_
      rw [HL_2]
      positivity
    exact mul_le_mul h1 h2 (lmfun_pos_le _) Real.pi_pos.le
  · exact mul_nonneg Real.pi_pos.le (by norm_num [h0])

/-- marchal3.hl:6671 `BOUND_GAMMA_X_lmfun`. -/
theorem BOUND_GAMMA_X_lmfun :
    ∃ c : ℝ, ∀ (V : Set V3) (X : Set V3), Packing V → saturated V → mcellSet V X →
      gammaX V X lmfun ≤ c := sorry

end Kepler.Text
