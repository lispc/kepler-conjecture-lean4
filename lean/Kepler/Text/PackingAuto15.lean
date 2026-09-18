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
  (`MCELL_ID_*`, `CONIC_CAP_*`, `LEFT_ACTION_LIST_*`, `DIHX_SYM`,
  the klemma bound kit, ...) are `sorry` skeletons faithful to the source
  statements, for later lanes.

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
import Kepler.Text.Polytope
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

/-- marchal3.hl:101 `HD_IN_MCELL`. -/
theorem HD_IN_MCELL (V : Set V3) (ul : List V3) (i : ℕ) (X : Set V3)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell i V ul)
    (hne : X ≠ ∅) (hi : i ≠ 0) : hdV ul ∈ X := sorry

/-- marchal3.hl:231 `FINITE_MCELL_SET_lemma1`. -/
theorem FINITE_MCELL_SET_lemma1 (V : Set V3) (ul : List V3) (i : ℕ) (r : ℝ) (X : Set V3)
    (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul) (hX : X = mcell i V ul)
    (hball : X ⊆ Metric.ball 0 r) (hne : X ≠ ∅) :
    ∀ u ∈ setOfList ul, u ∈ Metric.ball 0 (r + 6) := sorry

/-- marchal3.hl:329 `FINITE_MCELL_SET_LEMMA_concl` (a plain statement `let`
in the source). -/
def FINITE_MCELL_SET_LEMMA_concl : Prop :=
  ∀ (V : Set V3) (r : ℝ), Packing V → saturated V →
    {X : Set V3 | X ⊆ Metric.ball 0 r ∧ mcellSet V X}.Finite

/-- marchal3.hl:332 `FINITE_MCELL_SET_LEMMA` (statement is
`FINITE_MCELL_SET_LEMMA_concl`). -/
theorem FINITE_MCELL_SET_LEMMA : FINITE_MCELL_SET_LEMMA_concl := sorry

/-- marchal3.hl:443 `CARD_BOUNDARY_INT_BALL_BOUND_1`. -/
theorem CARD_BOUNDARY_INT_BALL_BOUND_1 (x : V3) (k1 k2 : ℝ) (hk1 : 0 < k1) (hk2 : 0 < k2) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      (((Nat.card ↥((intBall x (r + k1)) \ (intBall x (r - k2))) : ℕ) : ℝ)) ≤ C * r ^ 2 := sorry

/-- marchal3.hl:513 `CARD_BOUNDARY_INT_BALL_BOUND`. -/
theorem CARD_BOUNDARY_INT_BALL_BOUND (x : V3) (k1 k2 : ℝ) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      (((Nat.card ↥((intBall x (r + k1)) \ (intBall x (r - k2))) : ℕ) : ℝ)) ≤ C * r ^ 2 := sorry

/-- marchal3.hl:610 `BOUNDARY_VOLUME`. -/
theorem BOUNDARY_VOLUME (p : V3) (k1 k2 : ℝ) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      volume.real (Metric.ball p (r + k1) \ Metric.ball p (r - k2)) ≤ C * r ^ 2 := sorry

/-- marchal3.hl:737 `PACKING_BALL_BOUNDARY`. -/
theorem PACKING_BALL_BOUNDARY (V : Set V3) (p : V3) (k1 k2 : ℝ) (hp : Packing V) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      (((Nat.card ↥((V ∩ Metric.ball p (r + k1)) \ (V ∩ Metric.ball p (r - k2))) : ℕ) : ℝ))
        ≤ C * r ^ 2 := sorry

/-- marchal3.hl:831 `MCELL_SUBSET_BALL_4`. -/
theorem MCELL_SUBSET_BALL_4 (V : Set V3) (X : Set V3) (hp : Packing V) (hs : saturated V)
    (hm : mcellSet V X) : ∃ p : V3, X ⊆ Metric.ball p 4 := sorry

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

/-- marchal3.hl:1054 `HL_LE_SQRT2_IMP_BARV_1`. -/
theorem HL_LE_SQRT2_IMP_BARV_1 (V : Set V3) (u0 u1 : V3) (hs : saturated V) (hp : Packing V)
    (hu0 : u0 ∈ V) (hu1 : u1 ∈ V) (hne : u0 ≠ u1) (h : hl [u0, u1] < Real.sqrt 2) :
    barV V 1 [u0, u1] := sorry

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

/-- marchal3.hl:1264 `MCELL_ID_OMEGA_LIST_N`. -/
theorem MCELL_ID_OMEGA_LIST_N (V : Set V3) (i j : ℕ) (ul vl : List V3) (hp : Packing V)
    (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (heq : mcell i V ul = mcell j V vl) (hnel : ¬nullSet (mcell i V ul))
    (hi : i ∈ ({2, 3, 4} : Set ℕ)) (hj : j ∈ ({2, 3, 4} : Set ℕ)) :
    i = j ∧ ∀ k : ℕ, i - 1 ≤ k ∧ k ≤ 3 → omegaListN V ul k = omegaListN V vl k := sorry

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

/-- marchal3.hl:2184 `FINITE_EDGE_X2`. -/
theorem FINITE_EDGE_X2 (V : Set V3) (e : Set V3) (u0 u1 : V3) (hp : Packing V)
    (hs : saturated V) (he : e = {u0, u1}) :
    {X : Set V3 | mcellSet V X ∧ edgeX V X e}.Finite := sorry

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

/-- marchal3.hl:2465 `MCELL_SUBSET_BALL8_1`. -/
theorem MCELL_SUBSET_BALL8_1 (v : V3) (ul : List V3) (i : ℕ) (V : Set V3)
    (hi : i ≤ 4) (hp : Packing V) (hs : saturated V) (hb : barV V 3 ul)
    (hv : v ∈ mcell i V ul) : mcell i V ul ⊆ Metric.ball v 8 := sorry

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

/-- marchal3.hl:2602 `FINITE_MCELL_SET_LEMMA_2`. -/
theorem FINITE_MCELL_SET_LEMMA_2 (V : Set V3) (r : ℝ) (s : V3) (hp : Packing V)
    (hs : saturated V) : {X : Set V3 | X ⊆ Metric.ball s r ∧ mcellSet V X}.Finite := sorry

/-! ## marchal3.hl:2623-3671: conic caps, measurability, pair calculus -/

/-- marchal3.hl:2623 `CONIC_CAP_WEDGE_EQ_0`. -/
theorem CONIC_CAP_WEDGE_EQ_0 (v0 v1 : V3) (a r : ℝ) (w1 w2 : V3) (ha : a < 1) (hr : 0 < r)
    (h : volume.real (conicCap v0 v1 r a ∩ wedge v0 v1 w1 w2) = 0) :
    Coplanar ℝ ({v0, v1, w1, w2} : Set V3) := sorry

/-- marchal3.hl:2657 `CONIC_CAP_AFF_GT_EQ_0`. -/
theorem CONIC_CAP_AFF_GT_EQ_0 (v0 v1 : V3) (a r : ℝ) (w1 w2 : V3) (ha : a < 1) (hr : 0 < r)
    (h : volume.real (conicCap v0 v1 r a ∩ affGt {v0, v1} {w1, w2}) = 0) :
    Coplanar ℝ ({v0, v1, w1, w2} : Set V3) := sorry

/-- marchal3.hl:2708 `CONIC_CAP_INTER_CONVEX_HULL_4_GT_0`. -/
theorem CONIC_CAP_INTER_CONVEX_HULL_4_GT_0 (u0 u1 w1 w2 : V3) (r a : ℝ) (hr : 0 < r)
    (ha : a < 1) (ha0 : 0 ≤ a) (hcop : ¬Coplanar ℝ ({u0, u1, w1, w2} : Set V3)) :
    0 < volume.real (conicCap u0 u1 r a ∩ convexHull ℝ {u0, u1, w1, w2}) := sorry

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

/-- marchal3.hl:4172 `MCELL_ID_MXI_2` (`MCELL_ID_MXI` without `HD ul = HD vl`). -/
theorem MCELL_ID_MXI_2 (V : Set V3) (i j : ℕ) (ul vl : List V3) (hp : Packing V)
    (hs : saturated V) (hul : barV V 3 ul) (hvl : barV V 3 vl)
    (heq : mcell i V ul = mcell j V vl) (hnel : ¬nullSet (mcell i V ul))
    (hi : i ∈ ({2, 3} : Set ℕ)) (hj : j ∈ ({2, 3} : Set ℕ)) :
    mxi V ul = mxi V vl := sorry

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
