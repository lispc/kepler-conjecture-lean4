/-
Kepler/Text/PackingAuto12.lean — port of flyspeck `scripts/packing/marchal2.hl`
(6603 lines; the mcell4 / flat-sheet support machinery: radial annotations,
closedness/measurability of cells and cones, omega_list/mxi explicit forms,
convex-hull splitting, projections, affine-hull algebra, left_action_list).

HOL source file map (marchal2.hl line numbers):
  AFF_GE_2_2:57  MEASURABLE_ROGERS:68  CONVEX_RCONE_GE:90
  FINITE_PERMUTE_3:163  FINITE_PERMUTE_4:166  DIHV_SYM:194
  RCONE_GT_SUBSET_RCONE_GE:255  MCELL_EXPLICIT:262
  EVENTUALLY_RADIAL_EMPTY:291  EVENTUALLY_RADIAL_NOT_IN_CLOSED_SET:306
  CLOSED_CONVEX_HULL_FINITE:349  CLOSED_ROGERS:355
  CLOSED_SET_OF_LIST_KY_LEMMA_1:376  CLOSED_SET_OF_LIST_KY_LEMMA_2:396
  CLOSED_RCONE_GE:413  BARV_IMP_HL_1_POS_LT:487  CLOSED_MCELL:541
  BARV_IMP_u0_IN_V:609  ROGERS_INTER_V_LEMMA:626  CONVEX_HULL_4:669
  REAL_LE_DIV_SIMPLIFY_KY_LEMMA:681
  EVENTUALLY_RADIAL_CONVEX_HULL_4_sub1:697
  U0_NOT_IN_CONVEX_HULL_FROM_ROGERS:1014  RADIAL_VS_RADIAL_NORM:1151
  EVENTUALLY_RADIAL_INTER:1161  SET_EQ_LEMMA:1242  SET_OF_0_TO_3:1245
  SET_OF_0_TO_2:1260  ZERO_LT_SQRT_2:1273  RCONE_GE_TRANS:1284
  RCONE_GE_INTER_VORONOI_CLOSED_PROJECTION_KY_LEMMA:1302
  RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE:1440
  OMEGA_LIST_1_EXPLICIT_NEW:1693  IN_SET_IMP_IN_CONVEX_HULL_SET:1724
  CONVEX_HULL_BREAK_KY_LEMMA:1737  CONVEX_HULL_4_SUBSET_AFF_GE_2_2:2002
  AFF_INDEPENDENT_SET_OF_LIST_BARV:2117
  VORONOI_LIST_3_SINGLETON_EXPLICIT:2231  SIMPLEX_FURTHEST_LT_2:2393
  DIST_BETWEEN_FURTHEST_LT:2424  ROGERS_EXPLICIT:2445
  SEGMENT_INTER_CBALL_LEMMA:2481  CLOSEST_POINT_SING:2502  MXI_EXPLICIT:2516
  CONVEX_HULL_4_IMP_2_2:2864  MXI_EXPLICIT_OLD:2932  proj_point:2942 (def)
  projection_proj_point:2945  PRO_EXP:2949  BETWEEN_PROJ_POINT:2955
  PARALLEL_PROJECTION:2971  OMEGA_LIST_TRUNCATE_1_NEW1:3027
  OMEGA_LIST_TRUNCATE_1_NEW2:3037  OMEGA_LIST_TRUNCATE_2_NEW1:3045
  IN_AFFINE_KY_LEMMA1:3055  AFFINE_SUBSET_KY_LEMMA:3065
  TRANSLATE_AFFINE_KY_LEMMA1:3076  IN_AFFINE_HULL_KY_LEMMA3:3097
  IN_AFFINE_HULL_KY_LEMMA3_alt:3130  IN_AFFINE_HULL_3_KY_LEMMA2:3142
  SUM_CLAUSES_alt:3163  SUM_DIS4:3168  CARD4_IMP_DISTINCT:3225
  VSUM_CLAUSES_alt:3233  VSUM_DIS4:3237  AFFINE_DEPENDENT_KY_LEMMA1:3294
  IN_2_2_IMP_CONVEX_HULL_4:3410  BETWEEN_TRANS_3_CASES:3425
  OMEGA_LIST_UP_TO_2:3520  CONVEX_HULL_KY_LEMMA_5:3536
  KY_PERMUTES_2_PERMUTES_3:3665  TABLE_4:3673  MEM_LEFT_ACTION_LIST_2:3684
  SET_OF_LIST_LEFT_ACTION_LIST_2:3780  OMEGA_LIST_2_EXPLICIT_NEW:3788
  INTER_RCONE_GE_IMP_BETWEEN_PROJ_POINT:3819
  INTER_RCONE_GE_LT_lemma:3863  INTER_RCONE_GE_LE_lemma:4162
  LEFT_ACTION_LIST_PROPERTIES:4460  MEM_LEFT_ACTION_LIST_3:5557
  SET_OF_LIST_LEFT_ACTION_LIST_3:5653  LEFT_ACTION_LIST_1_EXPLICIT:5663
  LEFT_ACTION_LIST_1_PROPERTIES:5848  NUMSEG_012:6444
  SET_OF_LIST_TRUN2_LEFT_ACTION_LIST2:6452  SQRT2_LT_2:6594
  (also the alias `INTER_RCONE_GE_dist_lemma1:4156 := INTER_RCONE_GE_LT_lemma`,
  stated below as a derived lemma, and the proof-tactic bundles
  TRUONG_SET_TAC:172 / PRESET_TAC:177 / allthms:175, which are HOL tactic
  scaffolding and intentionally not ported.)

Encoding notes:
  - HOL `real^3` ↔ `V3` (Kepler.Geom), `real^N` statements restricted to `V3`
    where the Kepler API fixes the type (noted per-theorem).
  - `measurable S` ↔ `MeasurableSet S` (PackingAuto10.MEASURABLE_MCELL style).
  - `between x (a,b)` ↔ `x ∈ segment ℝ a b` (closed segment; Polytope.lean).
  - HOL `projection e x` (project x onto span e) does not exist in Kepler;
    Kepler.Text.PackingAuto5.projection v d = v - ((v⬝ᵥd)/(d⬝ᵥd)) • d.
    We reconstruct BOTH HOL notions privately:
      projHL e x      = x - projection x e           (HOL `projection e x`)
      proj_point e x  = x - projHL e x               (HOL `proj_point`, the
        one new_definition of marchal2.hl:2942; the component of x along e).
    PRO_EXP confirms the explicit form.
  - `sum`/`vsum` over sets ↔ Finset sums; SUM_DIS4/VSUM_DIS4 are stated over
    Finsets (HOL `CARD {x,y,z,t} = 4` hypothesis kept).
  - `p permutes s` ↔ `Kepler.Text.permutes` (PackingAuto2), the POINTWISE
    encoding `∀ x, x ∈ s ↔ p x ∈ s`. Caveat documented in PackingAuto10: this
    weak encoding does not force `p` to fix the complement of `s`, so
    statements that (as in HOL, with the complement-fixing `permutes`) count
    permutations of `s`, or consume values of `p`/`inverse p` outside `s`,
    are FALSE as encoded; they are stated faithfully and sorried with a
    caveat note.
  - RECONSTRUCTED DEFS: the radial annotation kit of marchal2
    (`radial`, `radial_norm`, `eventually_radial`) is defined in a flyspeck
    file ABSENT from this export. Reconstructed here as private `_p12` defs
    from their five usage sites below, matching the standard flyspeck shapes:
      radial r x C          := 0 ≤ r ∧ ∀ ε > 0, ∃ u, r ≤ dist u x ∧
                               dist u x ≤ r + ε ∧ u ∉ C
      radial_norm r x C     := 0 ≤ r ∧ ∀ ε > 0, ∃ u, dist u x ∈ [r, r+ε] ∧
                               u ∉ C   (so RADIAL_VS_RADIAL_NORM is
                               essentially definitional)
      eventually_radial x C := ∃ r, radial r x C
    The "u ∉ C" orientation is forced by EVENTUALLY_RADIAL_EMPTY:291 and
    EVENTUALLY_RADIAL_NOT_IN_CLOSED_SET:306 (both proved honestly below).
  - `mcell_set`: NOT USED anywhere in this export of marchal2.hl (checked by
    grep); the dispatch constants mcell0..mcell4/mcell it would collect are
    public in PackingAuto2 (:316-:359) and `mcellSet` itself is public at
    PackingAuto2:363. No private reconstruction was therefore necessary;
    MCELL_EXPLICIT below is proved from `Kepler.Text.mcell` directly.
-/

import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto5
import Kepler.Text.PackingAuto6
import Kepler.Text.PackingAuto7
import Kepler.Text.PackingAuto8
import Kepler.Text.PackingAuto10
import Kepler.Text.PackingAuto11
import Mathlib

set_option maxHeartbeats 5000000

noncomputable section

namespace Kepler.Text

open Kepler.Geom Set Classical MeasureTheory

/-! ## Reconstructed radial annotations (defining file absent from export) -/

/-- HOL `radial r x C` (reconstruction; see file header). -/
private def radial_p12 (r : ℝ) (x : V3) (C : Set V3) : Prop :=
  0 ≤ r ∧ ∀ ε : ℝ, 0 < ε → ∃ u : V3, r ≤ dist u x ∧ dist u x ≤ r + ε ∧ u ∉ C

/-- HOL `radial_norm r x C` (reconstruction; see file header). -/
private def radialNorm_p12 (r : ℝ) (x : V3) (C : Set V3) : Prop :=
  0 ≤ r ∧ ∀ ε : ℝ, 0 < ε → ∃ u : V3, dist u x ∈ Icc r (r + ε) ∧ u ∉ C

/-- HOL `eventually_radial x C` (reconstruction; see file header). -/
private def eventuallyRadial_p12 (x : V3) (C : Set V3) : Prop := ∃ r, radial_p12 r x C

/-! ## Private helper kit -/

/-- HOL `projection e x` reconstruction (see file header). -/
private def projHL (e x : V3) : V3 := projection x e

/-- `convex hull {a, b} = segment ℝ a b`. -/
private theorem p12_hull_pair (a b : V3) : convexHull ℝ {a, b} = segment ℝ a b := by
  refine Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · refine convexHull_min (fun w hw => ?_) (convex_segment (𝕜 := ℝ) a b) hz
    rcases hw with rfl | hw'
    · exact left_mem_segment ℝ _ _
    · rw [hw']
      exact right_mem_segment ℝ _ _
  · rcases hz with ⟨u, w, hu, hw, huw, rfl⟩
    have hconv := convex_convexHull (𝕜 := ℝ) (s := ({a, b} : Set V3))
    exact hconv (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
      hu hw huw

/-- A finite set's `toFinset` is determined by its elements. -/
private theorem p12_finite_toFinset_eq {S : Set V3} {hS : S.Finite} {T : Finset V3}
    (h : S = (T : Set V3)) : hS.toFinset = T := by
  refine Finset.coe_inj.1 ?_
  rw [hS.coe_toFinset, h]

/-- A vertex of `s` lies in `affGe s t` (finite `s ∪ t`). -/
private theorem p12_mem_affGe_vertex {s t : Set V3} (hfin : (s ∪ t).Finite) {v : V3}
    (hv : v ∈ s) : v ∈ affGe s t := by
  have hvF : v ∈ hfin.toFinset := by
    simpa [Set.Finite.mem_toFinset] using Set.mem_union_left _ hv
  refine ⟨fun p => if p = v then 1 else 0, hfin, ?_, ?_, ?_⟩
  · show v = ∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0) • p
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v → (if p = v then (1:ℝ) else 0) • p = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp
  · intro p hp
    by_cases hpv : p = v <;> simp [hpv]
  · show (∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0)) = 1
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v → (if p = v then (1:ℝ) else 0) = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp

/-- A vertex of `t` lies in `affGe s t` (finite `s ∪ t`). -/
private theorem p12_mem_affGe_vertex_t {s t : Set V3} (hfin : (s ∪ t).Finite) {v : V3}
    (hv : v ∈ t) : v ∈ affGe s t := by
  have hvF : v ∈ hfin.toFinset := by
    simpa [Set.Finite.mem_toFinset] using Set.mem_union_right _ hv
  refine ⟨fun p => if p = v then 1 else 0, hfin, ?_, ?_, ?_⟩
  · show v = ∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0) • p
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v → (if p = v then (1:ℝ) else 0) • p = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp
  · intro p hp
    by_cases hpv : p = v <;> simp [hpv]
  · show (∑ p ∈ hfin.toFinset, (if p = v then (1:ℝ) else 0)) = 1
    have heq : ∀ p ∈ hfin.toFinset, p ≠ v →
        (if p = v then (1:ℝ) else 0) = 0 := by
      intro p _ hpv
      simp [hpv]
    rw [Finset.sum_eq_single v heq (fun h => absurd hvF h)]
    simp

/-- `affGe s t` is convex for finite `s ∪ t` (blends of admissible weight
functions are admissible). -/
private theorem p12_convex_affGe {s t : Set V3} (hfin : (s ∪ t).Finite) :
    Convex ℝ (affGe s t) := by
  intro x hx y hy a b ha hb hab
  simp only [affGe, Affsign, Set.mem_setOf_eq] at hx hy
  obtain ⟨f1, _, hx1, hx2, hx3⟩ := hx
  obtain ⟨f2, _, hy1, hy2, hy3⟩ := hy
  refine ⟨fun p => a * f1 p + b * f2 p, hfin, ?_, ?_, ?_⟩
  · have key : ∀ (g : V3 → ℝ) (c : ℝ), ∑ q ∈ hfin.toFinset, (c * g q) • q
        = c • ∑ q ∈ hfin.toFinset, g q • q := by
      intro g c
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [smul_smul]
    have hsum1 : ∑ q ∈ hfin.toFinset, (a * f1 q + b * f2 q) • q
        = ∑ q ∈ hfin.toFinset, ((a * f1 q) • q + (b * f2 q) • q) := by
      exact Finset.sum_congr rfl fun q _ => by rw [add_smul]
    rw [hsum1, Finset.sum_add_distrib, key, key, hx1, hy1]
  · intro p hp
    have h1 : 0 ≤ f1 p := hx2 p hp
    have h2 : 0 ≤ f2 p := hy2 p hp
    show 0 ≤ a * f1 p + b * f2 p
    exact add_nonneg (mul_nonneg ha h1) (mul_nonneg hb h2)
  · show (∑ q ∈ hfin.toFinset, (a * f1 q + b * f2 q)) = 1
    have h3' : ∑ q ∈ hfin.toFinset, (a * f1 q + b * f2 q)
        = a * ∑ q ∈ hfin.toFinset, f1 q + b * ∑ q ∈ hfin.toFinset, f2 q := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [h3', hx3, hy3]
    simp
    linarith

/-! ## marchal2.hl:57 AFF_GE_2_2 -/

/-- HOL `AFF_GE_2_2` (marchal2.hl:57): explicit weight characterization of
`aff_ge {x,v} {w,z}` under disjointness of the two pairs. -/
theorem AFF_GE_2_2 (x v w z : V3) (hdis : Disjoint ({x, v} : Set V3) ({w, z} : Set V3)) :
    affGe {x, v} {w, z} =
      {y : V3 | ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t3 ∧ 0 ≤ t4 ∧ t1 + t2 + t3 + t4 = 1 ∧
        y = t1 • x + t2 • v + t3 • w + t4 • z} := by
  have hxd : x ≠ w := by
    intro e
    have h1 : (x : V3) ∈ ({x, v} : Set V3) := by simp
    have h2 : (x : V3) ∈ ({w, z} : Set V3) := by rw [e]; simp
    exact Set.disjoint_left.1 hdis h1 h2
  have hxz : x ≠ z := by
    intro e
    have h1 : (x : V3) ∈ ({x, v} : Set V3) := by simp
    have h2 : (x : V3) ∈ ({w, z} : Set V3) := by rw [e]; simp
    exact Set.disjoint_left.1 hdis h1 h2
  have hvd : v ≠ w := by
    intro e
    have h1 : (v : V3) ∈ ({x, v} : Set V3) := by simp
    have h2 : (v : V3) ∈ ({w, z} : Set V3) := by rw [e]; simp
    exact Set.disjoint_left.1 hdis h1 h2
  have hvz : v ≠ z := by
    intro e
    have h1 : (v : V3) ∈ ({x, v} : Set V3) := by simp
    have h2 : (v : V3) ∈ ({w, z} : Set V3) := by rw [e]; simp
    exact Set.disjoint_left.1 hdis h1 h2
  have hf1 : ({x, v} : Set V3).Finite := by simp
  have hf2 : ({w, z} : Set V3).Finite := by simp
  have hfinUV : (({x, v} : Set V3) ∪ {w, z}).Finite := hf1.union hf2
  ext y
  simp only [affGe, Affsign, Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hfin, hy, hneg, hsum⟩
    rcases eq_or_ne x v with rfl | hxv
    · rcases eq_or_ne w z with rfl | hwz
      · -- x = v, w = z : F = {x, w}
        have hF' : hfin.toFinset = insert x (insert w (∅ : Finset V3)) :=
          p12_finite_toFinset_eq (by ext a; simp only [Set.mem_union,
            Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton]; tauto)
        have hxw : x ∉ (insert w (∅ : Finset V3)) := by simp [hxz]
        rw [hy, hF', Finset.sum_insert hxw,
          Finset.sum_insert (by simp : w ∉ (∅ : Finset V3))]
        refine ⟨f x, 0, f w, 0, hneg w (by simp), by simp, ?_, ?_⟩
        · rw [← hsum, hF', Finset.sum_insert hxw,
            Finset.sum_insert (by simp : w ∉ (∅ : Finset V3))]
          simp
        · simp [add_assoc]
      · -- x = v, w ≠ z : F = {x, w, z}
        have hF' : hfin.toFinset = insert x (insert w (insert z (∅ : Finset V3))) :=
          p12_finite_toFinset_eq (by ext a; simp only [Set.mem_union,
            Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton]; tauto)
        have hxw' : x ∉ (insert w (insert z (∅ : Finset V3))) := by simp [hxd, hxz, hwz]
        have hwz' : w ∉ (insert z (∅ : Finset V3)) := by simp [hwz]
        rw [hy, hF', Finset.sum_insert hxw', Finset.sum_insert hwz',
          Finset.sum_insert (by simp : z ∉ (∅ : Finset V3))]
        refine ⟨f x, 0, f w, f z, hneg w (by simp), hneg z (by simp), ?_, ?_⟩
        · rw [← hsum, hF', Finset.sum_insert hxw', Finset.sum_insert hwz',
            Finset.sum_insert (by simp : z ∉ (∅ : Finset V3))]
          simp
          linarith
        · simp [add_assoc]
    · rcases eq_or_ne w z with rfl | hwz
      · -- x ≠ v, w = z : F = {x, v, z}
        have hF' : hfin.toFinset = insert x (insert v (insert w (∅ : Finset V3))) :=
          p12_finite_toFinset_eq (by ext a; simp only [Set.mem_union,
            Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton]; tauto)
        have hxv' : x ∉ (insert v (insert w (∅ : Finset V3))) := by
          simp [hxv, hxz, hvz]
        have hvw' : v ∉ (insert w (∅ : Finset V3)) := by simp [hvd]
        rw [hy, hF', Finset.sum_insert hxv', Finset.sum_insert hvw',
          Finset.sum_insert (by simp : w ∉ (∅ : Finset V3))]
        refine ⟨f x, f v, f w, 0, hneg w (by simp), by simp, ?_, ?_⟩
        · rw [← hsum, hF', Finset.sum_insert hxv', Finset.sum_insert hvw',
            Finset.sum_insert (by simp : w ∉ (∅ : Finset V3))]
          simp
          linarith
        · simp [add_assoc]
      · -- all four distinct : F = {x, v, w, z}
        have hF' : hfin.toFinset =
            insert x (insert v (insert w (insert z (∅ : Finset V3)))) :=
          p12_finite_toFinset_eq (by ext a; simp only [Set.mem_union,
            Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton]; tauto)
        have hxv' : x ∉ (insert v (insert w (insert z (∅ : Finset V3)))) := by
          simp [hxd, hxv, hxz, hvz]
        have hvw' : v ∉ (insert w (insert z (∅ : Finset V3))) := by simp [hvd, hvz]
        have hwz' : w ∉ (insert z (∅ : Finset V3)) := by simp [hwz]
        rw [hy, hF', Finset.sum_insert hxv', Finset.sum_insert hvw',
          Finset.sum_insert hwz', Finset.sum_insert (by simp : z ∉ (∅ : Finset V3))]
        refine ⟨f x, f v, f w, f z, hneg w (by simp), hneg z (by simp), ?_, ?_⟩
        · rw [← hsum, hF', Finset.sum_insert hxv', Finset.sum_insert hvw',
            Finset.sum_insert hwz', Finset.sum_insert (by simp : z ∉ (∅ : Finset V3))]
          simp
          linarith
        · simp [add_assoc]
  · rintro ⟨t1, t2, t3, t4, ht3, ht4, htsum, hty⟩
    rcases eq_or_ne x v with rfl | hxv
    · rcases eq_or_ne w z with rfl | hwz
      · -- x = v, w = z : F = {x, w}
        have hF' : hfinUV.toFinset = insert x (insert w (∅ : Finset V3)) :=
          p12_finite_toFinset_eq (by ext a; simp only [Set.mem_union,
            Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton]; tauto)
        have hxw : x ∉ (insert w (∅ : Finset V3)) := by simp [hxz]
        refine ⟨fun p => if p = x then t1 + t2 else if p = w then t3 + t4 else 0,
          hfinUV, ?_, ?_, ?_⟩
        · rw [hty, hF', Finset.sum_insert hxw,
            Finset.sum_insert (by simp : w ∉ (∅ : Finset V3))]
          simp [add_assoc, add_smul, hxd.symm]
        · intro p hp
          have hpw : p = w := by simpa using hp
          rw [hpw]
          simp [hxd.symm]
          exact add_nonneg ht3 ht4
        · rw [hF', Finset.sum_insert hxw,
            Finset.sum_insert (by simp : w ∉ (∅ : Finset V3))]
          simp [hxd.symm]
          linarith
      · -- x = v, w ≠ z : F = {x, w, z}
        have hF' : hfinUV.toFinset = insert x (insert w (insert z (∅ : Finset V3))) :=
          p12_finite_toFinset_eq (by ext a; simp only [Set.mem_union,
            Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton]; tauto)
        have hxw' : x ∉ (insert w (insert z (∅ : Finset V3))) := by simp [hxd, hxz, hwz]
        have hwz' : w ∉ (insert z (∅ : Finset V3)) := by simp [hwz]
        refine ⟨fun p => if p = x then t1 + t2 else if p = w then t3 else
          if p = z then t4 else 0, hfinUV, ?_, ?_, ?_⟩
        · rw [hty, hF', Finset.sum_insert hxw', Finset.sum_insert hwz',
            Finset.sum_insert (by simp : z ∉ (∅ : Finset V3))]
          simp [add_assoc, add_smul, hxd.symm, hxz.symm, hwz.symm, hvd.symm,
            hvz.symm]
        · intro p hp
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe] at hp
          rcases hp with rfl | rfl <;>
            simp [hxd.symm, hwz.symm, hxz.symm, hvz.symm, hvd.symm, ht3, ht4,
              add_nonneg]
        · rw [hF', Finset.sum_insert hxw', Finset.sum_insert hwz',
            Finset.sum_insert (by simp : z ∉ (∅ : Finset V3))]
          simp [hxd.symm, hxz.symm, hwz.symm, hvd.symm, hvz.symm]
          linarith
    · rcases eq_or_ne w z with rfl | hwz
      · -- x ≠ v, w = z : F = {x, v, w}
        have hF' : hfinUV.toFinset = insert x (insert v (insert w (∅ : Finset V3))) :=
          p12_finite_toFinset_eq (by ext a; simp only [Set.mem_union,
            Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton]; tauto)
        have hxv' : x ∉ (insert v (insert w (∅ : Finset V3))) := by
          simp [hxv, hxz, hvz]
        have hvw' : v ∉ (insert w (∅ : Finset V3)) := by simp [hvd]
        refine ⟨fun p => if p = x then t1 else if p = v then t2 else
          if p = w then t3 + t4 else 0, hfinUV, ?_, ?_, ?_⟩
        · rw [hty, hF', Finset.sum_insert hxv', Finset.sum_insert hvw',
            Finset.sum_insert (by simp : w ∉ (∅ : Finset V3))]
          simp [add_assoc, add_smul, hxd.symm, hxv.symm, hxz.symm, hvd.symm,
            hvz.symm]
        · intro p hp
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe] at hp
          rcases hp with rfl | rfl <;>
            simp [hxd.symm, hxv.symm, hxz.symm, hvz.symm, hvd.symm, ht3, ht4,
              add_nonneg]
        · rw [hF', Finset.sum_insert hxv', Finset.sum_insert hvw',
            Finset.sum_insert (by simp : w ∉ (∅ : Finset V3))]
          simp [hxd.symm, hxv.symm, hxz.symm, hvz.symm, hvd.symm]
          linarith
      · -- all four distinct : F = {x, v, w, z}
        have hF' : hfinUV.toFinset =
            insert x (insert v (insert w (insert z (∅ : Finset V3)))) :=
          p12_finite_toFinset_eq (by ext a; simp only [Set.mem_union,
            Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe,
            Finset.mem_insert, Finset.mem_singleton]; tauto)
        have hxv' : x ∉ (insert v (insert w (insert z (∅ : Finset V3)))) := by
          simp [hxd, hxv, hxz, hvz]
        have hvw' : v ∉ (insert w (insert z (∅ : Finset V3))) := by simp [hvd, hvz]
        have hwz' : w ∉ (insert z (∅ : Finset V3)) := by simp [hwz]
        refine ⟨fun p => if p = x then t1 else if p = v then t2 else
          if p = w then t3 else if p = z then t4 else 0, hfinUV, ?_, ?_, ?_⟩
        · rw [hty, hF', Finset.sum_insert hxv', Finset.sum_insert hvw',
            Finset.sum_insert hwz', Finset.sum_insert (by simp : z ∉ (∅ : Finset V3))]
          simp [add_assoc, add_smul, hxd.symm, hxv.symm, hxz.symm, hvz.symm,
            hwz.symm, hvd.symm]
        · intro p hp
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe] at hp
          rcases hp with rfl | rfl <;>
            simp [hxd.symm, hxv.symm, hwz.symm, hxz.symm, hvz.symm, hvd.symm,
              ht3, ht4]
        · rw [hF', Finset.sum_insert hxv', Finset.sum_insert hvw',
            Finset.sum_insert hwz', Finset.sum_insert (by simp : z ∉ (∅ : Finset V3))]
          simp [hxd.symm, hxv.symm, hxz.symm, hvz.symm, hwz.symm, hvd.symm]
          linarith

/-! ## marchal2.hl:68 MEASURABLE_ROGERS -/

/-- A `barV` list's Rogers simplex is a hull of finitely many points. -/
private theorem p12_rogers_finite (V : Set V3) (ul : List V3) (hb : barV V 3 ul) :
    (omegaListN V ul '' {j : ℕ | j < ul.length}).Finite := by
  have h4 : ul.length = 4 := hb.1
  have hset : {j : ℕ | j < ul.length} = {0, 1, 2, 3} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  refine Set.Finite.image _ ?_
  rw [hset]
  exact by simp

/-- HOL `MEASURABLE_ROGERS` (marchal2.hl:68): `measurable (rogers V ul)`,
rendered as `MeasurableSet`. -/
theorem MEASURABLE_ROGERS (V : Set V3) (ul : List V3)
    (_hs : saturated V) (_hp : Packing V) (hb : barV V 3 ul) :
    MeasurableSet (rogers V ul) := by
  have hc : IsClosed (convexHull ℝ (omegaListN V ul '' {j : ℕ | j < ul.length})) :=
    (Set.Finite.isCompact_convexHull ℝ (p12_rogers_finite V ul hb)).isClosed
  rw [rogers]
  exact IsClosed.measurableSet hc

/-! ## marchal2.hl:90 CONVEX_RCONE_GE -/

/-- HOL `CONVEX_RCONE_GE` (marchal2.hl:90; stated for `real^N` in HOL,
restricted to `V3` per the Kepler `rconeGe` API). -/
theorem CONVEX_RCONE_GE (a : V3) (b : V3) (r : ℝ) (hr : 0 ≤ r) :
    Convex ℝ (rconeGe a b r) := by
  intro x hx y hy u v hu hv huv
  simp only [rconeGe, Set.mem_setOf_eq] at hx hy ⊢
  have hdba : 0 ≤ dist b a := dist_nonneg
  have hsub : u • x + v • y - a = u • (x - a) + v • (y - a) := by
    rw [smul_sub, smul_sub]
    have h1 : a = u • a + v • a := by rw [← add_smul, huv, one_smul]
    conv_lhs => rw [h1]
    abel
  have hdist : dist (u • x + v • y) a ≤ u * dist x a + v * dist y a := by
    have key : dist (u • x + v • y) a = ‖u • (x - a) + v • (y - a)‖ := by
      rw [dist_eq_norm, hsub]
    rw [key]
    calc ‖u • (x - a) + v • (y - a)‖
        ≤ ‖u • (x - a)‖ + ‖v • (y - a)‖ := norm_add_le _ _
      _ = u * dist x a + v * dist y a := by
          simp [norm_smul, Real.norm_eq_abs, dist_eq_norm, abs_of_nonneg hu,
            abs_of_nonneg hv]
  show dist (u • x + v • y) a * dist b a * r ≤ (u • x + v • y - a) ⬝ᵥ (b - a)
  have hxN : x ⬝ᵥ b - a ⬝ᵥ b - (x ⬝ᵥ a - a ⬝ᵥ a) ≥ dist x a * dist b a * r := by
    simpa [inner_sub_left] using hx
  have hyN : y ⬝ᵥ b - a ⬝ᵥ b - (y ⬝ᵥ a - a ⬝ᵥ a) ≥ dist y a * dist b a * r := by
    simpa [inner_sub_left] using hy
  calc (u • x + v • y - a) ⬝ᵥ (b - a)
      = u * (x ⬝ᵥ b - a ⬝ᵥ b - (x ⬝ᵥ a - a ⬝ᵥ a))
        + v * (y ⬝ᵥ b - a ⬝ᵥ b - (y ⬝ᵥ a - a ⬝ᵥ a)) := by simp [hsub]; ring
    _ ≥ u * (dist x a * dist b a * r) + v * (dist y a * dist b a * r) := by
          have e1 : u * (x ⬝ᵥ b - a ⬝ᵥ b - (x ⬝ᵥ a - a ⬝ᵥ a))
              ≥ u * (dist x a * dist b a * r) :=
                mul_le_mul_of_nonneg_left hxN hu
          have e2 : v * (y ⬝ᵥ b - a ⬝ᵥ b - (y ⬝ᵥ a - a ⬝ᵥ a))
              ≥ v * (dist y a * dist b a * r) :=
                mul_le_mul_of_nonneg_left hyN hv
          linarith
    _ = (u * dist x a + v * dist y a) * (dist b a * r) := by ring
    _ ≥ dist (u • x + v • y) a * (dist b a * r) := by
          have h := mul_le_mul_of_nonneg_left hdist (mul_nonneg hdba hr)
          linarith [h, mul_comm (dist b a * r) (u * dist x a + v * dist y a),
            mul_comm (dist b a * r) (dist (u • x + v • y) a)]
    _ = dist (u • x + v • y) a * dist b a * r := by ring

/-! ## marchal2.hl:163 / :166 FINITE_PERMUTE_3 / FINITE_PERMUTE_4 -/

/-- HOL `FINITE_PERMUTE_3` (marchal2.hl:163): finiteness of the symmetric
group on `{0,1,2}`. FIDELITY-FIX 2026-09-19: HOL `permutes` (Library/perms.ml)
is complement-fixing, so the faithful set-builder is the tail-fixed
permutations `∀ j ≥ 3, p j = j` (the old pointwise-`permutes` set-builder
was infinite, hence false as encoded). -/
theorem FINITE_PERMUTE_3 :
    Set.Finite {p : Equiv.Perm ℕ | ∀ j : ℕ, 3 ≤ j → p j = j} := by
  classical
  set S0 : Set ℕ := ({0, 1, 2} : Set ℕ) with hS0
  have hin : ∀ p : Equiv.Perm ℕ, (∀ j : ℕ, 3 ≤ j → p j = j) →
      ∀ i : ℕ, i ≤ 2 → p i ∈ S0 := by
    intro p hp i hi
    by_contra hcon
    simp only [hS0, Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
    have h3 : 3 ≤ p i := by omega
    have hfix : p i = p (p i) := (hp (p i) h3).symm
    have hij : i = p i := Equiv.injective p hfix
    omega
  have hf2 : S0.Finite := by simp [hS0]
  have hfp : ((S0 ×ˢ S0) ×ˢ S0).Finite := (hf2.prod hf2).prod hf2
  haveI := hfp.to_subtype
  have hmem : ∀ p : Equiv.Perm ℕ, (∀ j : ℕ, 3 ≤ j → p j = j) →
      ((⟨⟨p 0, p 1⟩, p 2⟩ : (ℕ × ℕ) × ℕ) ∈ ((S0 ×ˢ S0) ×ˢ S0)) :=
    fun p hp => Set.mem_prod.mpr (And.intro
      (Set.mem_prod.mpr (And.intro (hin p hp 0 (by omega)) (hin p hp 1 (by omega))))
      (hin p hp 2 (by omega)))
  refine Finite.of_injective
    (f := fun p : {p : Equiv.Perm ℕ | ∀ j : ℕ, 3 ≤ j → p j = j} =>
      (⟨⟨⟨p.1 0, p.1 1⟩, p.1 2⟩, hmem p.1 p.2⟩ :
        ↥((S0 ×ˢ S0) ×ˢ S0))) ?_
  rintro ⟨p, hp⟩ ⟨q, hq⟩ heq
  have hval : (⟨⟨p.1 0, p.1 1⟩, p.1 2⟩ : (ℕ × ℕ) × ℕ)
      = (⟨⟨q.1 0, q.1 1⟩, q.1 2⟩ : (ℕ × ℕ) × ℕ) :=
    congrArg Subtype.val heq
  have h0 : p.1 0 = q.1 0 := congrArg (fun t : (ℕ × ℕ) × ℕ => t.1.1) hval
  have h1e : p.1 1 = q.1 1 := congrArg (fun t : (ℕ × ℕ) × ℕ => t.1.2) hval
  have h2e : p.1 2 = q.1 2 := congrArg (fun t : (ℕ × ℕ) × ℕ => t.2) hval
  have hext : p = q := Equiv.ext (fun j => by
    rcases Nat.lt_or_ge j 3 with hlt | hge
    · interval_cases j
      · exact h0
      · exact h1e
      · exact h2e
    · exact (hp j hge).trans (hq j hge).symm)
  exact Subtype.ext hext

/-- HOL `FINITE_PERMUTE_4` (marchal2.hl:166): finiteness of the symmetric
group on `{0,1,2,3}`. Same FIDELITY-FIX as `FINITE_PERMUTE_3`. -/
theorem FINITE_PERMUTE_4 :
    Set.Finite {p : Equiv.Perm ℕ | ∀ j : ℕ, 4 ≤ j → p j = j} := by
  classical
  set S0 : Set ℕ := ({0, 1, 2, 3} : Set ℕ) with hS0
  have hin : ∀ p : Equiv.Perm ℕ, (∀ j : ℕ, 4 ≤ j → p j = j) →
      ∀ i : ℕ, i ≤ 3 → p i ∈ S0 := by
    intro p hp i hi
    by_contra hcon
    simp only [hS0, Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
    have h4 : 4 ≤ p i := by omega
    have hfix : p i = p (p i) := (hp (p i) h4).symm
    have hij : i = p i := Equiv.injective p hfix
    omega
  have hf2 : S0.Finite := by simp [hS0]
  have hfp : (((S0 ×ˢ S0) ×ˢ S0) ×ˢ S0).Finite :=
    ((hf2.prod hf2).prod hf2).prod hf2
  haveI := hfp.to_subtype
  have hmem : ∀ p : Equiv.Perm ℕ, (∀ j : ℕ, 4 ≤ j → p j = j) →
      ((⟨⟨⟨p 0, p 1⟩, p 2⟩, p 3⟩ : ((ℕ × ℕ) × ℕ) × ℕ) ∈
        (((S0 ×ˢ S0) ×ˢ S0) ×ˢ S0)) :=
    fun p hp => Set.mem_prod.mpr (And.intro
      (Set.mem_prod.mpr (And.intro (Set.mem_prod.mpr
        (And.intro (hin p hp 0 (by omega)) (hin p hp 1 (by omega))))
        (hin p hp 2 (by omega))))
      (hin p hp 3 (by omega)))
  refine Finite.of_injective
    (f := fun p : {p : Equiv.Perm ℕ | ∀ j : ℕ, 4 ≤ j → p j = j} =>
      (⟨⟨⟨⟨p.1 0, p.1 1⟩, p.1 2⟩, p.1 3⟩, hmem p.1 p.2⟩ :
        ↥(((S0 ×ˢ S0) ×ˢ S0) ×ˢ S0))) ?_
  rintro ⟨p, hp⟩ ⟨q, hq⟩ heq
  have hval : (⟨⟨⟨p.1 0, p.1 1⟩, p.1 2⟩, p.1 3⟩ :
      ((ℕ × ℕ) × ℕ) × ℕ)
      = (⟨⟨⟨q.1 0, q.1 1⟩, q.1 2⟩, q.1 3⟩ :
      ((ℕ × ℕ) × ℕ) × ℕ) :=
    congrArg Subtype.val heq
  have h0 : p.1 0 = q.1 0 := congrArg
    (fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.1.1) hval
  have h1e : p.1 1 = q.1 1 := congrArg
    (fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.1.2) hval
  have h2e : p.1 2 = q.1 2 := congrArg
    (fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.1.2) hval
  have h3e : p.1 3 = q.1 3 := congrArg
    (fun t : ((ℕ × ℕ) × ℕ) × ℕ => t.2) hval
  have hext : p = q := Equiv.ext (fun j => by
    rcases Nat.lt_or_ge j 4 with hlt | hge
    · interval_cases j
      · exact h0
      · exact h1e
      · exact h2e
      · exact h3e
    · exact (hp j hge).trans (hq j hge).symm)
  exact Subtype.ext hext

/-! ## marchal2.hl:194 DIHV_SYM -/

/-- HOL `DIHV_SYM` (marchal2.hl:194): `dihV x y z t = dihV y x z t`.
Direct projection algebra (no collinearity hypotheses needed): with `c = y - x`,
swapping the edge endpoints replaces `(va, vc) := (z - x, y - x)` by
`(va - c, -c)`, and the `vap` vector is unchanged since
`((-c)⬝ᵥ(-c)) • (va - c) - ((va - c)⬝ᵥ(-c)) • (-c) = (c⬝ᵥc) • va - (va⬝ᵥc) • c`;
the same holds for `vbp`. Proved componentwise on `Fin 3` (the `WithLp`
wrapper blocks direct rewrites on the dot-product arguments). -/
theorem DIHV_SYM (x y z t : V3) : dihV x y z t = dihV y x z t := by
  simp only [dihV]
  congr 1
  · ext i
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, dotProduct,
      Fin.sum_univ_three]
    ring
  · ext i
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, dotProduct,
      Fin.sum_univ_three]
    ring

/-! ## marchal2.hl:255 RCONE_GT_SUBSET_RCONE_GE -/

/-- HOL `RCONE_GT_SUBSET_RCONE_GE` (marchal2.hl:255). -/
theorem RCONE_GT_SUBSET_RCONE_GE (z w : V3) (h : ℝ) :
    rconeGt z w h ⊆ rconeGe z w h := by
  intro x hx
  simp only [rconeGt, Set.mem_setOf_eq] at hx
  simp only [rconeGe, Set.mem_setOf_eq]
  exact le_of_lt hx

/-! ## marchal2.hl:262 MCELL_EXPLICIT -/

/-- HOL `MCELL_EXPLICIT` (marchal2.hl:262): the `mcell` dispatch on `i`. -/
theorem MCELL_EXPLICIT (k : ℕ) (V : Set V3) (ul : List V3) :
    mcell 0 V ul = mcell0 V ul ∧
    mcell 1 V ul = mcell1 V ul ∧
    mcell 2 V ul = mcell2 V ul ∧
    mcell 3 V ul = mcell3 V ul ∧
    (4 ≤ k → mcell k V ul = mcell4 V ul) := by
  refine ⟨rfl, rfl, rfl, rfl, fun hk => ?_⟩
  rw [mcell, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-! ## marchal2.hl:291 EVENTUALLY_RADIAL_EMPTY -/

/-- HOL `EVENTUALLY_RADIAL_EMPTY` (marchal2.hl:291), for the reconstructed
`eventuallyRadial_p12`. -/
theorem EVENTUALLY_RADIAL_EMPTY (v : V3) : eventuallyRadial_p12 v ∅ :=
  ⟨0, by norm_num, fun ε hε => ⟨v, by simp, by simpa using hε.le, by simp⟩⟩

/-! ## marchal2.hl:306 EVENTUALLY_RADIAL_NOT_IN_CLOSED_SET -/

/-- HOL `EVENTUALLY_RADIAL_NOT_IN_CLOSED_SET` (marchal2.hl:306): points off a
closed set see it escaped at every radius. -/
theorem EVENTUALLY_RADIAL_NOT_IN_CLOSED_SET (v : V3) (S : Set V3) (hS : v ∉ S)
    (hc : IsClosed S) : eventuallyRadial_p12 v S := by
  obtain ⟨e, he, hsub⟩ := Metric.isOpen_iff.1 (hc.isOpen_compl) v
    (by simpa using hS : (v : V3) ∈ (Sᶜ : Set V3))
  refine ⟨0, by norm_num, ?_⟩
  intro ε hε
  have hpos : 0 ≤ min e ε / 2 := by positivity
  have hdist : dist (v + (min e ε / 2) • (EuclideanSpace.single (0 : Fin 3) (1:ℝ))) v
      = min e ε / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hpos]
    have h1 : ‖(EuclideanSpace.single (0 : Fin 3) (1:ℝ) : V3)‖ = 1 := by simp
    rw [h1]
    simp
  refine ⟨v + (min e ε / 2) • (EuclideanSpace.single (0 : Fin 3) (1:ℝ)), by simp, ?_, ?_⟩
  · rw [hdist]
    linarith [min_le_right e ε]
  · intro hu
    have hlt : dist (v + (min e ε / 2) • (EuclideanSpace.single (0 : Fin 3) (1:ℝ))) v < e := by
      rw [hdist]
      linarith [min_le_left e ε]
    exact hsub (by simpa using hlt) hu

/-! ## marchal2.hl:349 CLOSED_CONVEX_HULL_FINITE -/

/-- HOL `CLOSED_CONVEX_HULL_FINITE` (marchal2.hl:349). -/
theorem CLOSED_CONVEX_HULL_FINITE (s : Set V3) (hs : s.Finite) :
    IsClosed (convexHull ℝ s) :=
  (Set.Finite.isCompact_convexHull ℝ hs).isClosed

/-! ## marchal2.hl:355 CLOSED_ROGERS -/

/-- HOL `CLOSED_ROGERS` (marchal2.hl:355). -/
theorem CLOSED_ROGERS (V : Set V3) (ul : List V3)
    (_hs : saturated V) (_hp : Packing V) (hb : barV V 3 ul) :
    IsClosed (rogers V ul) := by
  have hc : IsClosed (convexHull ℝ (omegaListN V ul '' {j : ℕ | j < ul.length})) :=
    (Set.Finite.isCompact_convexHull ℝ (p12_rogers_finite V ul hb)).isClosed
  rw [rogers]
  exact hc

/-! ## marchal2.hl:376 CLOSED_SET_OF_LIST_KY_LEMMA_1 -/

/-- The point-set of a list is finite. -/
private theorem p12_setOfList_finite (l : List V3) : (setOfList l).Finite := by
  have h : setOfList l = (l.toFinset : Set V3) := by
    ext a
    simp [setOfList]
  rw [h]
  exact l.toFinset.finite_toSet

/-- HOL `CLOSED_SET_OF_LIST_KY_LEMMA_1` (marchal2.hl:376). -/
theorem CLOSED_SET_OF_LIST_KY_LEMMA_1 (V : Set V3) (ul : List V3)
    (_hs : saturated V) (_hp : Packing V) (_hb : barV V 3 ul) :
    IsClosed (convexHull ℝ (setOfList (truncateSimplex 2 ul) ∪ {mxi V ul})) := by
  have hfin : (setOfList (truncateSimplex 2 ul) ∪ {mxi V ul}).Finite :=
    Set.Finite.union (p12_setOfList_finite _) (Set.finite_singleton (mxi V ul))
  exact (Set.Finite.isCompact_convexHull ℝ hfin).isClosed

/-- HOL `CLOSED_SET_OF_LIST_KY_LEMMA_2` (marchal2.hl:396). -/
theorem CLOSED_SET_OF_LIST_KY_LEMMA_2 (V : Set V3) (ul : List V3)
    (_hs : saturated V) (_hp : Packing V) (_hb : barV V 3 ul) :
    IsClosed (convexHull ℝ (setOfList ul)) :=
  (Set.Finite.isCompact_convexHull ℝ (p12_setOfList_finite ul)).isClosed

/-! ## marchal2.hl:413 CLOSED_RCONE_GE -/

/-- HOL `CLOSED_RCONE_GE` (marchal2.hl:413). -/
theorem CLOSED_RCONE_GE (v0 v1 : V3) (a : ℝ) (_ha : 0 < a) : IsClosed (rconeGe v0 v1 a) := by
  have hset : rconeGe v0 v1 a
      = {x : V3 | dist x v0 * dist v1 v0 * a ≤ (x - v0) ⬝ᵥ (v1 - v0)} := by
    ext x
    simp only [rconeGe, Set.mem_setOf_eq, ge_iff_le]
  rw [hset]
  have hc1 : Continuous fun x : V3 => dist x v0 * dist v1 v0 * a :=
    Continuous.mul (Continuous.mul (continuous_id.dist continuous_const)
      continuous_const) continuous_const
  have hc2 : Continuous fun x : V3 => (x - v0) ⬝ᵥ (v1 - v0) := by
    fun_prop
  exact isClosed_le hc1 hc2

/-! ## marchal2.hl:481 SEGMENT_INTER_CBALL_LEMMA -/

/-- HOL `SEGMENT_INTER_CBALL_LEMMA` (marchal2.hl:2481): a segment whose
endpoint distances straddle `r` crosses the sphere of radius `r`. -/
theorem SEGMENT_INTER_CBALL_LEMMA (x : V3) (r : ℝ) (a b : V3)
    (h1 : dist x a ≤ r) (h2 : r ≤ dist x b) :
    ∃ c : V3, c ∈ segment ℝ a b ∧ dist x c = r := by
  have hcont : ContinuousOn (fun t : ℝ => dist x (AffineMap.lineMap a b t))
      (uIcc (0:ℝ) 1) :=
    (Continuous.dist continuous_const AffineMap.lineMap_continuous).continuousOn
  have h0 : dist x (AffineMap.lineMap a b (0:ℝ)) = dist x a := by
    simp [AffineMap.lineMap_apply]
  have h1v : dist x (AffineMap.lineMap a b (1:ℝ)) = dist x b := by
    simp [AffineMap.lineMap_apply]
  have key : r ∈ uIcc (dist x (AffineMap.lineMap a b (0:ℝ)))
      (dist x (AffineMap.lineMap a b (1:ℝ))) := by
    rw [h0, h1v]
    exact mem_uIcc_of_le h1 h2
  obtain ⟨t, ht, hval⟩ := intermediate_value_uIcc hcont key
  have hI : t ∈ Icc (0:ℝ) 1 := by
    rwa [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  exact ⟨AffineMap.lineMap a b t, lineMap_mem_segment ℝ a b hI, hval⟩

/-! ## marchal2.hl:487 BARV_IMP_HL_1_POS_LT -/

/-- HOL `BARV_IMP_HL_1_POS_LT` (marchal2.hl:487): `0 < hl (truncate 1 ul)`
for a `barV V 3` list. `truncate 1 ul = [u0; u1]` and
`hl [u0; u1] = dist u0 u1 / 2` (re-derivation of PackingAuto11's PRIVATE
`hlPair` from the public Rogers `HL_EQ_DIST0` + `CIRCUMCENTER_2`);
`u0 ≠ u1` because the nondg conditions force `affDim (voronoiList V [u0])`
to equal both `3` (from the singleton sublist) and `2` (from the pair
sublist) if `u0 = u1`. -/
theorem BARV_IMP_HL_1_POS_LT (V : Set V3) (ul : List V3)
    (_hs : saturated V) (_hp : Packing V) (hb : barV V 3 ul) :
    0 < hl (truncateSimplex 1 ul) := by
  obtain ⟨u0, u1, u2, u3, hul⟩ : ∃ a b c d : V3, ul = [a, b, c, d] :=
    BARV_3_EXPLICIT V ul hb
  subst hul
  have hv1 : voronoiNondg V [u0, u1] := hb.2 [u0, u1] ⟨⟨[u2, u3], rfl⟩, by simp⟩
  have hv0 : voronoiNondg V [u0] := hb.2 [u0] ⟨⟨[u1, u2, u3], rfl⟩, by simp⟩
  have hne : u0 ≠ u1 := by
    intro he
    subst he
    have hset : setOfList [u0, u0] = setOfList [u0] := by simp [setOfList]
    have h1 : affDim (voronoiSet V (setOfList [u0, u0])) + 2 = 4 := hv1.2.2
    have h0 : affDim (voronoiSet V (setOfList [u0])) + 1 = 4 := hv0.2.2
    rw [hset] at h1
    omega
  have hb1 : barV V 1 [u0, u1] := by
    refine ⟨rfl, fun vl hv => hb.2 vl ⟨?_, hv.2⟩⟩
    obtain ⟨yl, hy⟩ := hv.1
    refine ⟨yl ++ [u2, u3], ?_⟩
    show [u0, u1] ++ [u2, u3] = vl ++ (yl ++ [u2, u3])
    rw [hy, List.append_assoc]
  have hhl : hl [u0, u1] = dist u0 u1 / 2 := by
    have hhd : hdV [u0, u1] = u0 := rfl
    have hc : setOfList [u0, u1] = {u0, u1} := by
      ext x
      simp [setOfList]
    rw [HL_EQ_DIST0 V 1 [u0, u1] _hp hb1, hc, CIRCUMCENTER_2, hhd, dist_midpoint_left,
      Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < 2 by norm_num)]
    ring
  rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u3).2.2, hhl]
  exact div_pos (dist_pos.mpr hne) (by norm_num)

/-! ## marchal2.hl:541 CLOSED_MCELL -/

/-- HOL `CLOSED_MCELL` (marchal2.hl:541): every Marchal cell is closed.
Cases `k = 0,1,3,4` are proved from CLOSED_ROGERS / cone-openness /
finite-hull closedness; the `k = 2` case needs `IsClosed (affGe …)` (the
affine-combination set of Geom/Aff.lean), not yet available upstream —
sorried for `k = 2` only. -/
theorem CLOSED_MCELL (V : Set V3) (ul : List V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul) :
    ∀ k : ℕ, IsClosed (mcell k V ul) := by
  intro k
  rcases Nat.lt_or_ge k 4 with hk | hk
  · interval_cases k
    · -- k = 0: rogers \ open ball
      show IsClosed (mcell0 V ul)
      rw [mcell0]
      exact (CLOSED_ROGERS V ul hs hp hb).inter Metric.isOpen_ball.isClosed_compl
    · -- k = 1: (rogers ∩ closedBall) \ open cone
      show IsClosed (mcell1 V ul)
      rw [mcell1]
      split_ifs with hle
      · have hc2 : Continuous fun x : V3 =>
            (x - hdV ul) ⬝ᵥ (hdV ul.tail - hdV ul) := by fun_prop
        have hc1 : Continuous fun x : V3 => dist x (hdV ul)
            * dist (hdV ul.tail) (hdV ul)
            * (hl (truncateSimplex 1 ul) / Real.sqrt 2) := by fun_prop
        have hopen : IsOpen (rconeGt (hdV ul) (hdV ul.tail)
            (hl (truncateSimplex 1 ul) / Real.sqrt 2)) := by
          have hF : Continuous fun x : V3 =>
              (x - hdV ul) ⬝ᵥ (hdV ul.tail - hdV ul)
              - dist x (hdV ul) * dist (hdV ul.tail) (hdV ul)
                * (hl (truncateSimplex 1 ul) / Real.sqrt 2) := hc2.sub hc1
          have hset : rconeGt (hdV ul) (hdV ul.tail)
                (hl (truncateSimplex 1 ul) / Real.sqrt 2)
              = (fun x : V3 => (x - hdV ul) ⬝ᵥ (hdV ul.tail - hdV ul)
                  - dist x (hdV ul) * dist (hdV ul.tail) (hdV ul)
                    * (hl (truncateSimplex 1 ul) / Real.sqrt 2)) ⁻¹'
                Set.Ioi 0 := by
            ext x
            simp [rconeGt, Set.mem_preimage, sub_pos]
          rw [hset]
          exact hF.isOpen_preimage _ isOpen_Ioi
        exact ((CLOSED_ROGERS V ul hs hp hb).inter Metric.isClosed_closedBall).inter
          hopen.isClosed_compl
      · exact isClosed_empty
    · -- k = 2: cones ∩ affGe — needs IsClosed (affGe …)
      show IsClosed (mcell2 V ul)
      rw [mcell2]
      split_ifs with hcond
      · sorry
      · exact isClosed_empty
    · -- k = 3: finite hull
      show IsClosed (mcell3 V ul)
      rw [mcell3]
      split_ifs with hcond
      · exact (Set.Finite.isCompact_convexHull ℝ
          (Set.Finite.union (p12_setOfList_finite (truncateSimplex 2 ul))
            (Set.finite_singleton (mxi V ul)))).isClosed
      · exact isClosed_empty
  · -- k ≥ 4: dispatch resolves to mcell4
    rw [mcell, if_neg (by omega : ¬(k = 0)), if_neg (by omega : ¬(k = 1)),
      if_neg (by omega : ¬(k = 2)), if_neg (by omega : ¬(k = 3))]
    rw [mcell4]
    split_ifs with hlt
    · exact (Set.Finite.isCompact_convexHull ℝ (p12_setOfList_finite ul)).isClosed
    · exact isClosed_empty

/-! ## marchal2.hl:609 BARV_IMP_u0_IN_V -/

/-- HOL `BARV_IMP_u0_IN_V` (marchal2.hl:609). -/
theorem BARV_IMP_u0_IN_V (V : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3)
    (_hs : saturated V) (_hp : Packing V) (hb : barV V 3 ul) (hul : ul = [u0, u1, u2, u3]) :
    u0 ∈ V := by
  have hv : voronoiNondg V ul := hb.2 ul
    ⟨⟨[], by rw [List.append_nil]⟩, by rw [hul]; exact Nat.succ_pos 3⟩
  have hsub : setOfList ul ⊆ V := hv.2.1
  have hmem : u0 ∈ setOfList ul := by rw [hul]; simp [setOfList]
  exact hsub hmem

/-! ## marchal2.hl:626 ROGERS_INTER_V_LEMMA -/

/-- HOL `ROGERS_INTER_V_LEMMA` (marchal2.hl:626): `v ∈ V` inside the Rogers
simplex forces `v = HD ul`. Sorried: matches the PRIVATE sorry'd copy
`PackingAuto11.rogersInterVLemma` (needs the omega-points-within-2 geometry). -/
theorem ROGERS_INTER_V_LEMMA (V : Set V3) (ul : List V3) (v : V3)
    (_hs : saturated V) (_hp : Packing V) (_hb : barV V 3 ul)
    (_hv : v ∈ V) (_hr : rogers V ul v) : v = hdV ul := by
  sorry

/-! ## marchal2.hl:669 CONVEX_HULL_4 -/

/-- HOL `CONVEX_HULL_4` (marchal2.hl:669): the four-point hull as the set of
convex weights. -/
theorem CONVEX_HULL_4 (a b c d : V3) :
    convexHull ℝ {a, b, c, d} =
      {z | ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t1 ∧ 0 ≤ t2 ∧ 0 ≤ t3 ∧ 0 ≤ t4 ∧
        t1 + t2 + t3 + t4 = 1 ∧ z = t1 • a + t2 • b + t3 • c + t4 • d} := by
  have hvsub : ({a, b, c, d} : Set V3) ⊆ {z : V3 | ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t1 ∧
      0 ≤ t2 ∧ 0 ≤ t3 ∧ 0 ≤ t4 ∧ t1 + t2 + t3 + t4 = 1 ∧
      z = t1 • a + t2 • b + t3 • c + t4 • d} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw ⊢
    rcases hw with rfl | hw
    · exact ⟨1, 0, 0, 0, zero_le_one, le_rfl, le_rfl, le_rfl, by norm_num, by simp⟩
    rcases hw with rfl | hw
    · exact ⟨0, 1, 0, 0, le_rfl, zero_le_one, le_rfl, le_rfl, by norm_num, by simp⟩
    rcases hw with rfl | hw
    · exact ⟨0, 0, 1, 0, le_rfl, le_rfl, zero_le_one, le_rfl, by norm_num, by simp⟩
    rcases hw with rfl
    exact ⟨0, 0, 0, 1, le_rfl, le_rfl, le_rfl, zero_le_one, by norm_num, by simp⟩
  have hvconv : Convex ℝ {z : V3 | ∃ t1 t2 t3 t4 : ℝ, 0 ≤ t1 ∧ 0 ≤ t2 ∧ 0 ≤ t3 ∧
      0 ≤ t4 ∧ t1 + t2 + t3 + t4 = 1 ∧ z = t1 • a + t2 • b + t3 • c + t4 • d} := by
    intro x hx y hy u v hu hv huv
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    obtain ⟨x1, x2, x3, x4, hx1, hx2, hx3, hx4, hxsum, rfl⟩ := hx
    obtain ⟨y1, y2, y3, y4, hy1, hy2, hy3, hy4, hysum, rfl⟩ := hy
    have e1 : u * (x1 + x2 + x3 + x4) = u := by rw [hxsum, mul_one]
    have e2 : v * (y1 + y2 + y3 + y4) = v := by rw [hysum, mul_one]
    have e3 : (u * x1 + v * y1) + (u * x2 + v * y2) + (u * x3 + v * y3)
        + (u * x4 + v * y4)
        = u * (x1 + x2 + x3 + x4) + v * (y1 + y2 + y3 + y4) := by ring
    refine ⟨u * x1 + v * y1, u * x2 + v * y2, u * x3 + v * y3, u * x4 + v * y4,
      add_nonneg (mul_nonneg hu hx1) (mul_nonneg hv hy1),
      add_nonneg (mul_nonneg hu hx2) (mul_nonneg hv hy2),
      add_nonneg (mul_nonneg hu hx3) (mul_nonneg hv hy3),
      add_nonneg (mul_nonneg hu hx4) (mul_nonneg hv hy4),
      by rw [e3, e1, e2]; exact huv,
      by simp only [add_smul, smul_add, smul_smul]; abel⟩
  have hconv := convex_convexHull (𝕜 := ℝ) (s := ({a, b, c, d} : Set V3))
  have ha_mem : a ∈ convexHull ℝ {a, b, c, d} := subset_convexHull ℝ _ (by simp)
  have hb_mem : b ∈ convexHull ℝ {a, b, c, d} := subset_convexHull ℝ _ (by simp)
  have hc_mem : c ∈ convexHull ℝ {a, b, c, d} := subset_convexHull ℝ _ (by simp)
  have hd_mem : d ∈ convexHull ℝ {a, b, c, d} := subset_convexHull ℝ _ (by simp)
  refine Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · simp only [Set.mem_setOf_eq] at hz ⊢
    exact convexHull_min hvsub hvconv hz
  · simp only [Set.mem_setOf_eq] at hz ⊢
    obtain ⟨t1, t2, t3, t4, ht1, ht2, ht3, ht4, htsum, rfl⟩ := hz
    rcases eq_or_ne (t3 + t4) 0 with h0 | h0
    · have h3 : t3 = 0 := by linarith [h0, ht4]
      have h4 : t4 = 0 := by linarith [h0, ht3]
      rw [h3, h4, add_zero, add_zero] at htsum
      rw [h3, h4, zero_smul, zero_smul, add_zero, add_zero]
      exact hconv ha_mem hb_mem ht1 ht2 htsum
    · have hS : 0 < t3 + t4 := by positivity
      have hn_mem : (t3 / (t3 + t4)) • c + (t4 / (t3 + t4)) • d
          ∈ convexHull ℝ {a, b, c, d} :=
        hconv hc_mem hd_mem (div_nonneg ht3 hS.le) (div_nonneg ht4 hS.le)
          (by field_simp)
      have hm_mem : (t2 / (t2 + t3 + t4)) • b
            + ((t3 + t4) / (t2 + t3 + t4)) •
              ((t3 / (t3 + t4)) • c + (t4 / (t3 + t4)) • d)
          ∈ convexHull ℝ {a, b, c, d} :=
        hconv hb_mem hn_mem (div_nonneg ht2 (by linarith)) (by positivity)
          (by field_simp [show (t2 + t3 + t4 : ℝ) ≠ 0 by linarith]; ring)
      have hz2 : t1 • a + (t2 • b + t3 • c + t4 • d)
          = t1 • a + (t2 + t3 + t4) • ((t2 / (t2 + t3 + t4)) • b
            + ((t3 + t4) / (t2 + t3 + t4)) •
              ((t3 / (t3 + t4)) • c + (t4 / (t3 + t4)) • d)) := by
        congr 1
        simp only [smul_add, smul_smul]
        field_simp [show (t2 + t3 + t4 : ℝ) ≠ 0 by linarith]
        abel
      have hz3 : t1 • a + t2 • b + t3 • c + t4 • d
          = t1 • a + (t2 • b + t3 • c + t4 • d) := by abel
      rw [hz3, hz2]
      exact hconv ha_mem hm_mem ht1 (by positivity) (by linarith)

/-! ## marchal2.hl:681 REAL_LE_DIV_SIMPLIFY_KY_LEMMA -/

/-- HOL `REAL_LE_DIV_SIMPLIFY_KY_LEMMA` (marchal2.hl:681). -/
theorem REAL_LE_DIV_SIMPLIFY_KY_LEMMA (a b c : ℝ) (ha : 0 < a) (hb : b ≤ c / a) :
    a * b ≤ c := by
  have h := (le_div_iff₀ ha).mp hb
  linarith [h, mul_comm a b]

/-! ## marchal2.hl:697 EVENTUALLY_RADIAL_CONVEX_HULL_4_sub1 -/

/-- HOL `EVENTUALLY_RADIAL_CONVEX_HULL_4_sub1` (marchal2.hl:697): `a` off the
face `{b,c,d}` sees the tetrahedron escaped at every radius (separation
functional + outward ray). -/
theorem EVENTUALLY_RADIAL_CONVEX_HULL_4_sub1 (a b c d : V3)
    (ha : a ∉ convexHull ℝ {b, c, d}) :
    eventuallyRadial_p12 a (convexHull ℝ {a, b, c, d}) := by
  have hfin : ({b, c, d} : Set V3).Finite := by
    refine Set.Finite.insert b ?_
    refine Set.Finite.insert c ?_
    exact by simp
  have hc : IsClosed (convexHull ℝ {b, c, d}) :=
    (Set.Finite.isCompact_convexHull ℝ hfin).isClosed
  obtain ⟨f, u, hseple, hfau⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (s := ({b, c, d} : Set V3))) hc ha
  -- hseple : ∀ a ∈ hull{b,c,d}, f a < u;  hfau : f a < u
  have hfb : f b < u := hseple b (subset_convexHull ℝ _ (by simp))
  have hfc : f c < u := hseple c (subset_convexHull ℝ _ (by simp))
  have hfd : f d < u := hseple d (subset_convexHull ℝ _ (by simp))
  have hfab : f (a - b) = f a - f b := by rw [map_sub]
  have hw : 0 < f (a - b) := by rw [hfab]; linarith
  have hsep : ∀ z ∈ convexHull ℝ ({a, b, c, d} : Set V3), f z ≤ f a := by
    intro z hz
    rw [CONVEX_HULL_4 a b c d] at hz
    simp only [Set.mem_setOf_eq] at hz
    obtain ⟨t1, t2, t3, t4, m1, m2, m3, m4, msum, rfl⟩ := hz
    have hv : f (t1 • a + t2 • b + t3 • c + t4 • d)
        = t1 * f a + t2 * f b + t3 * f c + t4 * f d := by simp
    have key : 0 ≤ t2 * (f a - f b) + t3 * (f a - f c) + t4 * (f a - f d) := by
      have e1 := mul_nonneg m2 (by linarith : 0 ≤ f a - f b)
      have e2 := mul_nonneg m3 (by linarith : 0 ≤ f a - f c)
      have e3 := mul_nonneg m4 (by linarith : 0 ≤ f a - f d)
      linarith
    have hrew : t1 * f a + t2 * f b + t3 * f c + t4 * f d
        = f a - (t2 * (f a - f b) + t3 * (f a - f c) + t4 * (f a - f d)) := by
      have ht1' : t1 = 1 - t2 - t3 - t4 := by linarith
      rw [ht1']
      ring
    rw [hv, hrew]
    linarith [key]
  refine ⟨0, by norm_num, ?_⟩
  intro ε hε
  have hab_ne : a ≠ b := by
    intro e
    apply ha
    rw [e]
    exact subset_convexHull ℝ _ (by simp : (b : V3) ∈ ({b, c, d} : Set V3))
  have hnorm : 0 < ‖a - b‖ := by
    by_contra h0
    push_neg at h0
    have h0' : a - b = 0 := norm_eq_zero.1 (le_antisymm h0 (norm_nonneg _))
    exact hab_ne (sub_eq_zero.1 h0')
  have hδpos : 0 < min ε 1 / (2 * ‖a - b‖) := by positivity
  refine ⟨a + (min ε 1 / (2 * ‖a - b‖)) • (a - b), by simp, ?_, ?_⟩
  · have hdd : dist (a + (min ε 1 / (2 * ‖a - b‖)) • (a - b)) a
        = min ε 1 / (2 * ‖a - b‖) * ‖a - b‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hδpos]
    rw [hdd]
    have hsum2 : min ε 1 / (2 * ‖a - b‖) * ‖a - b‖ = min ε 1 / 2 := by
      field_simp [hnorm.ne]
    have hdiv : min ε 1 / 2 ≤ min ε 1 :=
      div_le_self (by positivity) (by norm_num : (1:ℝ) ≤ 2)
    rw [hsum2]
    exact le_trans (le_trans hdiv (min_le_left ε 1)) (by linarith)
  · intro hin
    have hvout : f (a + (min ε 1 / (2 * ‖a - b‖)) • (a - b))
        = f a + min ε 1 / (2 * ‖a - b‖) * f (a - b) := by
      rw [map_add, map_smul]; ring
    have hbound : f (a + (min ε 1 / (2 * ‖a - b‖)) • (a - b)) ≤ f a := hsep _ hin
    rw [hvout] at hbound
    have hpos : 0 < min ε 1 / (2 * ‖a - b‖) * f (a - b) := mul_pos hδpos hw
    linarith [hpos]

/-! ## marchal2.hl:1014 U0_NOT_IN_CONVEX_HULL_FROM_ROGERS -/

/-- HOL `U0_NOT_IN_CONVEX_HULL_FROM_ROGERS` (marchal2.hl:1014). Sorried:
geometric giant (the omega points stay off the first vertex's spot). -/
theorem U0_NOT_IN_CONVEX_HULL_FROM_ROGERS (V : Set V3) (ul : List V3)
    (_hs : saturated V) (_hp : Packing V) (_hb : barV V 3 ul) :
    hdV ul ∉ convexHull ℝ {omegaListN V ul 1, omegaListN V ul 2,
      omegaListN V ul 3} := by
  sorry

/-! ## marchal2.hl:1151 RADIAL_VS_RADIAL_NORM -/

/-- HOL `RADIAL_VS_RADIAL_NORM` (marchal2.hl:1151), for the reconstructed
radial annotations. -/
theorem RADIAL_VS_RADIAL_NORM (r : ℝ) (x : V3) (C : Set V3) :
    radial_p12 r x C ↔ radialNorm_p12 r x C := by
  constructor <;> rintro ⟨hr0, h⟩
  · refine ⟨hr0, fun ε hε => ?_⟩
    obtain ⟨u, hu1, hu2, hu3⟩ := h ε hε
    exact ⟨u, ⟨hu1, hu2⟩, hu3⟩
  · refine ⟨hr0, fun ε hε => ?_⟩
    obtain ⟨u, hu, hu3⟩ := h ε hε
    exact ⟨u, hu.1, hu.2, hu3⟩

/-! ## marchal2.hl:1161 EVENTUALLY_RADIAL_INTER -/

/-- HOL `EVENTUALLY_RADIAL_INTER` (marchal2.hl:1161): the witness for `C`
already witnesses `C ∩ C'`. -/
theorem EVENTUALLY_RADIAL_INTER (x : V3) (C C' : Set V3)
    (h : eventuallyRadial_p12 x C) (_h' : eventuallyRadial_p12 x C') :
    eventuallyRadial_p12 x (C ∩ C') := by
  obtain ⟨r, hr0, hr⟩ := h
  refine ⟨r, hr0, fun ε hε => ?_⟩
  obtain ⟨u, hu1, hu2, hu3⟩ := hr ε hε
  exact ⟨u, hu1, hu2, fun hmem => hu3 hmem.1⟩

/-! ## marchal2.hl:1242 SET_EQ_LEMMA -/

/-- HOL `SET_EQ_LEMMA` (marchal2.hl:1242). -/
theorem SET_EQ_LEMMA (A B : Set V3) :
    A = B ↔ ∀ x, (x ∈ A → x ∈ B) ∧ (x ∈ B → x ∈ A) := by
  constructor
  · intro h x
    subst h
    exact ⟨fun mm => mm, fun mm => mm⟩
  · intro h
    exact Set.ext fun x => ⟨fun m => (h x).1 m, fun m => (h x).2 m⟩

/-! ## marchal2.hl:1245 SET_OF_0_TO_3 -/

/-- HOL `SET_OF_0_TO_3` (marchal2.hl:1245). -/
theorem SET_OF_0_TO_3 : {j : ℕ | j < 4} = {0, 1, 2, 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-! ## marchal2.hl:1260 SET_OF_0_TO_2 -/

/-- HOL `SET_OF_0_TO_2` (marchal2.hl:1260). -/
theorem SET_OF_0_TO_2 : {j : ℕ | j ≤ 2} = {0, 1, 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-! ## marchal2.hl:1273 ZERO_LT_SQRT_2 -/

/-- HOL `ZERO_LT_SQRT_2` (marchal2.hl:1273). -/
theorem ZERO_LT_SQRT_2 : (1 : ℝ) < Real.sqrt 2 := by
  have h1 : (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
  rw [h1]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 2)

/-! ## marchal2.hl:1284 RCONE_GE_TRANS -/

/-- HOL `RCONE_GE_TRANS` (marchal2.hl:1284): membership persists along the
ray `a + t • r`. -/
theorem RCONE_GE_TRANS (a b : V3) (r : ℝ) (x : V3) (t : ℝ) (h0 : 0 ≤ t)
    (hx : a + x ∈ rconeGe a b r) : a + t • x ∈ rconeGe a b r := by
  simp only [rconeGe, Set.mem_setOf_eq] at hx ⊢
  have hdx : dist (a + x) a = ‖x‖ := by rw [dist_eq_norm, add_sub_cancel_left]
  have hdx2 : dist (a + t • x) a = t * ‖x‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg h0]
  have hx' : x ⬝ᵥ (b - a) ≥ ‖x‖ * dist b a * r := by
    have h := hx
    simp only [add_sub_cancel_left] at h
    rw [hdx] at h
    exact h
  have hdot : (a + t • x - a) ⬝ᵥ (b - a) = t * (x ⬝ᵥ (b - a)) := by
    simp
    ring
  have e1 : t * (x ⬝ᵥ (b - a)) ≥ t * (‖x‖ * dist b a * r) :=
    mul_le_mul_of_nonneg_left hx' h0
  have hrs : t * ‖x‖ * dist b a * r = t * (‖x‖ * dist b a * r) := by ring
  rw [hdot, hdx2, hrs]
  exact e1

/-! ## marchal2.hl:1302 RCONE_GE_INTER_VORONOI_CLOSED_PROJECTION_KY_LEMMA -/

/-- HOL `RCONE_GE_INTER_VORONOI_CLOSED_PROJECTION_KY_LEMMA` (marchal2.hl:1302).
Sorried: geometric giant (140-line projection argument). -/
theorem RCONE_GE_INTER_VORONOI_CLOSED_PROJECTION_KY_LEMMA (a b : V3) (r : ℝ)
    (x : V3) (V : Set V3) (hr : 0 < r) (hab : a ≠ b) (ha : a ∈ V) (hb : b ∈ V)
    (hx : x ∈ rconeGe a b r ∩ voronoiClosed V a) :
    ∃ s, s ∈ convexHull ℝ {a, b} ∧ (x - s) ⬝ᵥ (a - b) = 0 := by
  sorry

/-! ## marchal2.hl:1440 RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE -/

/-- HOL `RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE` (marchal2.hl:1440).
Sorried: geometric giant (250-line packing/saturation argument). -/
theorem RCONEGE_INTER_VORONOI_CLOSED_IMP_RCONEGE (V : Set V3) (a b : V3) (r : ℝ)
    (x : V3) (hp : Packing V) (hs : saturated V) (ha : a ∈ V) (hb : b ∈ V)
    (hab : a ≠ b) (hr : 0 < r) (hrle : r ≤ 1)
    (hx1 : x ∈ rconeGe a b r) (hx2 : x ∈ voronoiClosed V a) :
    x ∈ rconeGe b a r := by
  sorry

/-! ## marchal2.hl:1693 OMEGA_LIST_1_EXPLICIT_NEW -/

/-- HOL `OMEGA_LIST_1_EXPLICIT_NEW` (marchal2.hl:1693): the `hl [a;b] < √2`
variant of the omega-explicit lemma (differs from PackingAuto8's
`OMEGA_LIST_1_EXPLICIT`, whose hypothesis bounds `hl ul` of the full list).
Both reduce to the shared Rogers interface `XNHPWAB1_concl` (PackingAuto2)
applied to the pair `[a, b]`. -/
theorem OMEGA_LIST_1_EXPLICIT_NEW (a b c d : V3) (V : Set V3) (ul : List V3)
    (_hs : saturated V) (_hp : Packing V) (hb : barV V 3 ul)
    (hul : ul = [a, b, c, d]) (hh : hl [a, b] < Real.sqrt 2) :
    omegaListN V ul 1 = circumcenter {a, b} := by
  rw [hul] at hb ⊢
  have hb1 : barV V 1 [a, b] := by
    simpa using BARV_INITIAL_SUBLIST V 3 [a, b, c, d] [a, b] hb
      (INITIAL_SUBLIST_APPEND [a, b] [c, d]) (by simp)
  have h1 : omegaListN V [a, b, c, d] 1 = omegaList V [a, b] := by
    show closestPoint (voronoiList V (truncateSimplex 1 [a, b, c, d])) (hdV [a, b, c, d])
        = closestPoint (voronoiList V (truncateSimplex 1 [a, b])) (hdV [a, b])
    rw [(TRUNCATE_SIMPLEX_EXPLICIT_1 a b c d).2.2,
      (TRUNCATE_SIMPLEX_EXPLICIT_1 a b c d).1]
    rfl
  have hcen : omegaList V [a, b] = circumcenter (setOfList [a, b]) :=
    XNHPWAB1_concl V [a, b] 1 _hs _hp (by omega) hb1 hh
  rw [h1, hcen]
  exact congrArg circumcenter (by ext x; simp [setOfList])

/-! ## marchal2.hl:1724 IN_SET_IMP_IN_CONVEX_HULL_SET -/

/-- HOL `IN_SET_IMP_IN_CONVEX_HULL_SET` (marchal2.hl:1724). -/
theorem IN_SET_IMP_IN_CONVEX_HULL_SET (a : V3) (S : Set V3) (ha : a ∈ S) :
    a ∈ convexHull ℝ S := subset_convexHull ℝ S ha

/-! ## marchal2.hl:1737 CONVEX_HULL_BREAK_KY_LEMMA -/

/-- HOL `CONVEX_HULL_BREAK_KY_LEMMA` (marchal2.hl:1737). Sorried: geometric
giant (265-line hull-splitting argument). -/
theorem CONVEX_HULL_BREAK_KY_LEMMA (a b c d x : V3) (hx : x ∈ segment ℝ a b) :
    convexHull ℝ {a, b, c, d} =
      convexHull ℝ {a, x, c, d} ∪ convexHull ℝ {x, b, c, d} := by
  sorry

/-! ## marchal2.hl:2002 CONVEX_HULL_4_SUBSET_AFF_GE_2_2 -/

/-- HOL `CONVEX_HULL_4_SUBSET_AFF_GE_2_2` (marchal2.hl:2002). -/
theorem CONVEX_HULL_4_SUBSET_AFF_GE_2_2 (a b c d : V3) :
    convexHull ℝ {a, b, c, d} ⊆ affGe {a, b} {c, d} := by
  have hfin : (({a, b} : Set V3) ∪ {c, d}).Finite := by simp
  have hverts : ({a, b, c, d} : Set V3) ⊆ affGe {a, b} {c, d} := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    have ha : a ∈ ({a, b} : Set V3) := by simp
    have hb' : b ∈ ({a, b} : Set V3) := by simp
    have hc' : c ∈ ({c, d} : Set V3) := by simp
    have hd' : d ∈ ({c, d} : Set V3) := by simp
    rcases hw with rfl | rfl | rfl | rfl
    · exact p12_mem_affGe_vertex hfin ha
    · exact p12_mem_affGe_vertex hfin hb'
    · exact p12_mem_affGe_vertex_t hfin hc'
    · exact p12_mem_affGe_vertex_t hfin hd'
  exact convexHull_min hverts (p12_convex_affGe hfin)

/-! ## marchal2.hl:2117 AFF_INDEPENDENT_SET_OF_LIST_BARV -/

/-- HOL `AFF_INDEPENDENT_SET_OF_LIST_BARV` (marchal2.hl:2117). Sorried:
needs the affine-dimension bookkeeping of the voronoi_nondg clauses. -/
theorem AFF_INDEPENDENT_SET_OF_LIST_BARV (V : Set V3) (ul : List V3)
    (_hp : Packing V) (_hs : saturated V) (_hb : barV V 3 ul) :
    ¬affineDependent (setOfList ul) := by
  sorry

/-! ## marchal2.hl:2231 VORONOI_LIST_3_SINGLETON_EXPLICIT -/

/-- HOL `VORONOI_LIST_3_SINGLETON_EXPLICIT` (marchal2.hl:2231). Sorried:
geometric giant (circumcenter/voronoi-singleton characterization). -/
theorem VORONOI_LIST_3_SINGLETON_EXPLICIT (V : Set V3) (ul : List V3)
    (_hp : Packing V) (_hs : saturated V) (_hb : barV V 3 ul) :
    ∃ a, voronoiList V ul = {a} ∧ a = circumcenter (setOfList ul) ∧
      hl ul = dist (hdV ul) a := by
  sorry

/-! ## marchal2.hl:2393 SIMPLEX_FURTHEST_LT_2 -/

/-- HOL `SIMPLEX_FURTHEST_LT_2` (marchal2.hl:2393). Sorried: strict convexity
(norm-square Jensen) argument; matches the PRIVATE sorry'd copy
`PackingAuto11.simplexFurthestLt2`. -/
theorem SIMPLEX_FURTHEST_LT_2 (a : V3) (s : Set V3) (hs : s.Finite)
    (hx : x ∈ convexHull ℝ s) (hxs : x ∉ s) :
    ∃ y, y ∈ s ∧ ‖x - a‖ < ‖y - a‖ := by
  sorry

/-! ## marchal2.hl:2424 DIST_BETWEEN_FURTHEST_LT -/

/-- Squared distance to a segment point (variance identity). -/
private theorem p12_norm_sq_convex (u v : V3) (t : ℝ) :
    ‖((1 - t) • u + t • v : V3)‖ ^ 2
      = (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 - t * (1 - t) * ‖u - v‖ ^ 2 := by
  have hnorm : ∀ w : V3, ‖w‖ ^ 2 = @inner ℝ _ _ w w :=
    fun w => (real_inner_self_eq_norm_sq w).symm
  simp only [hnorm, inner_sub_right, inner_sub_left, inner_add_left, inner_add_right,
    real_inner_smul_right, real_inner_comm]
  ring

/-- HOL `DIST_BETWEEN_FURTHEST_LT` (marchal2.hl:2424): an interior point `s`
of the segment `[a, b]` is strictly closer to `x` than `a` whenever `b` is.
Squared-distance variance identity along the segment
(36-line HOL case analysis collapses to one strict inequality). -/
theorem DIST_BETWEEN_FURTHEST_LT (x a b s : V3) (hs : s ∈ segment ℝ a b)
    (hsa : s ≠ a) (hsb : s ≠ b) (hab : a ≠ b)
    (hd : dist x b ≤ dist x a) : dist x s < dist x a := by
  rw [mem_segment_iff_div] at hs
  obtain ⟨α, β, hα, hβ, hsum, hse⟩ := hs
  have h1 : α / (α + β) + β / (α + β) = 1 := by
    rw [← add_div, div_self hsum.ne']
  set t := β / (α + β) with htdef
  have htge : 0 ≤ t := div_nonneg hβ (le_of_lt hsum)
  have ht1 : t ≤ 1 := by
    have hα0 : 0 ≤ α / (α + β) := div_nonneg hα hsum.le
    linarith
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le htge with h | h
    · rw [← h] at h1
      simp at h1
      rw [← hse, ← h, h1] at hsa
      simp at hsa
    · exact h
  have htl1 : t < 1 := by
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [← h] at h1
      have h1' : α / (α + β) = 0 := by linarith
      rw [← hse, h, h1'] at hsb
      simp at hsb
    · exact h
  have hbA : ((x - a : V3) - (x - b)) = (b - a : V3) := by abel
  have hids : (x : V3) - s = (1 - t) • (x - a) + t • (x - b) := by
    rw [← hse, show (α / (α + β) : ℝ) = 1 - t from by linarith]
    module
  have hsq : ‖x - s‖ ^ 2
      = (1 - t) * ‖x - a‖ ^ 2 + t * ‖x - b‖ ^ 2 - t * (1 - t) * ‖b - a‖ ^ 2 := by
    rw [hids]
    have h2 := p12_norm_sq_convex (x - a) (x - b) t
    rw [hbA] at h2
    exact h2
  have hdb : ‖x - b‖ ^ 2 ≤ ‖x - a‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hlt2 : ‖x - s‖ ^ 2 < ‖x - a‖ ^ 2 := by
    have hmul : t * ‖x - b‖ ^ 2 ≤ t * ‖x - a‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hdb htge
    have hpos : 0 < t * (1 - t) * ‖b - a‖ ^ 2 :=
      mul_pos (mul_pos ht0 (by linarith))
        (pow_pos (norm_pos_iff.mpr (fun e => hab (sub_eq_zero.mp e).symm)) 2)
    rw [hsq]
    linarith
  have hlt : ‖x - s‖ < ‖x - a‖ := (abs_lt_of_sq_lt_sq' hlt2 (norm_nonneg _)).2
  rwa [dist_eq_norm, dist_eq_norm]

/-! ## marchal2.hl:2445 ROGERS_EXPLICIT -/

/-- HOL `ROGERS_EXPLICIT` (marchal2.hl:2445): the Rogers simplex is the hull
of the four omega points. -/
theorem ROGERS_EXPLICIT (V : Set V3) (ul : List V3)
    (_hs : saturated V) (_hp : Packing V) (hb : barV V 3 ul) :
    rogers V ul = convexHull ℝ {hdV ul, omegaListN V ul 1, omegaListN V ul 2,
      omegaListN V ul 3} := by
  have h4 : ul.length = 4 := hb.1
  have hset : omegaListN V ul '' {j : ℕ | j < ul.length}
      = {hdV ul, omegaListN V ul 1, omegaListN V ul 2, omegaListN V ul 3} := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [h4] at hj
      interval_cases j
      · simp [hdV, omegaListN]
      · simp
      · simp
      · simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by omega, rfl⟩
      · exact ⟨1, by omega, rfl⟩
      · exact ⟨2, by omega, rfl⟩
      · exact ⟨3, by omega, rfl⟩
  rw [rogers, hset]

/-! ## marchal2.hl:2502 CLOSEST_POINT_SING -/

/-- HOL `CLOSEST_POINT_SING` (marchal2.hl:2502). -/
theorem CLOSEST_POINT_SING (a b : V3) : closestPoint {a} b = a := by
  have hP : (Classical.epsilon fun y : V3 => y ∈ ({a} : Set V3) ∧
      ∀ z ∈ ({a} : Set V3), dist b y ≤ dist b z) = a := by
    have h := Classical.epsilon_spec (p := fun y : V3 => y ∈ ({a} : Set V3) ∧
      ∀ z ∈ ({a} : Set V3), dist b y ≤ dist b z)
      ⟨a, by simp, by intro z hz; simp at hz; subst hz; exact le_refl _⟩
    exact Set.mem_singleton_iff.1 h.1
  rw [closestPoint, hP]

/-! ## marchal2.hl:2516 MXI_EXPLICIT -/

/-- HOL `MXI_EXPLICIT` (marchal2.hl:2516). DISCHARGES the public form of
PackingAuto11's PRIVATE sorry'd `mxiExplicit` via the interface
`MXI_EXISTS_concl` (PackingAuto2). -/
theorem MXI_EXPLICIT (V : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hul : ul = [u0, u1, u2, u3]) (h2 : hl (truncateSimplex 2 ul) < Real.sqrt 2)
    (h3 : Real.sqrt 2 ≤ hl ul) :
    ∃ s : V3, s ∈ segment ℝ (omegaListN V ul 2) (omegaListN V ul 3) ∧
      dist (hdV ul) s = Real.sqrt 2 ∧ s = mxi V ul := by
  have hm := MXI_EXISTS_concl V ul hs hp hb h3
  have h2' : dist (hdV ul) (mxi V ul) = Real.sqrt 2 :=
    (dist_comm _ _).trans hm.2
  refine ⟨mxi V ul, ?_, h2', rfl⟩
  rw [← p12_hull_pair]
  exact hm.1

/-! ## marchal2.hl:2864 CONVEX_HULL_4_IMP_2_2 -/

/-- HOL `CONVEX_HULL_4_IMP_2_2` (marchal2.hl:2864): a point of the
tetrahedron hull lies between a point of edge `ab` and a point of edge `cd`. -/
theorem CONVEX_HULL_4_IMP_2_2 (a b c d p : V3) (hp : p ∈ convexHull ℝ {a, b, c, d}) :
    ∃ m n : V3, p ∈ segment ℝ m n ∧ m ∈ segment ℝ a b ∧ n ∈ segment ℝ c d := by
  rw [CONVEX_HULL_4 a b c d] at hp
  simp only [Set.mem_setOf_eq] at hp
  obtain ⟨t1, t2, t3, t4, ht1, ht2, ht3, ht4, htsum, rfl⟩ := hp
  have hconv := convex_convexHull (𝕜 := ℝ) (s := ({a, b, c, d} : Set V3))
  have ham : a ∈ convexHull ℝ {a, b, c, d} := subset_convexHull ℝ _ (by simp)
  have hbm : b ∈ convexHull ℝ {a, b, c, d} := subset_convexHull ℝ _ (by simp)
  have hcm : c ∈ convexHull ℝ {a, b, c, d} := subset_convexHull ℝ _ (by simp)
  have hdm : d ∈ convexHull ℝ {a, b, c, d} := subset_convexHull ℝ _ (by simp)
  rcases eq_or_ne (t3 + t4) 0 with h0 | h0
  · -- p on edge ab: m := p, n := d
    have h3 : t3 = 0 := by linarith [h0, ht4]
    have h4 : t4 = 0 := by linarith [h0, ht3]
    have htsum' : t1 + t2 = 1 := by rw [h3, h4, add_zero, add_zero] at htsum; exact htsum
    rw [h3, h4, zero_smul, zero_smul, add_zero, add_zero]
    refine ⟨t1 • a + t2 • b, d, ⟨1, 0, by norm_num, by simp, by simp⟩, ?_,
      right_mem_segment ℝ c d⟩
    exact ⟨t1, t2, ht1, ht2, htsum', rfl⟩
  · rcases eq_or_ne (t1 + t2) 0 with h0' | h0'
    · -- p on edge cd: m := a, n := p
        have h1 : t1 = 0 := by linarith [h0', ht2]
        have h2 : t2 = 0 := by linarith [h0', ht1]
        have htsum' : t3 + t4 = 1 := by
          rw [h1, h2, zero_add, zero_add] at htsum
          exact htsum
        rw [h1, h2, zero_smul, zero_smul, zero_add, zero_add]
        refine ⟨a, t3 • c + t4 • d, ⟨0, 1, by norm_num, by simp, by simp⟩,
          left_mem_segment ℝ a b, ?_⟩
        exact ⟨t3, t4, ht3, ht4, htsum', rfl⟩
    · -- general
      have hM : 0 < t1 + t2 := lt_of_le_of_ne (by linarith) (Ne.symm h0')
      have hN : 0 < t3 + t4 := lt_of_le_of_ne (by linarith) (Ne.symm h0)
      refine ⟨(t1 / (t1 + t2)) • a + (t2 / (t1 + t2)) • b,
        (t3 / (t3 + t4)) • c + (t4 / (t3 + t4)) • d, ?_, ?_, ?_⟩
      · refine ⟨t1 + t2, t3 + t4, by linarith, by linarith, by linarith, ?_⟩
        rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
        field_simp [hM.ne', hN.ne']
        abel
      · exact ⟨t1 / (t1 + t2), t2 / (t1 + t2), div_nonneg ht1 hM.le,
          div_nonneg ht2 hM.le, by field_simp [hM.ne'], rfl⟩
      · exact ⟨t3 / (t3 + t4), t4 / (t3 + t4), div_nonneg ht3 hN.le,
          div_nonneg ht4 hN.le, by field_simp [hN.ne'], rfl⟩

/-! ## marchal2.hl:2932 MXI_EXPLICIT_OLD -/

/-- HOL `MXI_EXPLICIT_OLD` (marchal2.hl:2932): the same statement with the
four vertices named (HOL's free variables are implicitly quantified). -/
theorem MXI_EXPLICIT_OLD (V : Set V3) (ul : List V3) (u0 u1 u2 u3 : V3)
    (hs : saturated V) (hp : Packing V) (hb : barV V 3 ul)
    (hul : ul = [u0, u1, u2, u3]) (h2 : hl (truncateSimplex 2 ul) < Real.sqrt 2)
    (h3 : Real.sqrt 2 ≤ hl ul) :
    ∃ s : V3, s ∈ segment ℝ (omegaListN V ul 2) (omegaListN V ul 3) ∧
      dist u0 s = Real.sqrt 2 ∧ s = mxi V ul := by
  obtain ⟨s, hseg, hdist, hs⟩ := MXI_EXPLICIT V ul u0 u1 u2 u3 hs hp hb hul h2 h3
  have hh : hdV ul = u0 := by rw [hul]; rfl
  rw [hh] at hdist
  exact ⟨s, hseg, hdist, hs⟩

/-! ## marchal2.hl:2942 proj_point (the file's one new_definition) -/

/-- HOL `proj_point` (marchal2.hl:2942, the file's only `new_definition`):
the component of `x` along `e` (HOL `projection e x` reconstructed as
`projHL`, see file header). -/
def proj_point (e x : V3) : V3 := x - projHL e x

/-- HOL `PRO_EXP` (marchal2.hl:2949): the explicit form of `proj_point`. -/
theorem PRO_EXP (e x : V3) : proj_point e x = ((x ⬝ᵥ e) / (e ⬝ᵥ e)) • e := by
  rw [proj_point, projHL, projection, sub_sub_cancel]

/-- HOL `projection_proj_point` (marchal2.hl:2945). -/
theorem projection_proj_point (e x : V3) : projHL e x = x - proj_point e x := by
  rw [proj_point, sub_sub_cancel]

/-- Linearity of `proj_point e ·` in the additive argument. -/
private theorem p12_proj_point_add (e u v : V3) :
    proj_point e (u + v) = proj_point e u + proj_point e v := by
  have hd : ((u + v) ⬝ᵥ e) = (u ⬝ᵥ e) + (v ⬝ᵥ e) :=
    add_dotProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ) (e : Fin 3 → ℝ)
  rw [PRO_EXP, PRO_EXP, PRO_EXP, hd, add_div, add_smul]

/-- Linearity of `proj_point e ·` in the scalar argument. -/
private theorem p12_proj_point_smul (e : V3) (c : ℝ) (v : V3) :
    proj_point e (c • v) = c • proj_point e v := by
  have hd : ((c • v) ⬝ᵥ e) = c * (v ⬝ᵥ e) :=
    smul_dotProduct c (v : Fin 3 → ℝ) (e : Fin 3 → ℝ)
  rw [PRO_EXP, PRO_EXP, hd, smul_smul, mul_div_assoc']

/-- Linearity of `projHL e ·` in the scalar argument. -/
private theorem p12_projHL_smul (e : V3) (c : ℝ) (v : V3) :
    projHL e (c • v) = c • projHL e v := by
  rw [projection_proj_point, projection_proj_point, p12_proj_point_smul e,
    smul_sub]

/-- HOL `BETWEEN_PROJ_POINT` (marchal2.hl:2955): `proj_point e ·` is linear,
hence maps segments to segments. -/
theorem BETWEEN_PROJ_POINT (a b x e : V3) (hx : x ∈ segment ℝ a b) :
    proj_point e x ∈ segment ℝ (proj_point e a) (proj_point e b) := by
  rw [← p12_hull_pair] at hx
  have h2 : proj_point e x ∈ convexHull ℝ
      ((fun w : V3 => proj_point e w) '' ({a, b} : Set V3)) := by
    rw [← IsLinearMap.image_convexHull ⟨p12_proj_point_add e, p12_proj_point_smul e⟩]
    exact Set.mem_image_of_mem _ hx
  have himg : ((fun w : V3 => proj_point e w) '' ({a, b} : Set V3))
      = {proj_point e a, proj_point e b} := by
    ext y
    constructor
    · rintro ⟨w, hwmem, hwe⟩
      rw [← hwe]
      rcases hwmem with rfl | rfl
      · simp
      · simp
    · rintro (rfl | rfl)
      · exact ⟨a, by simp⟩
      · exact ⟨b, by simp⟩
  rw [himg, p12_hull_pair] at h2
  exact h2
theorem PARALLEL_PROJECTION (x y a b : V3) (hx : x ∈ segment ℝ a y) (hab : a ≠ b) :
    ∃ k : ℝ, k ≤ 1 ∧ 0 ≤ k ∧
      projHL (b - a) (x - a) = k • projHL (b - a) (y - a) := by
  rw [mem_segment_iff_div] at hx
  obtain ⟨α, β, hα, hβ, hsum, hxe⟩ := hx
  refine ⟨β / (α + β), (div_le_one hsum).2 (by linarith),
    div_nonneg hβ (le_of_lt hsum), ?_⟩
  have h1 : α / (α + β) + β / (α + β) = 1 := by
    rw [← add_div, div_self hsum.ne']
  have h1' : α / (α + β) = 1 - β / (α + β) := by linarith
  have hsub : x - a = (β / (α + β)) • (y - a) := by
    rw [← hxe, h1', sub_smul, one_smul, smul_sub]
    abel
  rw [hsub, p12_projHL_smul]
theorem OMEGA_LIST_TRUNCATE_1_NEW1 (V : Set V3) (u0 u1 u2 : V3) :
    omegaListN V [u0, u1, u2] 1 = omegaList V [u0, u1] := by
  have htr : truncateSimplex 1 [u0, u1, u2] = [u0, u1] :=
    (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u2).2.1
  show closestPoint (voronoiList V (truncateSimplex 1 [u0, u1, u2]))
      (omegaListN V [u0, u1, u2] 0)
    = closestPoint (voronoiList V (truncateSimplex 1 [u0, u1])) (omegaListN V [u0, u1] 0)
  rw [htr, (TRUNCATE_SIMPLEX_EXPLICIT_1 u0 u1 u2 u0).1]
  rfl
theorem TRANSLATE_AFFINE_KY_LEMMA1 (a b c x y z : V3) (k : ℝ)
    (ha : a ∈ affineSpan ℝ ({x, y, z} : Set V3))
    (hb : b ∈ affineSpan ℝ ({x, y, z} : Set V3))
    (hc : c ∈ affineSpan ℝ ({x, y, z} : Set V3)) :
    a + k • (b - c) ∈ affineSpan ℝ ({x, y, z} : Set V3) := by
  have hdir : (k : ℝ) • ((b : V3) - c) ∈ (affineSpan ℝ ({x, y, z} : Set V3)).direction := by
    refine Submodule.smul_mem _ k ?_
    have hv : (b : V3) -ᵥ c ∈ (affineSpan ℝ ({x, y, z} : Set V3)).direction :=
      AffineSubspace.vsub_mem_direction hb hc
    rwa [vsub_eq_sub] at hv
  have h := AffineSubspace.vadd_mem_of_mem_direction hdir ha
  rwa [vadd_eq_add, add_comm] at h
theorem IN_AFFINE_HULL_KY_LEMMA3 (x y z p a : V3) (r : ℝ)
    (h1 : p + a ∈ affineSpan ℝ ({x, y, z} : Set V3))
    (h2 : p + r • a ∈ affineSpan ℝ ({x, y, z} : Set V3))
    (hr : r ≠ 1) : p ∈ affineSpan ℝ ({x, y, z} : Set V3) := by
  have hv : (p : V3) + r • a -ᵥ (p + a) ∈
      (affineSpan ℝ ({x, y, z} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction h2 h1
  have hv' : (r - 1) • a ∈ (affineSpan ℝ ({x, y, z} : Set V3)).direction := by
    rw [sub_smul, one_smul]
    rwa [vsub_eq_sub, add_sub_add_left_eq_sub] at hv
  have hneg : (-a : V3) ∈ (affineSpan ℝ ({x, y, z} : Set V3)).direction := by
    have h := Submodule.smul_mem (affineSpan ℝ ({x, y, z} : Set V3)).direction
      (r - 1)⁻¹ hv'
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero_of_ne hr), one_smul] at h
    exact Submodule.neg_mem _ h
  have hmem := (AffineSubspace.vadd_mem_iff_mem_direction (-a) h1).2 hneg
  have hp : (-a : V3) +ᵥ (p + a) = p := by rw [vadd_eq_add]; abel
  rwa [hp] at hmem
theorem IN_AFFINE_HULL_KY_LEMMA3_alt (x y z p a : V3) (r : ℝ)
    (h1 : p - a ∈ affineSpan ℝ ({x, y, z} : Set V3))
    (h2 : p - r • a ∈ affineSpan ℝ ({x, y, z} : Set V3))
    (hr : r ≠ 1) : p ∈ affineSpan ℝ ({x, y, z} : Set V3) := by
  have hv : (p : V3) - r • a -ᵥ (p - a) ∈
      (affineSpan ℝ ({x, y, z} : Set V3)).direction :=
    AffineSubspace.vsub_mem_direction h2 h1
  have hv' : (1 - r) • a ∈ (affineSpan ℝ ({x, y, z} : Set V3)).direction := by
    rw [sub_smul, one_smul]
    rwa [vsub_eq_sub, sub_sub_sub_cancel_left] at hv
  have hmem : (a : V3) ∈ (affineSpan ℝ ({x, y, z} : Set V3)).direction := by
    have h := Submodule.smul_mem (affineSpan ℝ ({x, y, z} : Set V3)).direction
      (1 - r)⁻¹ hv'
    rw [smul_smul,
      inv_mul_cancel₀ (fun e => hr (sub_eq_zero.mp e).symm), one_smul] at h
    exact h
  have hfin := (AffineSubspace.vadd_mem_iff_mem_direction a h1).2 hmem
  have hp : (a : V3) +ᵥ (p - a) = p := by rw [vadd_eq_add]; abel
  rwa [hp] at hfin
theorem IN_AFFINE_HULL_3_KY_LEMMA2 (X Y Z a b c : V3)
    (hX : X ∈ affineSpan ℝ ({a, b, c} : Set V3))
    (hY : Y ∈ affineSpan ℝ ({a, b, c} : Set V3))
    (hZ : Z ∈ segment ℝ X Y) : Z ∈ affineSpan ℝ ({a, b, c} : Set V3) := by
  have hsub : ({X, Y} : Set V3) ⊆ (affineSpan ℝ ({a, b, c} : Set V3)) := by
    intro w hw
    rcases hw with rfl | rfl
    · exact hX
    · exact hY
  have h1 : Z ∈ affineSpan ℝ ({X, Y} : Set V3) := by
    rw [← p12_hull_pair] at hZ
    exact convexHull_subset_affineSpan ({X, Y} : Set V3) hZ
  have hle : affineSpan ℝ ({X, Y} : Set V3) ≤ affineSpan ℝ ({a, b, c} : Set V3) :=
    affineSpan_le.2 hsub
  exact hle h1