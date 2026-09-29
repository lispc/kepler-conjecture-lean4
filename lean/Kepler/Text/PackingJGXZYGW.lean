/-
Leaf module for the pack1.hl density chain (`JGXZYGW`), Flyspeck
`reference/flyspeck/text_formalization/packing/pack1.hl:325-592`.

The chain was ported as a skeleton in `Kepler/Text/PackingAuto1.lean`
(:785-1032); this module carries a private, `jg_`-prefixed copy of that
chain with the twelve `sorry` items discharged. The public surface is the
single capstone `jgxzygw_p` (HOL `JGXZYGW`, pack1.hl:519, `p` explicit),
stated over `Space3` with every definition inlined, so consumers
(`PackingAuto2.JGXZYGW_KY_p2`, `PackingAuto19.JGXZYGW_p19`) can bridge
their own encodings (`volume.real`, `voronoiOpen`, `setSum`) by
`rfl`-level conversions.

All chain items are `private` and uniquely prefixed `jg_`, so the module
can be imported anywhere without name clashes (the public `saturated` /
`voronoi_open` / `KIUMVTC` of PackingAuto1 are what blocks importing it).
The pack2 closed-cell chain of PackingAuto1 is NOT part of this module.
-/

import Kepler.Statement
import Mathlib

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Set Metric MeasureTheory Filter Topology Classical

noncomputable section

local instance : DecidableEq Space3 := Classical.decEq Space3

/-! ### Private environment: cells, saturation, finiteness -/

/-- HOL `voronoi_open` (pack1.hl:153; the `IN`-form of pack2.hl:25). -/
private def jg_voronoi_open (S : Set Space3) (v : Space3) : Set Space3 :=
  {x | ∀ w, w ∈ S → w ≠ v → dist x v < dist x w}

/-- HOL `saturated` (pack1.hl:159). -/
private def jg_saturated (S : Set Space3) : Prop := ∀ x : Space3, ∃ y ∈ S, dist x y < 2

/-- Distance to the origin is translation-equivariant (center transfer for
Lemma 5.1). -/
private theorem jg_dist_sub_right (x p : Space3) : dist (x - p) 0 = dist x p := by
  rw [dist_zero_right, dist_eq_norm]

/-- HOL Lemma 5.1 `KIUMVTC` (pack1.hl:140), arbitrary center: a packing
inside any ball is finite. -/
private theorem jg_set_finite_inter_ball (S : Set Space3) (hV : Packing S) (p : Space3)
    (r : ℝ) : (S ∩ Metric.ball p r).Finite := by
  classical
  -- Translate the packing to the origin, apply `Packing.finite_inter_ball`,
  -- translate back.
  have hTsub : ((fun x => x - p) '' (S ∩ Metric.ball p r)) ⊆ Metric.ball 0 r := by
    rintro x ⟨y, ⟨-, hy⟩, rfl⟩
    rw [Metric.mem_ball, jg_dist_sub_right]
    exact Metric.mem_ball.mp hy
  have hTpack : Packing ((fun x => x - p) '' (S ∩ Metric.ball p r)) := by
    intro u hu v hv hlt
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have hd : dist (a - p) (b - p) = dist a b := by
      rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]
    rw [hd] at hlt
    rw [hV a ha.1 b hb.1 hlt]
  have hTfin : ((fun x => x - p) '' (S ∩ Metric.ball p r)).Finite := by
    have h1 : ((fun x => x - p) '' (S ∩ Metric.ball p r)) ∩ Metric.ball 0 r =
        (fun x => x - p) '' (S ∩ Metric.ball p r) :=
      Set.inter_eq_self_of_subset_left hTsub
    rw [← h1]
    exact hTpack.finite_inter_ball r
  have him2 : ((fun x => x + p) '' ((fun x => x - p) '' (S ∩ Metric.ball p r))).Finite :=
    Finite.image (fun x : Space3 => x + p) hTfin
  refine Set.Finite.subset him2 ?_
  intro x hx
  exact ⟨x - p, ⟨x, hx, rfl⟩, by abel⟩

/-! ### The density chain on open cells (pack1.hl:329-:592) -/

/-- HOL `negligible_fun_p` (pack1.hl:329): `f` is negligible on `S` at `p`. -/
private def jg_negligible_fun_p (f : Space3 → ℝ) (S : Set Space3) (p : Space3) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ h : (S ∩ Metric.ball p r).Finite,
    (∑ v ∈ Set.Finite.toFinset h, f v) ≤ C * r ^ 2

/-- HOL `fcc_compatible` (pack1.hl:332), open-cell form. -/
private def jg_fcc_compatible (f : Space3 → ℝ) (S : Set Space3) : Prop :=
  ∀ v ∈ S, Real.sqrt 32 ≤ (volume (jg_voronoi_open S v)).toReal + f v

/-- HOL `packing_subset_unions_ball` (pack1.hl:335). -/
private theorem jg_packing_subset_unions_ball (S : Set Space3) (p : Space3) (r : ℝ) :
    ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r) ⊆
      ⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1 := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx.1
  have hxp := hx.2
  refine Set.mem_iUnion₂.mpr ⟨v, ⟨hv, ?_⟩, hxv⟩
  have hlt1 : dist x v < 1 := Metric.mem_ball.mp hxv
  have hlt2 : dist x p < r := Metric.mem_ball.mp hxp
  have h1 : dist v p ≤ dist x p + dist x v := by
    have h2 : dist p v ≤ dist p x + dist x v := dist_triangle p x v
    linarith [dist_comm p v, dist_comm p x]
  rw [Metric.mem_ball]
  linarith

/-- HOL `measurable_packing_lm1` (pack1.hl:339). -/
private theorem jg_measurable_packing_lm1 (S : Set Space3) (p : Space3) (r : ℝ) :
    MeasurableSet ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r) :=
  ((isOpen_iUnion fun v => isOpen_iUnion fun (_ : v ∈ S) => isOpen_ball).inter
    isOpen_ball).measurableSet

/-- Rewrite of a finite-set-indexed union as a `Finset`-indexed union. -/
private theorem jg_biUnion_toFinset_eq {α ι : Type*} [DecidableEq ι] {t : Set ι}
    (ht : t.Finite) (f : ι → Set α) : (⋃ i ∈ t, f i) = ⋃ i ∈ Set.Finite.toFinset ht, f i := by
  ext x
  simp

/-- HOL `measurable_packing_lm2` (pack1.hl:353). -/
private theorem jg_measurable_packing_lm2 (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    MeasurableSet (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1) :=
  Set.Finite.measurableSet_biUnion (jg_set_finite_inter_ball S hV p (r + 1))
    fun _ _ => measurableSet_ball

/-- The volume of a ball in `Space3` is finite. -/
private theorem jg_volume_ball_ne_top (c : Space3) (q : ℝ) : volume (Metric.ball c q) ≠ ⊤ := by
  intro hq
  rw [EuclideanSpace.volume_ball_fin_three] at hq
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top hq

/-- The volume of a unit ball in `Space3`. -/
private theorem jg_volume_ball_one (c : Space3) :
    (volume (Metric.ball c 1)).toReal = 4 * Real.pi / 3 := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- The real volume of a ball of radius `q ≥ 0` in `Space3`. -/
private theorem jg_volume_ball (c : Space3) (q : ℝ) (hq : 0 ≤ q) :
    (volume (Metric.ball c q)).toReal = 4 * Real.pi / 3 * q ^ 3 := by
  rw [EuclideanSpace.volume_ball_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hq,
    ENNReal.toReal_ofReal (div_nonneg (mul_nonneg Real.pi_pos.le (by norm_num)) (by norm_num))]
  ring

/-- HOL `measure_ineq_lm53_1` (pack1.hl:357). -/
private theorem jg_measure_ineq_lm53_1 (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    (volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r)).toReal ≤
      (volume (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1)).toReal := by
  classical
  have hsub := jg_packing_subset_unions_ball S p r
  have hsub2 : (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1) ⊆ Metric.ball p (r + 3) := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    rw [Metric.mem_ball] at hxv ⊢
    have h1 : dist p x ≤ dist p v + dist x v := by
      linarith [dist_triangle p v x, dist_comm v x]
    linarith [Metric.mem_ball.mp hv.2, hxv, dist_comm x p, dist_comm v p]
  have hL : volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r) ≠ ⊤ :=
    fun hc => jg_volume_ball_ne_top p (r + 3)
      (top_le_iff.mp (le_trans (le_of_eq hc.symm) (le_trans (measure_mono hsub)
        (measure_mono hsub2))))
  have hR : volume (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1) ≠ ⊤ :=
    fun hc => jg_volume_ball_ne_top p (r + 3)
      (top_le_iff.mp (le_trans (le_of_eq hc.symm) (measure_mono hsub2)))
  exact (ENNReal.toReal_le_toReal hL hR).mpr (measure_mono hsub)

/-- HOL `card_eq_ball_point` (pack1.hl:371). -/
private theorem jg_card_eq_ball_point (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    ({q : Set Space3 | ∃ x ∈ (S ∩ Metric.ball p (r + 1)), q = Metric.ball x 1}).ncard =
      (S ∩ Metric.ball p (r + 1)).ncard := by
  classical
  have hinj : Set.InjOn (fun x : Space3 => Metric.ball x 1)
      (S ∩ Metric.ball p (r + 1)) := by
    intro x hx y hy hxy
    have hxy' : Metric.ball x 1 = Metric.ball y 1 := hxy
    by_contra hne
    have h1 : x ∈ Metric.ball y 1 := by
      have hx1 : x ∈ Metric.ball x 1 := Metric.mem_ball_self one_pos
      rwa [hxy'] at hx1
    have h2 : y ∈ Metric.ball x 1 := by
      have hy1 : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
      rw [← hxy'] at hy1
      exact hy1
    rw [Metric.mem_ball] at h1 h2
    have h3 : 2 ≤ dist x y := hV.dist_ge_two hx.1 hy.1 hne
    linarith [dist_comm x y]
  have hEq : {q : Set Space3 | ∃ x ∈ (S ∩ Metric.ball p (r + 1)), q = Metric.ball x 1} =
      (fun x : Space3 => Metric.ball x 1) '' (S ∩ Metric.ball p (r + 1)) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_image]
    tauto
  rw [hEq, Set.InjOn.ncard_image hinj]

/-- HOL `measure_ineq_lm53_2` (pack1.hl:363), Step 1: the volume inside
`ball p r` is at most the number of unit balls centered in `ball p (r+1)`
times the unit-ball volume `4π/3`. -/
private theorem jg_measure_ineq_lm53_2 (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    (volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r)).toReal ≤
      (({q : Set Space3 |
        ∃ v ∈ (S ∩ Metric.ball p (r + 1)), q = Metric.ball v 1}).ncard : ℝ) *
        4 * Real.pi / 3 := by
  classical
  have hfin : (S ∩ Metric.ball p (r + 1)).Finite := jg_set_finite_inter_ball S hV p (r + 1)
  have hinj : Set.InjOn (fun v : Space3 => Metric.ball v 1) (S ∩ Metric.ball p (r + 1)) := by
    intro x hx y hy hxy
    have hxy' : Metric.ball x 1 = Metric.ball y 1 := hxy
    by_contra hne
    have h1 : x ∈ Metric.ball y 1 := by
      have hx1 : x ∈ Metric.ball x 1 := Metric.mem_ball_self one_pos
      rwa [hxy'] at hx1
    have h2 : y ∈ Metric.ball x 1 := by
      have hy1 : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
      rw [← hxy'] at hy1
      exact hy1
    rw [Metric.mem_ball] at h1 h2
    have h3 : 2 ≤ dist x y := hV.dist_ge_two hx.1 hy.1 hne
    linarith [dist_comm x y]
  have himg : {q : Set Space3 | ∃ v ∈ (S ∩ Metric.ball p (r + 1)), q = Metric.ball v 1} =
      (fun v : Space3 => Metric.ball v 1) '' (S ∩ Metric.ball p (r + 1)) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_image]
    tauto
  have hcard : ((Set.Finite.toFinset hfin).card : ℝ) =
      ((S ∩ Metric.ball p (r + 1)).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card (S ∩ Metric.ball p (r + 1)) hfin]
  -- the union of the unit balls inside `ball p (r + 2)` has finite volume
  have hsub : (⋃ v ∈ Set.Finite.toFinset hfin, Metric.ball v 1) ⊆ Metric.ball p (r + 2) := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
    rw [Metric.mem_ball] at hxv ⊢
    have h1 : dist p x ≤ dist p v + dist v x := dist_triangle p v x
    have hvb : dist v p < r + 1 :=
      Metric.mem_ball.mp ((Set.Finite.mem_toFinset hfin).mp hv).2
    linarith [h1, hxv, hvb, dist_comm p v, dist_comm v x, dist_comm x p]
  have hU : (volume (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1)).toReal ≤
      ((Set.Finite.toFinset hfin).card : ℝ) * 4 * Real.pi / 3 := by
    rw [jg_biUnion_toFinset_eq hfin (fun v => Metric.ball v 1)]
    have hneU : volume (⋃ v ∈ Set.Finite.toFinset hfin, Metric.ball v 1) ≠ ⊤ :=
      fun hc => jg_volume_ball_ne_top p (r + 2)
        (top_le_iff.mp (le_trans (le_of_eq hc.symm) (measure_mono hsub)))
    have hle1 : (volume (⋃ v ∈ Set.Finite.toFinset hfin, Metric.ball v 1)).toReal ≤
        (∑ v ∈ Set.Finite.toFinset hfin, volume (Metric.ball v 1)).toReal :=
      (ENNReal.toReal_le_toReal hneU
        (ENNReal.sum_ne_top.mpr fun v (_ : v ∈ Set.Finite.toFinset hfin) =>
          jg_volume_ball_ne_top v 1)).mpr
        (measure_biUnion_finset_le (Set.Finite.toFinset hfin) (fun v => Metric.ball v 1))
    have hle2 : (∑ v ∈ Set.Finite.toFinset hfin, volume (Metric.ball v 1)).toReal =
        ((Set.Finite.toFinset hfin).card : ℝ) * 4 * Real.pi / 3 := by
      rw [ENNReal.toReal_sum (fun v (_ : v ∈ Set.Finite.toFinset hfin) =>
        jg_volume_ball_ne_top v 1)]
      have hall : ∀ v ∈ Set.Finite.toFinset hfin, (volume (Metric.ball v 1)).toReal =
          4 * Real.pi / 3 := fun v _ => jg_volume_ball_one v
      calc (∑ v ∈ Set.Finite.toFinset hfin, (volume (Metric.ball v 1)).toReal)
          = ∑ v ∈ Set.Finite.toFinset hfin, (4 * Real.pi / 3) :=
            Finset.sum_congr rfl fun v hv => hall v hv
        _ = ((Set.Finite.toFinset hfin).card : ℝ) * 4 * Real.pi / 3 := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    exact hle1.trans hle2.le
  calc (volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r)).toReal
      ≤ (volume (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), Metric.ball v 1)).toReal :=
        jg_measure_ineq_lm53_1 S p r hr hV
    _ ≤ ((Set.Finite.toFinset hfin).card : ℝ) * 4 * Real.pi / 3 := hU
    _ = ({q : Set Space3 |
          ∃ v ∈ (S ∩ Metric.ball p (r + 1)), q = Metric.ball v 1}.ncard : ℝ) *
          4 * Real.pi / 3 := by
        rw [hcard, himg, Set.InjOn.ncard_image hinj]

/-- HOL `voronoi_in_ball` (pack1.hl:285). -/
private theorem jg_voronoi_in_ball (x v : Space3) (S : Set Space3) (hV : Packing S)
    (hs : jg_saturated S) (hx : x ∈ jg_voronoi_open S v) : dist x v < 2 := by
  obtain ⟨y, hyS, hxy⟩ := hs x
  rcases eq_or_ne y v with rfl | hyv
  · exact hxy
  · linarith [hx y hyS hyv]

/-- HOL `open_voronoi` (pack1.hl:297), proved directly by a uniform-gap
argument over the finitely many centers within distance 4. -/
private theorem jg_open_voronoi (v : Space3) (S : Set Space3) (hV : Packing S)
    (hs : jg_saturated S) : IsOpen (jg_voronoi_open S v) := by
  classical
  rw [Metric.isOpen_iff]
  rintro x₀ hx₀
  have hD : dist x₀ v < 2 := jg_voronoi_in_ball x₀ v S hV hs hx₀
  set F : Set Space3 := (S ∩ Metric.ball v 4) \ {v} with hFdef
  have hFfin : F.Finite := (jg_set_finite_inter_ball S hV v 4).sdiff
  have hpos : ∀ w ∈ F, 0 < dist x₀ w - dist x₀ v := by
    intro w hw
    obtain ⟨⟨hwS, -⟩, hwv⟩ := hw
    have hwne : w ≠ v := by simpa using hwv
    linarith [hx₀ w hwS hwne]
  have hmin : ∃ m : ℝ, 0 < m ∧ ∀ w ∈ F, dist x₀ v + m ≤ dist x₀ w := by
    by_cases hFe : F = ∅
    · refine ⟨1, one_pos, ?_⟩
      intro w hw
      exact absurd hw (by rw [hFe]; simp)
    · have hne : Set.Finite.toFinset hFfin |>.Nonempty := by
        obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr hFe
        exact ⟨w, Set.Finite.mem_toFinset hFfin |>.mpr hw⟩
      have htne : ((Set.Finite.toFinset hFfin).image
          (fun w => dist x₀ w - dist x₀ v)).Nonempty := by
        obtain ⟨w, hw⟩ := hne
        exact ⟨dist x₀ w - dist x₀ v, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
      refine ⟨(Set.Finite.toFinset hFfin).image
        (fun w : Space3 => dist x₀ w - dist x₀ v) |>.min' htne, ?_, ?_⟩
      · rcases Finset.mem_image.mp (Finset.min'_mem _ htne) with ⟨w₀, hw₀, hw₀eq⟩
        rw [← hw₀eq]
        exact hpos w₀ (Set.Finite.mem_toFinset hFfin |>.mp hw₀)
      · intro w hw
        have hwT : w ∈ Set.Finite.toFinset hFfin := (Set.Finite.mem_toFinset hFfin).mpr hw
        have himg : (fun w : Space3 => dist x₀ w - dist x₀ v) w ∈
            (Set.Finite.toFinset hFfin).image (fun w : Space3 => dist x₀ w - dist x₀ v) :=
          Finset.mem_image.mpr ⟨w, hwT, rfl⟩
        have hle := Finset.min'_le _ _ himg
        linarith
  obtain ⟨m, hmpos, hmle⟩ := hmin
  refine ⟨min (m / 3) ((2 - dist x₀ v) / 3), lt_min (by linarith) (by linarith), ?_⟩
  intro y hy
  rw [Metric.mem_ball] at hy
  have hy1 := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 := lt_of_lt_of_le hy (min_le_right _ _)
  intro w hwS hwv
  by_cases hwF : w ∈ F
  · have hwb : dist w v < 4 := by
      have h5 := hwF.1.2
      rw [Metric.mem_ball] at h5
      exact h5
    have h1 : dist x₀ w ≤ dist x₀ y + dist y w := dist_triangle x₀ y w
    have h2 := hmle w hwF
    have h3 : dist y v ≤ dist y x₀ + dist x₀ v := dist_triangle y x₀ v
    linarith [hy1, hy2, h1, h2, h3, dist_comm x₀ y]
  · have hw4 : (4 : ℝ) ≤ dist v w := by
      by_contra hc
      exact hwF ⟨⟨hwS, by rw [Metric.mem_ball]; linarith [lt_of_not_ge hc, dist_comm v w]⟩,
        by simpa using hwv⟩
    have h1 : dist v w ≤ dist v y + dist y w := dist_triangle v y w
    have h2 : dist y v ≤ dist y x₀ + dist x₀ v := dist_triangle y x₀ v
    have h3 : dist v y = dist y v := dist_comm v y
    linarith [hy1, hy2]

/-- HOL `measurable_voronoi` (pack1.hl:322). -/
private theorem jg_measurable_voronoi (v : Space3) (S : Set Space3) (hV : Packing S)
    (hs : jg_saturated S) : MeasurableSet (jg_voronoi_open S v) :=
  (jg_open_voronoi v S hV hs).measurableSet

/-- HOL `voronoi_subset_ball` (pack1.hl:380). -/
private theorem jg_voronoi_subset_ball (v : Space3) (S : Set Space3) (hV : Packing S)
    (hs : jg_saturated S) : jg_voronoi_open S v ⊆ Metric.ball v 2 := by
  intro x hx
  rw [Metric.mem_ball]
  exact jg_voronoi_in_ball x v S hV hs hx

/-- HOL `all_voronoi_subset_ball` (pack1.hl:383). -/
private theorem jg_all_voronoi_subset_ball (v : Space3) (S : Set Space3) (p : Space3) (r : ℝ)
    (hV : Packing S) (hs : jg_saturated S) (hv : v ∈ Metric.ball p (r + 1)) :
    jg_voronoi_open S v ⊆ Metric.ball p (r + 3) := by
  intro x hx
  rw [Metric.mem_ball] at hv ⊢
  have h1 : dist p x ≤ dist p v + dist x v := by
    linarith [dist_triangle p v x, dist_comm v x]
  have h2 : dist x v < 2 := jg_voronoi_in_ball x v S hV hs hx
  linarith [Metric.mem_ball.mp hv, h1, h2, dist_comm x p, dist_comm v p]

/-- HOL `unions_voronoi_center_in_ball_subset_ball` (pack1.hl:385). -/
private theorem jg_unions_voronoi_center_in_ball_subset_ball (S : Set Space3) (p : Space3)
    (r : ℝ) (hV : Packing S) (hs : jg_saturated S) :
    (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), jg_voronoi_open S v) ⊆ Metric.ball p (r + 3) := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
  exact jg_all_voronoi_subset_ball v S p r hV hs hv.2 hxv

/-- HOL `map_to_voronoi` (pack1.hl:388). -/
private def jg_map_to_voronoi (q : Space3 × Set Space3) : Set Space3 :=
  jg_voronoi_open q.2 q.1

/-- HOL `surj_map_to_voronoi_db` (pack1.hl:390). -/
private theorem jg_surj_map_to_voronoi_db (S : Set Space3) (p : Space3) (r : ℝ) :
    jg_map_to_voronoi '' ((S ∩ Metric.ball p (r + 1)) ×ˢ {S}) =
      {q : Set Space3 | ∃ v : Space3, ∃ w : Set Space3,
        v ∈ S ∩ Metric.ball p (r + 1) ∧ w = S ∧ q = jg_voronoi_open w v} := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases a with ⟨v, w⟩
    have hv : v ∈ (S ∩ Metric.ball p (r + 1)) := ha.1
    have hwS : w = S := ha.2
    refine ⟨v, w, hv, hwS, ?_⟩
    rw [hwS]
    rfl
  · rintro ⟨v, w, hv, hwS, hqv⟩
    have hv' : v ∈ (S ∩ Metric.ball p (r + 1)) := hv
    have hwS' : w = S := hwS
    have hqv' : q = jg_voronoi_open w v := hqv
    subst hqv'
    rw [hwS']
    exact ⟨(v, S), ⟨hv', rfl⟩, rfl⟩

/-- HOL `finite_set_voronoi_center_in_ball` (pack1.hl:394). -/
private theorem jg_finite_set_voronoi_center_in_ball (S : Set Space3) (p : Space3) (r : ℝ)
    (hr : 0 ≤ r) (hV : Packing S) :
    {q : Set Space3 | ∃ v : Space3, ∃ w : Set Space3,
      v ∈ S ∩ Metric.ball p (r + 1) ∧ w = S ∧ q = jg_voronoi_open w v}.Finite := by
  rw [← jg_surj_map_to_voronoi_db S p r]
  exact Set.Finite.image _ (Set.Finite.prod (jg_set_finite_inter_ball S hV p (r + 1))
    (Set.finite_singleton S))

/-- HOL `measurable_unions_voronoi` (pack1.hl:398). -/
private theorem jg_measurable_unions_voronoi (S : Set Space3) (p : Space3) (r : ℝ)
    (hr : 0 ≤ r) (hV : Packing S) (hs : jg_saturated S) :
    MeasurableSet (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), jg_voronoi_open S v) :=
  Set.Finite.measurableSet_biUnion (jg_set_finite_inter_ball S hV p (r + 1))
    fun v _ => jg_measurable_voronoi v S hV hs

/-- HOL `negligible_voronoi` (pack1.hl:400): distinct open cells are
disjoint, hence null. -/
private theorem jg_negligible_voronoi (S : Set Space3) (p : Space3) (r : ℝ) :
    ∀ s ∈ {q : Set Space3 | ∃ v : Space3, ∃ w : Set Space3,
        v ∈ S ∩ Metric.ball p (r + 1) ∧ w = S ∧ q = jg_voronoi_open w v},
      ∀ t ∈ {q : Set Space3 | ∃ v : Space3, ∃ w : Set Space3,
        v ∈ S ∩ Metric.ball p (r + 1) ∧ w = S ∧ q = jg_voronoi_open w v},
        s ≠ t → volume (s ∩ t) = 0 := by
  intro s hs t ht hne
  obtain ⟨v, S', hvS, hS', hsv⟩ := hs
  obtain ⟨v', S'', hvS', hS'', hst⟩ := ht
  have hvSm : v ∈ S := hvS.1
  have hvS'm : v' ∈ S := hvS'.1
  have hsv' : s = jg_voronoi_open S v := by rw [hsv, hS']
  have hst' : t = jg_voronoi_open S v' := by rw [hst, hS'']
  have hvne : v ≠ v' := by
    intro h
    exact hne (by rw [hsv', hst', h])
  have hempty : (jg_voronoi_open S v ∩ jg_voronoi_open S v') = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have h1 : dist x v < dist x v' := hx.1 v' hvS'm (fun h => hvne h.symm)
    have h2 : dist x v' < dist x v := hx.2 v hvSm hvne
    linarith
  rw [hsv', hst', hempty]
  exact measure_empty

/-- HOL `inj_map_to_voronoi` (pack1.hl:407). -/
private theorem jg_inj_map_to_voronoi (S : Set Space3) (p : Space3) (r : ℝ) (hr : 0 ≤ r)
    (hV : Packing S) :
    ∀ q1 ∈ ((S ∩ Metric.ball p (r + 1)) ×ˢ {S}),
      ∀ q2 ∈ ((S ∩ Metric.ball p (r + 1)) ×ˢ {S}),
        jg_map_to_voronoi q1 = jg_map_to_voronoi q2 → q1 = q2 := by
  intro q1 hq1 q2 hq2 heq
  rcases q1 with ⟨x, w1⟩
  rcases q2 with ⟨y, w2⟩
  have hx : x ∈ (S ∩ Metric.ball p (r + 1)) := hq1.1
  have hw1 : w1 = S := hq1.2
  have hy : y ∈ (S ∩ Metric.ball p (r + 1)) := hq2.1
  have hw2 : w2 = S := hq2.2
  simp only [jg_map_to_voronoi] at heq
  rw [hw1, hw2] at heq
  have hxy : x = y := by
    by_contra hne
    have hxS : x ∈ S := hx.1
    have h1 : x ∈ jg_voronoi_open S x := by
      intro w _ hwx
      rw [dist_self]
      exact lt_of_le_of_ne dist_nonneg fun hc => hwx (dist_eq_zero.mp hc.symm).symm
    rw [heq] at h1
    have h2 := h1 x hxS hne
    rw [dist_self] at h2
    exact absurd h2 (not_lt.mpr dist_nonneg)
  rw [hw1, hw2, hxy]

/-- The volume of an open cell is finite (it sits inside `ball v 2`). -/
private theorem jg_volume_cell_ne_top (v : Space3) (S : Set Space3) (hV : Packing S)
    (hs : jg_saturated S) : volume (jg_voronoi_open S v) ≠ ⊤ :=
  fun hc => jg_volume_ball_ne_top v 2
    (top_le_iff.mp (le_trans (le_of_eq hc.symm) (measure_mono (jg_voronoi_subset_ball v S hV hs))))

/-- HOL `measure_unions_sum_voronoi` (pack1.hl:417), open-cell form:
finite additivity over the pairwise disjoint open cells. -/
private theorem jg_measure_unions_sum_voronoi (S : Set Space3) (p : Space3) (r : ℝ)
    (hr : 0 ≤ r) (hV : Packing S) (hs : jg_saturated S)
    (hfin : (S ∩ Metric.ball p (r + 1)).Finite) :
    (volume (⋃ v ∈ (S ∩ Metric.ball p (r + 1)), jg_voronoi_open S v)).toReal =
      ∑ v ∈ Set.Finite.toFinset hfin, (volume (jg_voronoi_open S v)).toReal := by
  classical
  rw [jg_biUnion_toFinset_eq hfin (fun v => jg_voronoi_open S v)]
  have hdisj : Set.PairwiseDisjoint
      ((Set.Finite.toFinset hfin : Finset Space3) : Set Space3)
      (fun v => jg_voronoi_open S v) := by
    intro v hv w hw hne
    show Disjoint (jg_voronoi_open S v) (jg_voronoi_open S w)
    rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hvS : v ∈ S := ((Set.Finite.mem_toFinset hfin).mp hv).1
    have hwS : w ∈ S := ((Set.Finite.mem_toFinset hfin).mp hw).1
    have h1 : dist x v < dist x w := hx.1 w hwS (Ne.symm hne)
    have h2 : dist x w < dist x v := hx.2 v hvS hne
    linarith
  rw [MeasureTheory.measure_biUnion_finset hdisj
    (fun v (_ : v ∈ Set.Finite.toFinset hfin) => jg_measurable_voronoi v S hV hs)]
  exact ENNReal.toReal_sum (fun v (_ : v ∈ Set.Finite.toFinset hfin) =>
    jg_volume_cell_ne_top v S hV hs)

/-- HOL `sum_measure_voronoi_le_ball` (pack1.hl:470), open-cell form. -/
private theorem jg_sum_measure_voronoi_le_ball (S : Set Space3) (p : Space3) (r : ℝ)
    (hr : 0 ≤ r) (hV : Packing S) (hs : jg_saturated S)
    (hfin : (S ∩ Metric.ball p (r + 1)).Finite) :
    ∑ v ∈ Set.Finite.toFinset hfin, (volume (jg_voronoi_open S v)).toReal ≤
      (volume (Metric.ball p (r + 3))).toReal := by
  classical
  have hsubT : (⋃ v ∈ Set.Finite.toFinset hfin, jg_voronoi_open S v) ⊆
      Metric.ball p (r + 3) := by
    rw [← jg_biUnion_toFinset_eq hfin (fun v => jg_voronoi_open S v)]
    exact jg_unions_voronoi_center_in_ball_subset_ball S p r hV hs
  have hneUT : volume (⋃ v ∈ Set.Finite.toFinset hfin, jg_voronoi_open S v) ≠ ⊤ :=
    fun hc => jg_volume_ball_ne_top p (r + 3)
      (top_le_iff.mp (le_trans (le_of_eq hc.symm) (measure_mono hsubT)))
  have hneB : volume (Metric.ball p (r + 3)) ≠ ⊤ := jg_volume_ball_ne_top p (r + 3)
  have hstep : ∑ v ∈ Set.Finite.toFinset hfin, (volume (jg_voronoi_open S v)).toReal
      ≤ (volume (⋃ v ∈ Set.Finite.toFinset hfin, jg_voronoi_open S v)).toReal := by
    rw [← jg_biUnion_toFinset_eq hfin (fun v => jg_voronoi_open S v)]
    exact (jg_measure_unions_sum_voronoi S p r hr hV hs hfin).symm.le
  calc ∑ v ∈ Set.Finite.toFinset hfin, (volume (jg_voronoi_open S v)).toReal
      ≤ (volume (⋃ v ∈ Set.Finite.toFinset hfin, jg_voronoi_open S v)).toReal := hstep
    _ ≤ (volume (Metric.ball p (r + 3))).toReal :=
          (ENNReal.toReal_le_toReal hneUT hneB).mpr (measure_mono hsubT)

/-- HOL `ineq_lm5_3_step3` (pack1.hl:476), open-cell form. -/
private theorem jg_ineq_lm5_3_step3 (S : Set Space3) (p : Space3) (r : ℝ) (A : Space3 → ℝ)
    (hr : 0 ≤ r) (hV : Packing S) (hs : jg_saturated S) (hfcc : jg_fcc_compatible A S)
    (hfin : (S ∩ Metric.ball p (r + 1)).Finite) :
    Real.sqrt 32 * ((S ∩ Metric.ball p (r + 1)).ncard : ℝ) ≤
      ∑ v ∈ Set.Finite.toFinset hfin, (A v + (volume (jg_voronoi_open S v)).toReal) := by
  have h1 : ∑ v ∈ Set.Finite.toFinset hfin, Real.sqrt 32 ≤
      ∑ v ∈ Set.Finite.toFinset hfin, (A v + (volume (jg_voronoi_open S v)).toReal) := by
    refine Finset.sum_le_sum fun v hv => ?_
    have hvT : v ∈ (S ∩ Metric.ball p (r + 1)) := (Set.Finite.mem_toFinset hfin).mp hv
    have hh := hfcc v hvT.1
    linarith
  have h2 : Real.sqrt 32 * ((S ∩ Metric.ball p (r + 1)).ncard : ℝ) =
      ∑ v ∈ Set.Finite.toFinset hfin, Real.sqrt 32 := by
    rw [Set.ncard_eq_toFinset_card (S ∩ Metric.ball p (r + 1)) hfin, Finset.sum_const,
      nsmul_eq_mul]
    exact mul_comm _ _
  rw [h2]
  exact h1

/-- HOL `ineq_lm5_3_step4` (pack1.hl:485): for every `c ≥ 0` the constant
`c' = 63π/√18 + 4c/√32` absorbs the `(1 + 3/r)³` and packing-count error
terms. -/
private theorem jg_ineq_lm5_3_step4 (c : ℝ) (hc : 0 ≤ c) :
    ∃ c' : ℝ, ∀ r : ℝ, 1 ≤ r →
      Real.pi / Real.sqrt 18 * (1 + 3 / r) ^ 3 +
          c * (r + 1) ^ 2 / (r ^ 3 * Real.sqrt 32) ≤
        Real.pi / Real.sqrt 18 + c' / r := by
  refine ⟨63 * Real.pi / Real.sqrt 18 + 4 * c / Real.sqrt 32, fun r hr => ?_⟩
  have hr1 : 0 ≤ r - 1 := by linarith
  have hr3 : 0 < r ^ 3 := pow_pos (by linarith : (0:ℝ) < r) 3
  have hsq18 : 0 < Real.sqrt 18 := Real.sqrt_pos.mpr (by norm_num)
  have hsq32 : 0 < Real.sqrt 32 := Real.sqrt_pos.mpr (by norm_num)
  have hk : 0 < r ^ 3 * Real.sqrt 18 * Real.sqrt 32 :=
    mul_pos (mul_pos hr3 hsq18) hsq32
  have exppow : (1 + 3 / r) ^ 3 = 1 + 9 / r + 27 / r ^ 2 + 27 / r ^ 3 := by
    field_simp
    ring
  have sq1 : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
  have cube1 : (r + 3) ^ 3 = r ^ 3 + 9 * r ^ 2 + 27 * r + 27 := by ring
  have hK1 : (0:ℝ) ≤ (2 * r + 1) * (r - 1) :=
    mul_nonneg (by linarith) hr1
  have hK2 : (0:ℝ) ≤ (3 * r + 1) * (r - 1) :=
    mul_nonneg (by linarith) hr1
  have hclearedL : (Real.pi / Real.sqrt 18 * (1 + 3 / r) ^ 3 +
        c * (r + 1) ^ 2 / (r ^ 3 * Real.sqrt 32)) * (r ^ 3 * Real.sqrt 18 * Real.sqrt 32)
      = Real.pi * Real.sqrt 32 * (r + 3) ^ 3 + c * Real.sqrt 18 * (r + 1) ^ 2 := by
    rw [exppow, sq1]
    field_simp
    ring
  have hclearedR : (Real.pi / Real.sqrt 18 +
        (63 * Real.pi / Real.sqrt 18 + 4 * c / Real.sqrt 32) / r) *
        (r ^ 3 * Real.sqrt 18 * Real.sqrt 32)
      = Real.pi * Real.sqrt 32 * r ^ 3 + 63 * Real.pi * Real.sqrt 32 * r ^ 2 +
        4 * c * Real.sqrt 18 * r ^ 2 := by
    field_simp
    ring
  have hpol : Real.pi * Real.sqrt 32 * (r + 3) ^ 3 + c * Real.sqrt 18 * (r + 1) ^ 2 ≤
      Real.pi * Real.sqrt 32 * r ^ 3 + 63 * Real.pi * Real.sqrt 32 * r ^ 2 +
        4 * c * Real.sqrt 18 * r ^ 2 := by
    have hpi32 : (0:ℝ) ≤ Real.pi * Real.sqrt 32 := mul_nonneg Real.pi_pos.le hsq32.le
    have hc18 : (0:ℝ) ≤ c * Real.sqrt 18 := mul_nonneg hc hsq18.le
    rw [cube1, sq1]
    linarith [hK1, hK2, mul_nonneg hpi32 hK1, mul_nonneg hc18 hK2]
  have hkey : (Real.pi / Real.sqrt 18 * (1 + 3 / r) ^ 3 +
        c * (r + 1) ^ 2 / (r ^ 3 * Real.sqrt 32)) * (r ^ 3 * Real.sqrt 18 * Real.sqrt 32) ≤
      (Real.pi / Real.sqrt 18 +
        (63 * Real.pi / Real.sqrt 18 + 4 * c / Real.sqrt 32) / r) *
        (r ^ 3 * Real.sqrt 18 * Real.sqrt 32) := by
    rw [hclearedL, hclearedR]
    exact hpol
  exact le_of_mul_le_mul_right hkey hk

/-! ### The capstone -/

/-- HOL `JGXZYGW` (pack1.hl:519): the density bound conditional on an
`fcc_compatible` and `negligible_fun_p` functional, with `p` explicit.

All definitions (`saturated`, the open Voronoi cell, `negligible_fun_p`)
are inlined in the statement so that consumers with their own encodings
(`volume.real`, `voronoiOpen`, `setSum` in PackingAuto2/PackingAuto19) can
bridge by `rfl`-level conversions. -/
theorem jgxzygw_p (S : Set Space3) (p : Space3) (hV : Packing S)
    (hs : ∀ x : Space3, ∃ y ∈ S, dist x y < 2)
    (hA : ∃ A : Space3 → ℝ,
      (∀ v ∈ S, Real.sqrt 32 ≤
          (volume {x : Space3 | ∀ w, w ∈ S → w ≠ v → dist x v < dist x w}).toReal + A v) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ h : (S ∩ Metric.ball p r).Finite,
        (∑ v ∈ Set.Finite.toFinset h, A v) ≤ C * r ^ 2)) :
    ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
      (volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r)).toReal /
        (volume (Metric.ball p r)).toReal ≤
        Real.pi / Real.sqrt 18 + c / r := by
  obtain ⟨A, hfcc, hneg⟩ := hA
  obtain ⟨C, hC0, hC⟩ := hneg
  obtain ⟨c', hc'⟩ := jg_ineq_lm5_3_step4 C hC0
  refine ⟨c', fun r hr => ?_⟩
  classical
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hr1 : 0 ≤ r + 1 := by linarith
  have hr3 : 0 ≤ r + 3 := by linarith
  have hM : (volume (Metric.ball p r)).toReal = 4 * Real.pi / 3 * r ^ 3 :=
    jg_volume_ball p r hr0
  have hMpos : 0 < (volume (Metric.ball p r)).toReal := by
    rw [hM]
    exact mul_pos (by linarith [Real.pi_pos]) (pow_pos (by linarith) 3)
  have hfin : (S ∩ Metric.ball p (r + 1)).Finite := jg_set_finite_inter_ball S hV p (r + 1)
  have hneg' : (∑ v ∈ Set.Finite.toFinset hfin, A v) ≤ C * (r + 1) ^ 2 :=
    hC (r + 1) (by linarith) hfin
  have hstep3 := jg_ineq_lm5_3_step3 S p r A hr0 hV hs hfcc hfin
  have hsum := jg_sum_measure_voronoi_le_ball S p r hr0 hV hs hfin
  -- √32 · n ≤ C (r+1)² + (1 + 3/r)³ · vol(ball p r)
  have hrne : (r : ℝ) ≠ 0 := by linarith
  have hsq18 : (0:ℝ) < Real.sqrt 18 := Real.sqrt_pos.mpr (by norm_num)
  have hsq32 : (0:ℝ) < Real.sqrt 32 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtle : Real.sqrt 32 * ((S ∩ Metric.ball p (r + 1)).ncard : ℝ) ≤
      C * (r + 1) ^ 2 + (1 + 3 / r) ^ 3 * (volume (Metric.ball p r)).toReal := by
    have hvol3 : (volume (Metric.ball p (r + 3))).toReal =
        (1 + 3 / r) ^ 3 * (volume (Metric.ball p r)).toReal := by
      rw [jg_volume_ball p (r + 3) hr3, jg_volume_ball p r hr0]
      field_simp
    calc Real.sqrt 32 * ((S ∩ Metric.ball p (r + 1)).ncard : ℝ)
        ≤ ∑ v ∈ Set.Finite.toFinset hfin, (A v + (volume (jg_voronoi_open S v)).toReal) :=
          hstep3
      _ = ∑ v ∈ Set.Finite.toFinset hfin, A v +
            ∑ v ∈ Set.Finite.toFinset hfin, (volume (jg_voronoi_open S v)).toReal :=
            Finset.sum_add_distrib
      _ ≤ C * (r + 1) ^ 2 + (volume (Metric.ball p (r + 3))).toReal :=
          add_le_add hneg' hsum
      _ = C * (r + 1) ^ 2 + (1 + 3 / r) ^ 3 * (volume (Metric.ball p r)).toReal :=
          by rw [hvol3]
  -- 4π/(3·√32) = π/√18
  have h2sqrt : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h18 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    rw [show (18 : ℝ) = 9 * 2 from by norm_num,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 9) 2]
    norm_num
  have h32 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
    rw [show (32 : ℝ) = 16 * 2 from by norm_num,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16) 2]
    norm_num
  have h43 : (4:ℝ) * Real.sqrt 18 = 3 * Real.sqrt 32 := by rw [h18, h32]; ring
  have hpidiv : 4 * Real.pi / (3 * Real.sqrt 32) = Real.pi / Real.sqrt 18 := by
    have kpos : (0:ℝ) < 3 * Real.sqrt 32 * Real.sqrt 18 := by positivity
    have hL : (3 * Real.sqrt 32 * Real.sqrt 18) * (4 * Real.pi / (3 * Real.sqrt 32))
        = 4 * Real.pi * Real.sqrt 18 := by
      field_simp [hsq32.ne']
    have hR : (3 * Real.sqrt 32 * Real.sqrt 18) * (Real.pi / Real.sqrt 18)
        = 3 * Real.sqrt 32 * Real.pi := by
      field_simp [hsq18.ne']
    have hcong : (4 * Real.sqrt 18) * Real.pi = (3 * Real.sqrt 32) * Real.pi := by
      rw [h43]
    refine mul_left_cancel₀ (ne_of_gt kpos) (hL.trans ?_)
    rw [show (4:ℝ) * Real.pi * Real.sqrt 18 = (4 * Real.sqrt 18) * Real.pi from by ring,
      hcong]
    exact hR.symm
  have hKpos : 0 ≤ 4 * Real.pi / (3 * Real.sqrt 32) := by
    refine div_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) ?_
    exact le_of_lt (mul_pos (by norm_num) hsq32)
  -- Step 1 + card: the left-hand volume is at most n · 4π/3
  have h1 := jg_measure_ineq_lm53_2 S p r hr0 hV
  rw [jg_card_eq_ball_point S p r hr0 hV] at h1
  -- ... ≤ M · (π/√18 · (1+3/r)³ + C(r+1)²/(r³·√32)) ≤ M · (π/√18 + c'/r)
  have h3 : (C * (r + 1) ^ 2 + (1 + 3 / r) ^ 3 * (volume (Metric.ball p r)).toReal) *
        (4 * Real.pi / (3 * Real.sqrt 32)) =
      (volume (Metric.ball p r)).toReal *
        (Real.pi / Real.sqrt 18 * (1 + 3 / r) ^ 3 +
          C * (r + 1) ^ 2 / (r ^ 3 * Real.sqrt 32)) := by
    have e1 : (1 + 3 / r) ^ 3 = 1 + 9 / r + 27 / r ^ 2 + 27 / r ^ 3 := by
      field_simp
      ring
    rw [hpidiv, hM, e1]
    field_simp [hrne, hsq18.ne', hsq32.ne', h2sqrt.ne']
    all_goals
      have hCres : (3:ℝ) * Real.sqrt 32 * (C * (r + 1) ^ 2)
          = 4 * Real.sqrt 18 * (C * (r + 1) ^ 2) := by rw [h43.symm]
      linarith [hCres]
  have hbound : (volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r)).toReal ≤
      (Real.pi / Real.sqrt 18 + c' / r) * (volume (Metric.ball p r)).toReal := by
    have hrw : ((S ∩ Metric.ball p (r + 1)).ncard : ℝ) * 4 * Real.pi / 3 =
        (Real.sqrt 32 * ((S ∩ Metric.ball p (r + 1)).ncard : ℝ)) *
          (4 * Real.pi / (3 * Real.sqrt 32)) := by
      field_simp [hsq32.ne', h2sqrt.ne']
    calc (volume ((⋃ v ∈ S, Metric.ball v 1) ∩ Metric.ball p r)).toReal
        ≤ ((S ∩ Metric.ball p (r + 1)).ncard : ℝ) * 4 * Real.pi / 3 := h1
      _ ≤ (volume (Metric.ball p r)).toReal *
            (Real.pi / Real.sqrt 18 * (1 + 3 / r) ^ 3 +
              C * (r + 1) ^ 2 / (r ^ 3 * Real.sqrt 32)) := by
          rw [hrw]
          exact le_trans (mul_le_mul_of_nonneg_right hsqrtle hKpos) h3.le
      _ ≤ (volume (Metric.ball p r)).toReal * (Real.pi / Real.sqrt 18 + c' / r) :=
          mul_le_mul_of_nonneg_left (hc' r hr) hMpos.le
      _ ≤ (Real.pi / Real.sqrt 18 + c' / r) * (volume (Metric.ball p r)).toReal := by
          rw [mul_comm]
  exact (div_le_iff₀ hMpos).mpr hbound

end

end Kepler.Text
