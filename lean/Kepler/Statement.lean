/-
  Phase 1 — Statement of the Kepler conjecture.

  This file mirrors, definition by definition, the Flyspeck statement
  `the_kepler_conjecture` (reference/flyspeck, commit 1ce0353,
  `text_formalization/general/the_main_statement.hl:19-24`):

      the_kepler_conjecture <=>
        (!V. packing V
               ==> (?c. !r. &1 <= r
                            ==> &(CARD(V INTER ball(vec 0,r))) <=
                                pi * r pow 3 / sqrt(&18) + c * r pow 2))

  with `packing` from `text_formalization/general/sphere.hl:425`:

      packing V <=> (!u v. u IN V /\ v IN V /\ dist(u,v) < &2 ==> u = v)

  The item-by-item correspondence is documented in
  `docs/statement-fidelity.md`. The proof body is a deliberate `sorry`
  placeholder (allowed by PLAN.md §4 Phase 1); the *statement* itself
  is complete and sorry-free.
-/
import Mathlib

open MeasureTheory Metric Set

namespace Kepler

/-- The ambient Euclidean 3-space (HOL Light's `real^3`). -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- `Packing V`: the centers of a family of non-overlapping unit balls in ℝ³.
    Any two distinct centers are at distance at least 2.
    Mirrors Flyspeck `Sphere.packing`. -/
def Packing (V : Set Space3) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, dist u v < 2 → u = v

theorem Packing.dist_ge_two {V : Set Space3} (hV : Packing V)
    {u v : Space3} (hu : u ∈ V) (hv : v ∈ V) (hne : u ≠ v) : 2 ≤ dist u v :=
  le_of_not_gt fun h => hne (hV u hu v hv h)

/-- Centers of a packing inside a bounded ball form a finite set: the unit
    balls around them are pairwise disjoint and all lie in `ball 0 (r + 1)`,
    so volume counting bounds their number. This justifies reading
    `(V ∩ ball 0 r).ncard` as a genuine cardinality (see the fidelity doc). -/
theorem Packing.finite_inter_ball {V : Set Space3} (hV : Packing V) (r : ℝ) :
    (V ∩ Metric.ball 0 r).Finite := by
  classical
  rcases le_total r 0 with hr | hr
  · -- `ball 0 r` is empty for `r ≤ 0`.
    rw [Metric.ball_eq_empty.mpr hr]
    simp
  -- Volume-counting bound: any finite subset `T` of the centers satisfies
  -- `T.card * (4π/3) ≤ (r+1)³ * (4π/3)`, hence `(T.card : ℝ) ≤ (r+1)³`.
  have key : ∀ T : Finset Space3, (∀ v ∈ T, v ∈ V ∩ Metric.ball 0 r) →
      (T.card : ℝ) ≤ (r + 1) ^ 3 := by
    intro T hT
    have hdisj : (T : Set Space3).PairwiseDisjoint (fun v => Metric.ball v 1) := by
      intro u hu v hv hne
      have hdist := hV.dist_ge_two (hT u hu).1 (hT v hv).1 hne
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
      have hvr : dist v 0 < r := Metric.mem_ball.mp (hT v hvT).2
      rw [Metric.mem_ball] at hwv ⊢
      calc dist w 0 ≤ dist w v + dist v 0 := dist_triangle w v 0
      _ < 1 + r := by linarith
      _ = r + 1 := by ring
    have hmeas : ∀ v ∈ T, MeasurableSet (Metric.ball v 1) :=
      fun v _ => measurableSet_ball
    have hsum := measure_biUnion_finset hdisj hmeas (μ := volume)
    have hle := measure_mono hsub (μ := volume)
    rw [hsum] at hle
    simp only [EuclideanSpace.volume_ball_fin_three] at hle
    -- hle : ∑ v ∈ T, .ofReal 1 ^ 3 * .ofReal (π * 4 / 3) ≤ .ofReal (r+1) ^ 3 * .ofReal (π * 4/3)
    simp only [ENNReal.ofReal_one, one_pow, one_mul] at hle
    rw [Finset.sum_const, nsmul_eq_mul] at hle
    have hr1 : (0 : ℝ) ≤ r + 1 := by linarith
    rw [← ENNReal.ofReal_pow hr1, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
    nlinarith [Real.pi_pos]
  -- If `V ∩ ball 0 r` were infinite, it would contain finite subsets of
  -- arbitrarily large cardinality, contradicting the bound above.
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨T, hTsub, hTcard⟩ :=
    hinf.exists_subset_card_eq (Nat.floor ((r + 1) ^ 3) + 1)
  have hbound := key T (fun v hv => hTsub (Finset.mem_coe.mpr hv))
  rw [hTcard] at hbound
  push_cast at hbound
  have hfl : (r + 1) ^ 3 < (Nat.floor ((r + 1) ^ 3) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  linarith

/-- **The Kepler conjecture** (Flyspeck `the_kepler_conjecture`):
    for every packing `V` of unit balls in ℝ³ there is a constant `c` such
    that for all radii `r ≥ 1`, the number of centers inside `ball 0 r`
    is at most `π r³ / √18 + c r²`.

    The proof body is a Phase-1 `sorry` placeholder (PLAN.md §4); the
    statement itself is complete and sorry-free. -/
theorem the_kepler_conjecture :
    ∀ V : Set Space3, Packing V →
      ∃ c : ℝ, ∀ r : ℝ, 1 ≤ r →
        ((V ∩ Metric.ball 0 r).ncard : ℝ) ≤
          Real.pi * r ^ 3 / Real.sqrt 18 + c * r ^ 2 := by
  sorry

end Kepler
