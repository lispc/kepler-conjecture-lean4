/-
Ox3q1hRebate: the curvature-rebate reduction kit for the ox3q1h corner
tables (lane `ox3q1h-nogate-w1`, S2 Batch 1).

Direction convention (matches NOGATE_PLAN §5): the corner tables give a
lower bound for `f` at every box vertex; the curvature rebates `R i`
bound how far `f` can dip below the vertex values inside the box.  The
kit produces a vertex `v` with `f v ≤ f x + Σ R i`, i.e.
`f x ≥ f v − Σ R i ≥ (min vertex value) − Σ R i`.

The γ4/dihY curvature envelopes backing the R_i are the follow-up lane's
obligation (NOGATE_PLAN §6 S3).  No `sorry`; axiom audit at the end.
-/
import Mathlib

open Set

namespace Kepler.Text

/-- One coordinate-descent step: if every point on the `i`-th slice has
`f`-value at least `min(endpoints) − R`, then some endpoint-replacement
`v` of `y` satisfies `f v ≤ f y + R`. -/
theorem descend_step_le {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {lo hi : Fin n → ℝ} {i : Fin n} {R : ℝ} {y : Fin n → ℝ}
    (hymem : ∀ j, y j ∈ Icc (lo j) (hi j))
    (hper : ∀ t ∈ Icc (lo i) (hi i),
      f (Function.update y i t) ≥
        min (f (Function.update y i (lo i))) (f (Function.update y i (hi i)))
        - R)
    (hlohi : lo i ≤ hi i) :
    ∃ v : Fin n → ℝ, (∀ j ≠ i, v j = y j) ∧ (v i ∈ Icc (lo i) (hi i)) ∧
      f v ≤ f y + R := by
  -- apply hper at t = y i
  have hs := hper (y i) (hymem i)
  -- the update at position i with value y i agrees with y everywhere
  have heq : Function.update y i (y i) = y := by
    funext j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]
    · rw [Function.update_of_ne hj]
  rw [heq] at hs
  -- hs : f y ≥ min (f (update y i (lo i))) (f (update y i (hi i))) - R
  -- ⇒ min(a, b) ≤ f y + R  where a, b are the two endpoint f-values
  have hmin : min (f (Function.update y i (lo i))) (f (Function.update y i (hi i)))
      ≤ f y + R := by linarith
  rcases min_le_iff.mp hmin with hlo | hhi
  · refine ⟨Function.update y i (lo i),
      fun j hne => by rw [Function.update_of_ne hne], ?_, ?_⟩
    · rw [Function.update_self]
      exact mem_Icc.mpr ⟨le_rfl, hlohi⟩
    · exact hlo
  · refine ⟨Function.update y i (hi i),
      fun j hne => by rw [Function.update_of_ne hne], ?_, ?_⟩
    · rw [Function.update_self]
      exact mem_Icc.mpr ⟨hlohi, le_rfl⟩
    · exact hhi

/-- Iterating the per-slice rebate descent over all `Fin n` coordinates
produces a vertex `v` with `f v ≤ f x + Σ_i R i`. -/
theorem exists_vertex_descend {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {lo hi R : Fin n → ℝ}
    (hper : ∀ (i : Fin n) (y : Fin n → ℝ), (∀ j, y j ∈ Icc (lo j) (hi j)) →
      ∀ t ∈ Icc (lo i) (hi i),
        f (Function.update y i t) ≥
          min (f (Function.update y i (lo i))) (f (Function.update y i (hi i)))
          - R i)
    (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Icc (lo j) (hi j)) (hlohi : ∀ i, lo i ≤ hi i) :
    ∃ v : Fin n → ℝ, (∀ j, v j ∈ Icc (lo j) (hi j)) ∧
      f v ≤ f x + ∑ i, R i := by
  classical
  have hkey : ∀ (s : Finset (Fin n)),
      ∃ y : Fin n → ℝ,
        (∀ j ∈ s, y j ∈ Icc (lo j) (hi j)) ∧
        (∀ j ∉ s, y j = x j) ∧
        f y ≤ f x + ∑ i ∈ s, R i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨x, fun j _ => hx j, fun j _ => rfl, by simp⟩
    | insert i s his ih =>
        obtain ⟨y, hymem, hyx, hsum⟩ := ih
        have hallmem : ∀ j, y j ∈ Icc (lo j) (hi j) := by
          intro j
          by_cases hj : j ∈ s
          · exact hymem j hj
          · rw [hyx j hj]
            exact hx j
        have hper_i := hper i y hallmem
        obtain ⟨v, hveq, hvmem, hreb⟩ :=
          descend_step_le (f := f) (lo := lo) (hi := hi) (i := i) (R := R i)
            (y := y) hallmem hper_i (hlohi i)
        refine ⟨v, ?_, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hvmem
          · have jne : j ≠ i := fun h => his (h ▸ hj)
            rw [hveq j jne]
            exact hymem j hj
        · intro j hj
          have hji : j ≠ i := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
          have hjs : j ∉ s := fun h => hj (Finset.mem_insert.mpr (Or.inr h))
          rw [hveq j hji, hyx j hjs]
        · rw [Finset.sum_insert his]
          linarith
  obtain ⟨v, h1, h2, h3⟩ := hkey Finset.univ
  exact ⟨v, fun j => h1 j (Finset.mem_univ j), h3⟩

/-- Rebate reading (NOGATE_PLAN §5): some box vertex `v` has
`f x ≥ f v − Σ R i`, so `f x` is bounded below by the vertex table
minimum minus the total rebate. -/
theorem exists_vertex_rebate {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {lo hi R : Fin n → ℝ}
    (hper : ∀ (i : Fin n) (y : Fin n → ℝ), (∀ j, y j ∈ Icc (lo j) (hi j)) →
      ∀ t ∈ Icc (lo i) (hi i),
        f (Function.update y i t) ≥
          min (f (Function.update y i (lo i))) (f (Function.update y i (hi i)))
          - R i)
    (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Icc (lo j) (hi j)) (hlohi : ∀ i, lo i ≤ hi i) :
    ∃ v : Fin n → ℝ, (∀ j, v j ∈ Icc (lo j) (hi j)) ∧
      f x ≥ f v - ∑ i, R i := by
  obtain ⟨v, hv, hle⟩ := exists_vertex_descend hper x hx hlohi
  exact ⟨v, hv, by linarith⟩

/-! ### Axiom audit -/

#print axioms descend_step_le
#print axioms exists_vertex_descend
#print axioms exists_vertex_rebate

end Kepler.Text
