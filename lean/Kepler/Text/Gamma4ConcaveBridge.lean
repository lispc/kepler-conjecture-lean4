/-
Kepler.Text.Gamma4ConcaveBridge — lane `g4-hessian-lean-w1` (2026-11-18):
the C²→ConcaveOn bridge consumed by the B0 y1 slice concavity route.

`concaveOn_of_hasDerivAt2_nonpos`: pointwise `HasDerivAt` version of
Mathlib's `concaveOn_of_hasDerivWithinAt2_nonpos`
(Mathlib.Analysis.Convex.Deriv; in-tree precedent TameLp.lean applies the
same lemma with explicit `HasDerivAt.hasDerivWithinAt` rewrites).  From
`f'` everywhere on `Icc a b` and `f'' ≤ 0` on `Ioo a b` (both pointwise,
with `f''` explicit) conclude `ConcaveOn ℝ (Icc a b) f`; degenerate
intervals (`a > b`) handled by emptiness.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/
import Mathlib.Analysis.Convex.Deriv

open Set

/-- W5 bridge (lane g4-hessian-lean-w1): pointwise second-derivative
nonpositivity on the open interval plus pointwise first derivatives
everywhere on the closed interval gives concavity on the closed interval. -/
theorem concaveOn_of_hasDerivAt2_nonpos {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hf2 : ∀ t ∈ Set.Ioo a b, HasDerivAt f' (f'' t) t)
    (hneg : ∀ t ∈ Set.Ioo a b, f'' t ≤ 0) :
    ConcaveOn ℝ (Set.Icc a b) f := by
  by_cases hab : a ≤ b
  · refine concaveOn_of_hasDerivWithinAt2_nonpos (D := Set.Icc a b) (f := f)
      (f' := f') (f'' := f'') (convex_Icc a b) ?_ ?_ ?_ ?_
    · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo a b := by rwa [interior_Icc] at ht
      exact (hf t ⟨ht'.1.le, ht'.2.le⟩).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo a b := by rwa [interior_Icc] at ht
      exact (hf2 t ht').hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo a b := by rwa [interior_Icc] at ht
      exact hneg t ht'
  · have hempty : Set.Icc a b = ∅ := Set.Icc_eq_empty hab
    rw [hempty]
    exact ⟨convex_empty, by simp⟩

#print axioms concaveOn_of_hasDerivAt2_nonpos
