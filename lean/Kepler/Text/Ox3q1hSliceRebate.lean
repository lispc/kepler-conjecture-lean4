/-
Ox3q1hSliceRebate: S2-remainder base for the ox3q1h corner tables
(lane `ox3q1h-nogate-w1`).

Generic curvature-rebate kit: a chord-rebate lemma turns a
shifted-concavity certificate — `ConcaveOn` of `fun t => f t - K/2*t*t`
on the axis interval, the twice-differentiable reading of `f'' ≤ K` —
into the per-slice rebate premise consumed by
`Ox3q1hRebate.descend_step_le` (rebate `R i = K i * (hi i - lo i)^2/8`),
plus the composed box-vertex interface for the S4 assembly.

The numeric side (per-box, per-slot dyadic `K` envelopes on
`|f''|`, following the `Gamma4Concave` mechanism) is the follow-up
lane's obligation: this file contains no numeric data.
-/
import Mathlib
import Kepler.Text.Ox3q1hRebate

open Set

namespace Kepler.Text

/-- Chord rebate: if `f - K/2·(·)²` is concave on `[a, b]` (the
twice-differentiable reading of `f'' ≤ K` on the interval), then every
`t ∈ [a, b]` satisfies `f t ≥ min (f a) (f b) - K·(b-a)²/8`. -/
theorem rebate_of_concave_shifted {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    {K : ℝ} (hK : 0 ≤ K)
    (hg : ConcaveOn ℝ (Set.Icc a b) (fun t => f t - K / 2 * t * t))
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    min (f a) (f b) - K * (b - a) ^ 2 / 8 ≤ f t := by
  rcases eq_or_lt_of_le hab with heq | hden0
  · rw [heq] at ht ⊢
    have hta : t = b := le_antisymm ht.2 ht.1
    subst hta
    simp
  · have hden : (0:ℝ) < b - a := by linarith
    have hbne : b - a ≠ 0 := by linarith
    have hαdef : (b - t) / (b - a) = (b - t) / (b - a) := rfl
    set α : ℝ := (b - t) / (b - a) with hα
    set β : ℝ := (t - a) / (b - a) with hβ
    have hα0 : 0 ≤ α := by
      rw [hα]
      exact div_nonneg (by linarith [ht.2]) (le_of_lt hden)
    have hβ0 : 0 ≤ β := by
      rw [hβ]
      exact div_nonneg (by linarith [ht.1]) (le_of_lt hden)
    have hαβ1 : α + β = 1 := by
      rw [hα, hβ]
      field_simp
      ring
    have hmem_a : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    have hmem_b : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
    have hconc := hg.2 hmem_a hmem_b hα0 hβ0 hαβ1
    simp only [smul_eq_mul] at hconc
    rw [show α * a + β * b = t from by
      rw [hα, hβ]
      field_simp
      ring] at hconc
    -- chord decomposition: min ≤ chord and the quadratic dip bound
    have hmin1 : min (f a) (f b) ≤ α * f a + β * f b := by
      have h1 : α * min (f a) (f b) ≤ α * f a :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hα0
      have h2 : β * min (f a) (f b) ≤ β * f b :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hβ0
      have h3 : α * min (f a) (f b) + β * min (f a) (f b) ≤
          α * f a + β * f b := add_le_add h1 h2
      have h4 : α * min (f a) (f b) + β * min (f a) (f b) =
          min (f a) (f b) := by
        rw [← add_mul, hαβ1, one_mul]
      linarith
    -- key identity: α·a² + β·b² - t² = α·β·(b-a)²
    have hident : α * (a * a) + β * (b * b) - t * t =
        α * β * ((b - a) * (b - a)) := by
      rw [hα, hβ]
      field_simp
      ring
    -- α·β ≤ 1/4
    have hsq1 : (α + β) ^ 2 = 1 := by rw [hαβ1]; ring
    have hsq2 : 0 ≤ (α - β) ^ 2 := sq_nonneg _
    have hab4 : α * β ≤ 1 / 4 := by nlinarith
    have hQ : K / 2 * (α * (a * a) + β * (b * b) - t * t)
        ≤ K * (b - a) ^ 2 / 8 := by
      have h3 : 0 ≤ (b - a) * (b - a) := mul_self_nonneg (b - a)
      have h4 : α * β * ((b - a) * (b - a))
          ≤ (b - a) * (b - a) / 4 := by
        nlinarith [hab4, h3]
      rw [hident]
      nlinarith [h4, hK, hden]
    linarith

/-- The slice-rebate premise of `Ox3q1hRebate.descend_step_le` for
coordinate `i`, produced from a shifted-concavity certificate of the
`i`-axis slice of `f` over the outward box. -/
theorem slice_hper {n : ℕ} {f : (Fin n → ℝ) → ℝ} {lo hi K : Fin n → ℝ}
    {i : Fin n} (hK : 0 ≤ K i) (hlohi : lo i ≤ hi i)
    (hsl : ∀ y : Fin n → ℝ, ConcaveOn ℝ (Set.Icc (lo i) (hi i))
      (fun t => f (Function.update y i t) - K i / 2 * t * t))
    (y : Fin n → ℝ) :
    ∀ t ∈ Set.Icc (lo i) (hi i),
      f (Function.update y i t) ≥
        min (f (Function.update y i (lo i)))
          (f (Function.update y i (hi i)))
        - K i * (hi i - lo i) ^ 2 / 8 :=
  fun t ht => rebate_of_concave_shifted hlohi hK (hsl y) ht

/-- Composed S2→S4 interface: from per-coordinate shifted-concavity
certificates (with per-coordinate curvature bound `K i`), some box
vertex `v` carries `f x ≥ f v - Σ K i·W i²/8`; combining with the
corner-table lower bound at `v` finishes each rebate-feasible conjunct. -/
theorem exists_vertex_rebate_of_shifted_concave {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {lo hi K : Fin n → ℝ}
    (hK : ∀ i, 0 ≤ K i) (hlohi : ∀ i, lo i ≤ hi i)
    (hsl : ∀ (i : Fin n) (y : Fin n → ℝ),
      ConcaveOn ℝ (Set.Icc (lo i) (hi i))
        (fun t => f (Function.update y i t) - K i / 2 * t * t))
    (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Set.Icc (lo j) (hi j)) :
    ∃ v : Fin n → ℝ, (∀ j, v j ∈ Set.Icc (lo j) (hi j)) ∧
      f x ≥ f v - ∑ i, K i * (hi i - lo i) ^ 2 / 8 := by
  have hxmem : ∀ j, x j ∈ Set.Icc (lo j) (hi j) := hx
  have hper : ∀ (i : Fin n) (y : Fin n → ℝ),
      (∀ j, y j ∈ Set.Icc (lo j) (hi j)) →
      ∀ t ∈ Set.Icc (lo i) (hi i),
        f (Function.update y i t) ≥
          min (f (Function.update y i (lo i)))
            (f (Function.update y i (hi i)))
          - K i * (hi i - lo i) ^ 2 / 8 :=
    fun i y _ t ht => slice_hper (hK i) (hlohi i) (hsl i) y t ht
  exact exists_vertex_rebate hper x hxmem hlohi

/-! ### Axiom audit -/

#print axioms rebate_of_concave_shifted
#print axioms slice_hper
#print axioms exists_vertex_rebate_of_shifted_concave

end Kepler.Text
