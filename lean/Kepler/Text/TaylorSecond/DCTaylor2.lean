/-
Kepler.Text.TaylorSecond.DCTaylor2 — lane `wt1-emission-pilot-w1`, M2 item 1
(2026-11-25).

The **first-order (T2) Taylor terminal** of the wt1 emission:

  `T2 = fc − Σ_i w_i sup_box|∂_i f|`

(`scripts/coverage.py`: "T2 (value + first) : `fc − Σ w_i sup_box|∂_i f| > 0`
(mean value theorem)"; `scripts/refine_t2.py` measures exactly this quantity).
It is the `taylor3_*` scaffolding of `Taylor3.lean` with the Lagrange remainder
dropped and the one-dimensional step replaced by Lagrange's mean value theorem
(`exists_hasDerivAt_eq_slope`), which is also the terminal HOL's
`m_taylor_bounds` uses for its linear part.

Contents
  1. `taylor2_upper` / `taylor2_lower` — one-sided first-order bounds;
  2. `dAbs` / `dAbs_mem` — outward dyadic absolute value;
  3. `dcT2_pos` — the DC T2 terminal (point value + box/point gradient from
     DC brackets), the DC counterpart of `w1F3Z_pos_of_slack2` with the
     Hessian term dropped.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.DCMatan
import Kepler.Text.TaylorSecond.Taylor3

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Filter
open scoped Topology

/-- **One-sided first-order Taylor upper bound in three variables.**

From a lower bound `fc` of the centre value and **box-wide** upper bounds
`g i` on the coordinate partials, `f x ≤ fc + Σ_i w i * g i` on the box.  The
gradient bound is box-wide because the mean value theorem lands at an unknown
interior point (`taylor3_upper` gets away with the centre gradient only
because the Lagrange remainder evaluates the derivative at the left endpoint).
This is exactly the T2 quantity of `scripts/coverage.py`. -/
theorem taylor2_upper {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    {c : Fin 3 → ℝ} {w : Fin 3 → ℝ} {fc : ℝ} {g : Fin 3 → ℝ}
    (hc : c ∈ D)
    (hconv : ∀ x ∈ D, ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun i => c i + t * (x i - c i)) ∈ D)
    (hC1 : ∀ x ∈ D, ContDiffAt ℝ 1 f x)
    (hw : ∀ x ∈ D, ∀ i, |x i - c i| ≤ w i)
    (hval : f c ≤ fc)
    (hg : ∀ x ∈ D, ∀ i, |partial1 i f x| ≤ g i) :
    ∀ x ∈ D, f x ≤ fc + ∑ i, w i * g i := by
  intro x hx
  -- the segment and its parametrisation
  set h : Fin 3 → ℝ := fun i => x i - c i with hh
  set γ : ℝ → (Fin 3 → ℝ) := fun t i => c i + t * h i with hγ
  set G : ℝ → ℝ := fun t => f (γ t) with hG
  have hhi : ∀ i, h i = x i - c i := fun i => by rw [hh]
  have hγ0 : γ 0 = c := by
    funext i
    simp [hγ]
  have hγ1 : γ 1 = x := by
    funext i
    simp only [hγ, one_mul]
    ring
  have hγγ : γ = fun t => c + t • h := by
    funext t i
    simp [hγ, Pi.add_apply, Pi.smul_apply]
  have hγderiv : ∀ t, HasDerivAt γ h t := by
    intro t
    rw [hγγ]
    have h1 : HasDerivAt (fun t : ℝ => t • h) ((1 : ℝ) • h) t := (hasDerivAt_id t).smul_const h
    exact (h1.const_add c).congr_deriv (by simp)
  have hγmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ D := fun t ht => hconv x hx t ht
  -- `deriv G t = Σ_i h_i ∂_i f (γ t)`
  have hG1 : ∀ t, γ t ∈ D → HasDerivAt G (∑ i, h i * partial1 i f (γ t)) t := by
    intro t hmem
    have hfD : DifferentiableAt ℝ f (γ t) :=
      (hC1 (γ t) hmem).differentiableAt (n := (1 : ℕ∞)) one_ne_zero
    have hG' : HasDerivAt G (fderiv ℝ f (γ t) h) t :=
      hfD.hasFDerivAt.comp_hasDerivAt t (hγderiv t)
    have hexp : fderiv ℝ f (γ t) h = ∑ i, h i * partial1 i f (γ t) :=
      clm_apply_eq_sum_coord (fderiv ℝ f (γ t)) h
    simpa [hexp] using hG'
  -- continuity on the closed segment
  have hfcont : ContinuousOn f D :=
    fun y hy => (hC1 y hy).continuousAt.continuousWithinAt
  have hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1) := by
    rw [hγγ]
    exact continuousOn_const.add (continuousOn_id.smul continuousOn_const)
  have hGcont : ContinuousOn G (Set.Icc (0 : ℝ) 1) := hfcont.comp hγcont hγmem
  -- the one-dimensional step: Lagrange's mean value theorem
  obtain ⟨t₀, ht₀, hslope⟩ :=
    exists_hasDerivAt_eq_slope (a := (0 : ℝ)) (b := 1) G
      (fun t => ∑ i, h i * partial1 i f (γ t)) (by norm_num) hGcont
      (fun t ht => hG1 t (hγmem t (Set.Ioo_subset_Icc_self ht)))
  rw [sub_zero, div_one] at hslope
  have hG0val : G 0 = f c := by simp only [hG, hγ0]
  have hG1val : G 1 = f x := by simp only [hG, hγ1]
  have ht₀D : γ t₀ ∈ D := hγmem t₀ (Set.Ioo_subset_Icc_self ht₀)
  have hMVT : f x - f c = ∑ i, h i * partial1 i f (γ t₀) := by
    rw [← hG1val, ← hG0val]
    exact hslope.symm
  -- the linear bound
  have hlin : ∑ i, h i * partial1 i f (γ t₀) ≤ ∑ i, w i * g i := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : h i * partial1 i f (γ t₀) ≤ |h i * partial1 i f (γ t₀)| := le_abs_self _
    have h2 : |h i * partial1 i f (γ t₀)| = |h i| * |partial1 i f (γ t₀)| := abs_mul _ _
    have h3 : |h i| ≤ w i := by rw [hhi i]; exact hw x hx i
    have h4 : |partial1 i f (γ t₀)| ≤ g i := hg (γ t₀) ht₀D i
    have hw0 : 0 ≤ w i := le_trans (abs_nonneg _) h3
    calc h i * partial1 i f (γ t₀) ≤ |h i| * |partial1 i f (γ t₀)| := by rw [← h2]; exact h1
      _ ≤ w i * g i := mul_le_mul h3 h4 (abs_nonneg _) hw0
  linarith

#print axioms taylor2_upper

/-- **One-sided first-order Taylor lower bound** — `taylor2_upper` applied to
`-f` (the shape `w1F3Z_pos_of_slack2`'s linear part consumes). -/
theorem taylor2_lower {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    {c : Fin 3 → ℝ} {w : Fin 3 → ℝ} {fc : ℝ} {g : Fin 3 → ℝ}
    (hc : c ∈ D)
    (hconv : ∀ x ∈ D, ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun i => c i + t * (x i - c i)) ∈ D)
    (hC1 : ∀ x ∈ D, ContDiffAt ℝ 1 f x)
    (hw : ∀ x ∈ D, ∀ i, |x i - c i| ≤ w i)
    (hval : fc ≤ f c)
    (hg : ∀ x ∈ D, ∀ i, |partial1 i f x| ≤ g i) :
    ∀ x ∈ D, fc - ∑ i, w i * g i ≤ f x := by
  have hC1' : ∀ x ∈ D, ContDiffAt ℝ 1 (fun y => -f y) x := fun x hx => (hC1 x hx).neg
  have hg' : ∀ x ∈ D, ∀ i, |partial1 i (fun y => -f y) x| ≤ g i := by
    intro x hx i
    rw [partial1_neg, abs_neg]
    exact hg x hx i
  have h := taylor2_upper (f := fun y => -f y) (D := D) (c := c) (w := w)
    (fc := -fc) (g := g) hc hconv hC1' hw (by linarith) hg'
  intro x hx
  have := h x hx
  linarith

#print axioms taylor2_lower

namespace DCMatan

open DCKit

/-- **Outward dyadic absolute value.**  For `a ∈ A`, `|a| ∈ dAbs A`: the upper
end is `max (-lo) hi` (HOL's `iabs`), the lower end is the exact range lower
bound (`lo` if the interval is positive, `-hi` if negative, `0` if it straddles
zero). -/
def dAbs (A : DC) : DC :=
  DC.mk A.k (max (if 0 < A.lo then A.lo else -A.hi) 0) (max (-A.lo) A.hi)

theorem dAbs_mem {A : DC} {a : ℝ} (h : A.mem a) : (dAbs A).mem |a| := by
  obtain ⟨hlo, hhi⟩ := h
  have hs : (0 : ℝ) < (2 : ℝ) ^ (-(A.k : ℤ)) := mem_zero_pow A.k
  -- the upper end: `iabs`
  have hup : ((max (-A.lo) A.hi : ℤ) : ℝ) = max (-(A.lo : ℝ)) (A.hi : ℝ) := by
    push_cast
    rfl
  have hMa : a ≤ ((max (-A.lo) A.hi : ℤ) : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ)) := by
    rw [hup]
    have h2 : (A.hi : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ)) ≤
        max (-(A.lo : ℝ)) (A.hi : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hs.le
    linarith
  have hM1 : -(((max (-A.lo) A.hi : ℤ) : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ))) ≤ a := by
    rw [hup]
    have hle : -max (-(A.lo : ℝ)) (A.hi : ℝ) ≤ (A.lo : ℝ) := by
      linarith [le_max_left (-(A.lo : ℝ)) (A.hi : ℝ)]
    have hmul : -max (-(A.lo : ℝ)) (A.hi : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ)) ≤
        (A.lo : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ)) :=
      mul_le_mul_of_nonneg_right hle hs.le
    linarith
  refine ⟨?_, ?_⟩
  · -- the lower end
    by_cases hpos : 0 < A.lo
    · have hif : (if 0 < A.lo then A.lo else -A.hi) = A.lo := if_pos hpos
      have hmax : (max A.lo 0 : ℤ) = A.lo := max_eq_left hpos.le
      rw [dAbs, hif, hmax]
      have hlr : (0 : ℝ) < (A.lo : ℝ) := by exact_mod_cast hpos
      have hspos : (0 : ℝ) < (A.lo : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ)) := mul_pos hlr hs
      have hapos : (0 : ℝ) ≤ a := le_trans hspos.le hlo
      rw [abs_of_nonneg hapos]
      exact hlo
    · have hif : (if 0 < A.lo then A.lo else -A.hi) = -A.hi := if_neg hpos
      have hlo0 : A.lo ≤ 0 := le_of_not_gt hpos
      by_cases hneg : A.hi < 0
      · have hmax : (max (-A.hi) 0 : ℤ) = -A.hi := max_eq_left (by omega)
        rw [dAbs, hif, hmax]
        have hhr : (A.hi : ℝ) < 0 := by exact_mod_cast hneg
        have hspos : (A.hi : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ)) < 0 :=
          mul_neg_of_neg_of_pos hhr hs
        have haneg : a < 0 := lt_of_le_of_lt hhi hspos
        rw [abs_of_neg haneg]
        have : ((-A.hi : ℤ) : ℝ) = -(A.hi : ℝ) := by push_cast; ring
        rw [this]
        linarith
      · have hmax : (max (-A.hi) 0 : ℤ) = 0 := max_eq_right (by omega)
        rw [dAbs, hif, hmax]
        push_cast
        rw [zero_mul]
        exact abs_nonneg a
  · change |a| ≤ ((max (-A.lo) A.hi : ℤ) : ℝ) * (2 : ℝ) ^ (-(A.k : ℤ))
    exact abs_le.mpr ⟨hM1, hMa⟩

#print axioms dAbs_mem

/-- **The DC T2 terminal.**  `V` brackets the centre value, `G i` bracket the
**box-wide** coordinate partials (the T2 quantity
`fc − Σ_i w_i sup_box|∂_i f|` of `scripts/coverage.py`), and the slack
`V.lo·2^-V.k − Σ_i w_i · (dAbs (G i)).hi·2^-(G i).k` is positive; then `f > 0`
on the whole box.  This is `w1F3Z_pos_of_slack2` with the Hessian term dropped
(`refine_t2.py`'s `T2`). -/
theorem dcT2_pos {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)} {c w : Fin 3 → ℝ}
    (hc : c ∈ D)
    (hconv : ∀ x ∈ D, ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun i => c i + t * (x i - c i)) ∈ D)
    (hC1 : ∀ x ∈ D, ContDiffAt ℝ 1 f x)
    (hw : ∀ x ∈ D, ∀ i, |x i - c i| ≤ w i)
    (V : DC) (G : Fin 3 → DC)
    (hV : V.mem (f c)) (hG : ∀ x ∈ D, ∀ i, (G i).mem (partial1 i f x))
    (hslack : 0 < (V.lo : ℝ) * (2 : ℝ) ^ (-(V.k : ℤ)) -
      (w 0 * (((dAbs (G 0)).hi : ℝ) * (2 : ℝ) ^ (-((G 0).k : ℤ))) +
       w 1 * (((dAbs (G 1)).hi : ℝ) * (2 : ℝ) ^ (-((G 1).k : ℤ))) +
       w 2 * (((dAbs (G 2)).hi : ℝ) * (2 : ℝ) ^ (-((G 2).k : ℤ))))) :
    ∀ x ∈ D, 0 < f x := by
  have hval : (V.lo : ℝ) * (2 : ℝ) ^ (-(V.k : ℤ)) ≤ f c := hV.1
  have hg : ∀ x ∈ D, ∀ i, |partial1 i f x| ≤
      ((dAbs (G i)).hi : ℝ) * (2 : ℝ) ^ (-((G i).k : ℤ)) := fun x hx i =>
    (dAbs_mem (hG x hx i)).2
  intro x hx
  have h := taylor2_lower (f := f) (D := D) (c := c) (w := w)
    (fc := (V.lo : ℝ) * (2 : ℝ) ^ (-(V.k : ℤ)))
    (g := fun i => ((dAbs (G i)).hi : ℝ) * (2 : ℝ) ^ (-((G i).k : ℤ)))
    hc hconv hC1 hw hval hg x hx
  rw [Fin.sum_univ_three] at h
  linarith

#print axioms dcT2_pos

end DCMatan

end Kepler.Text.TaylorSecond
