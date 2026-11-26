/-
Kepler.Text.TaylorSecond.Taylor3 — lane `wt1-taylor-probe-w1` (2026-11-25).

The generic **three-variable, one-sided, second-order Taylor upper bound** — the
Lean counterpart of the upper half of HOL's `m_taylor_bounds`
(`reference/flyspeck/formal_ineqs/taylor/theory/multivariate_taylor-compiled.hl:1529`,
with `m_cell_domain` :1349, `m_lin_approx` :22, `second_bounded` :3004,
`m_taylor_error` :936).

Shape (see `TAYLOR_MODEL_SPEC.md` §1.1 of lane `wt1-taylor-model-w1`):

    f x ≤ f c + Σ_i w_i g_i + (1/2) Σ_i Σ_j w_i w_j e_ij      for x in the box D

from the centre value, the centre gradient, and a whole-box Hessian enclosure.
No multivariate Taylor series is needed: apply the one-dimensional Lagrange
remainder (`taylor_mean_remainder_lagrange`) to `G(t) = f (c + t • (x - c))` on
`[0,1]`, whose second derivative is the quadratic form of the coordinate
Hessian at an interior point.  The Lagrange form is what produces the `1/2`
(coinciding with HOL's `dd_bound / 2`); `taylor_mean_remainder_bound` has
`(x-a)^(n+1)/n!` and would lose the factor two, which the calibration box
`15868/LLRLR` cannot afford (margin `+1.033e-3` becomes `-5.633e-4`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Order.Interval.Set.UnorderedInterval

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Filter
open scoped Topology

/-- A continuous linear functional on `Fin 3 → ℝ` is the sum of its coordinate
values: `L h = Σ_i h i * L (coord i)`. -/
theorem clm_apply_eq_sum_coord (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (h : Fin 3 → ℝ) :
    L h = ∑ i, h i * L (coord i) := by
  have hdecomp : h = ∑ i, h i • coord i := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, coord, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hjb : ¬ (j = b) := fun hj => hb hj.symm
      simp only [hjb, if_false, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  conv_lhs => rw [hdecomp]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

/-- **One-sided second-order Taylor upper bound in three variables.**

`e i j` is an absolute bound for `∂²_ij f = partial2 j i f` on the whole box
`D`; a lower-triangular family together with `partial2_comm` is enough at the
call site. -/
theorem taylor3_upper {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    {c : Fin 3 → ℝ} {w : Fin 3 → ℝ} {fc : ℝ} {g : Fin 3 → ℝ}
    {e : Fin 3 → Fin 3 → ℝ}
    (hc : c ∈ D)
    (hconv : ∀ x ∈ D, ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun i => c i + t * (x i - c i)) ∈ D)
    (hC2 : ∀ x ∈ D, ContDiffAt ℝ 2 f x)
    (hw : ∀ x ∈ D, ∀ i, |x i - c i| ≤ w i)
    (hval : f c ≤ fc)
    (hg : ∀ i, |partial1 i f c| ≤ g i)
    (he : ∀ x ∈ D, ∀ i j, |partial2 j i f x| ≤ e i j) :
    ∀ x ∈ D, f x ≤ fc + ∑ i, w i * g i + (1 / 2) * ∑ i, ∑ j, w i * w j * e i j := by
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
  -- affine images of points of `D` stay in `D`
  have hγmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ D := fun t ht => hconv x hx t ht
  -- `G` is `C²` on `[0,1]`
  have hG2 : ContDiffOn ℝ 2 G (Set.Icc (0 : ℝ) 1) := by
    have hf2 : ContDiffOn ℝ 2 f D := fun y hy => (hC2 y hy).contDiffWithinAt
    have hγ2 : ContDiffOn ℝ 2 γ (Set.Icc (0 : ℝ) 1) := by
      rw [hγγ]
      exact contDiffOn_const.add (contDiffOn_id.smul contDiffOn_const)
    exact hf2.comp hγ2 hγmem
  -- `deriv G t = Σ_i h_i ∂_i f (γ t)`
  have hG1 : ∀ t, γ t ∈ D → HasDerivAt G (∑ i, h i * partial1 i f (γ t)) t := by
    intro t hmem
    have hfD : DifferentiableAt ℝ f (γ t) := (hC2 (γ t) hmem).differentiableAt (by norm_num)
    have hG' : HasDerivAt G (fderiv ℝ f (γ t) h) t :=
      hfD.hasFDerivAt.comp_hasDerivAt t (hγderiv t)
    have hexp : fderiv ℝ f (γ t) h = ∑ i, h i * partial1 i f (γ t) :=
      clm_apply_eq_sum_coord (fderiv ℝ f (γ t)) h
    simpa [hexp] using hG'
  -- the one-dimensional Taylor step
  have hG1c : ContDiffOn ℝ 1 G (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact hG2.of_le (by norm_num)
  have hGd : DifferentiableOn ℝ (iteratedDerivWithin 1 G (Set.uIcc (0 : ℝ) 1))
      (Set.uIoo (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have h := hG2.differentiableOn_iteratedDerivWithin (m := 1)
      (by norm_num) (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    exact h.mono Set.Ioo_subset_Icc_self
  obtain ⟨ξ, hξ, hLag⟩ :=
    taylor_mean_remainder_lagrange (f := G) (x := 1) (x₀ := 0) (n := 1)
      (by norm_num) hG1c hGd
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hLag
  have hξmem : ξ ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hξ
    exact hξ
  -- the derivative within the closed segment at the left endpoint is the
  -- two-sided derivative (`Icc 0 1` and `Ici 0` agree on a punctured
  -- neighbourhood of `0`)
  have hset : Set.Icc (0 : ℝ) 1 =ᶠ[𝓝[{(0 : ℝ)}ᶜ] 0] Set.Ici 0 := by
    have hmem : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (by norm_num)
    have hmem' : Set.Iio (1 : ℝ) ∈ 𝓝[{(0 : ℝ)}ᶜ] (0 : ℝ) := nhdsWithin_le_nhds hmem
    filter_upwards [hmem'] with y hy
    have hiff : y ∈ Set.Icc (0:ℝ) 1 ↔ y ∈ Set.Ici (0:ℝ) :=
      ⟨fun h => h.1, fun h => ⟨h, le_of_lt (Set.mem_Iio.mp hy)⟩⟩
    -- 4.32: goal is `Set.Icc 0 1 y = Set.Ici 0 y`; 4.36: goal is the `↔` form.
    first | exact hiff | exact propext hiff
  have hd0 : deriv G 0 = ∑ i, h i * partial1 i f c := by
    have h := (hG1 0 (by rw [hγ0]; exact hc)).deriv
    rw [hγ0] at h
    exact h
  have hdw : derivWithin G (Set.Icc (0 : ℝ) 1) 0 = deriv G 0 := by
    rw [derivWithin_congr_set' 0 hset]
    have h := ((hG1 0 (by rw [hγ0]; exact hc)).hasDerivWithinAt).derivWithin
      (uniqueDiffWithinAt_Ici 0)
    rw [hγ0] at h
    exact h.trans hd0.symm
  have htw : taylorWithinEval G 1 (Set.Icc (0 : ℝ) 1) 0 1 = G 0 + deriv G 0 := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval]
    have h1 : iteratedDerivWithin (0 + 1) G (Set.Icc (0 : ℝ) 1) 0 = deriv G 0 := by
      rw [iteratedDerivWithin_one, hdw]
    rw [h1]
    norm_num
  -- the second derivative at the interior point `ξ` is that of `G`
  have hξcont : ∀ᶠ t in 𝓝 ξ, ContDiffAt ℝ 2 G t := by
    filter_upwards [isOpen_Ioo.mem_nhds hξmem] with t ht
    exact (hC2 (γ t) (hγmem t (Set.Ioo_subset_Icc_self ht))).comp t (by
      rw [hγγ]
      fun_prop)
  have hsec : iteratedDerivWithin 2 G (Set.Icc (0 : ℝ) 1) ξ = deriv (deriv G) ξ := by
    have hs : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
    rw [iteratedDerivWithin_eq_iteratedDeriv hs
      ((hξcont.self_of_nhds))
      (Set.Ioo_subset_Icc_self hξmem)]
    rw [iteratedDeriv_eq_iterate]
    rfl
  -- assemble `G 1 = G 0 + deriv G 0 + deriv (deriv G) ξ / 2`
  have hTaylor : G 1 = G 0 + deriv G 0 + deriv (deriv G) ξ / 2 := by
    rw [htw, hsec] at hLag
    norm_num at hLag
    linarith
  -- the second derivative of `G` as the quadratic form of the coordinate Hessian
  have hd2 : deriv (deriv G) ξ = ∑ i, ∑ j, h i * h j * partial2 j i f (γ ξ) := by
    have hev : deriv G =ᶠ[𝓝 ξ] fun t => ∑ i, h i * partial1 i f (γ t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hξmem] with t ht
      exact (hG1 t (hγmem t (Set.Ioo_subset_Icc_self ht))).deriv
    rw [hev.deriv_eq]
    have hmem : γ ξ ∈ D := hγmem ξ (Set.Ioo_subset_Icc_self hξmem)
    have hstep : ∀ i, HasDerivAt (fun t => h i * partial1 i f (γ t))
        (h i * ∑ j, h j * partial2 j i f (γ ξ)) ξ := by
      intro i
      have hfD : DifferentiableAt ℝ (fun y => partial1 i f y) (γ ξ) :=
        differentiableAt_partial1 (hC2 (γ ξ) hmem) i
      have hd : HasDerivAt (fun t => partial1 i f (γ t))
          (fderiv ℝ (fun y => partial1 i f y) (γ ξ) h) ξ :=
        hfD.hasFDerivAt.comp_hasDerivAt ξ (hγderiv ξ)
      have hexp : fderiv ℝ (fun y => partial1 i f y) (γ ξ) h
          = ∑ j, h j * partial2 j i f (γ ξ) :=
        clm_apply_eq_sum_coord (fderiv ℝ (fun y => partial1 i f y) (γ ξ)) h
      rw [hexp] at hd
      exact hd.const_mul (h i)
    have hfun : (fun t => ∑ i, h i * partial1 i f (γ t))
        = ∑ i, (fun t => h i * partial1 i f (γ t)) := by
      funext t
      simp [Finset.sum_apply]
    have hsum : HasDerivAt (∑ i, (fun t => h i * partial1 i f (γ t)))
        (∑ i, h i * ∑ j, h j * partial2 j i f (γ ξ)) ξ :=
      HasDerivAt.sum (u := Finset.univ) (fun i _ => hstep i)
    rw [hfun, hsum.deriv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hG0val : G 0 = f c := by simp only [hG, hγ0]
  have hG1val : G 1 = f x := by simp only [hG, hγ1]
  -- final arithmetic
  have hlin : ∑ i, h i * partial1 i f c ≤ ∑ i, w i * g i := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : h i * partial1 i f c ≤ |h i * partial1 i f c| := le_abs_self _
    have h2 : |h i * partial1 i f c| = |h i| * |partial1 i f c| := abs_mul _ _
    have h3 : |h i| ≤ w i := by rw [hhi i]; exact hw x hx i
    have h4 : |partial1 i f c| ≤ g i := hg i
    have hw0 : 0 ≤ w i := le_trans (abs_nonneg _) h3
    calc h i * partial1 i f c ≤ |h i| * |partial1 i f c| := by rw [← h2]; exact h1
      _ ≤ w i * g i := mul_le_mul h3 h4 (abs_nonneg _) hw0
  have hquad : ∑ i, ∑ j, h i * h j * partial2 j i f (γ ξ)
      ≤ ∑ i, ∑ j, w i * w j * e i j := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h1 : h i * h j * partial2 j i f (γ ξ) ≤ |h i * h j * partial2 j i f (γ ξ)| :=
      le_abs_self _
    have h2 : |h i * h j * partial2 j i f (γ ξ)|
        = |h i| * |h j| * |partial2 j i f (γ ξ)| := by
      rw [abs_mul, abs_mul]
    have h3 : |h i| ≤ w i := by rw [hhi i]; exact hw x hx i
    have h4 : |h j| ≤ w j := by rw [hhi j]; exact hw x hx j
    have h5 : |partial2 j i f (γ ξ)| ≤ e i j :=
      he (γ ξ) (hγmem ξ (Set.Ioo_subset_Icc_self hξmem)) i j
    have hw0 : 0 ≤ w i := le_trans (abs_nonneg _) h3
    have hw0' : 0 ≤ w j := le_trans (abs_nonneg _) h4
    calc h i * h j * partial2 j i f (γ ξ)
        ≤ |h i| * |h j| * |partial2 j i f (γ ξ)| := by rw [← h2]; exact h1
      _ ≤ w i * w j * e i j := by
        exact mul_le_mul (mul_le_mul h3 h4 (abs_nonneg _) hw0) h5 (abs_nonneg _)
          (mul_nonneg hw0 hw0')
  calc f x = G 1 := hG1val.symm
    _ = f c + (∑ i, h i * partial1 i f c)
          + (1 / 2) * ∑ i, ∑ j, h i * h j * partial2 j i f (γ ξ) := by
        rw [hTaylor, hG0val, hd0, hd2]
        ring
    _ ≤ fc + ∑ i, w i * g i + (1 / 2) * ∑ i, ∑ j, w i * w j * e i j := by
        nlinarith [hval, hlin, hquad]

#print axioms clm_apply_eq_sum_coord
#print axioms taylor3_upper

/-- Coordinate partials commute with negation. -/
theorem partial1_neg (i : Fin 3) (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    partial1 i (fun y => -f y) x = -partial1 i f x := by
  unfold partial1
  rw [fderiv_fun_neg]
  rfl

/-- Mixed coordinate second partials commute with negation. -/
theorem partial2_neg (j i : Fin 3) (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    partial2 j i (fun y => -f y) x = -partial2 j i f x := by
  unfold partial2
  have hfun : (fun y => partial1 i (fun y' => -f y') y) = fun y => -partial1 i f y := by
    funext y
    exact partial1_neg i f y
  rw [hfun, fderiv_fun_neg]
  rfl

/-- **One-sided second-order Taylor lower bound** — the lower half of HOL
`m_taylor_bounds` (`multivariate_taylor-compiled.hl:1529`), obtained from
`taylor3_upper` applied to `-f`. -/
theorem taylor3_lower {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    {c : Fin 3 → ℝ} {w : Fin 3 → ℝ} {fc : ℝ} {g : Fin 3 → ℝ}
    {e : Fin 3 → Fin 3 → ℝ}
    (hc : c ∈ D)
    (hconv : ∀ x ∈ D, ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun i => c i + t * (x i - c i)) ∈ D)
    (hC2 : ∀ x ∈ D, ContDiffAt ℝ 2 f x)
    (hw : ∀ x ∈ D, ∀ i, |x i - c i| ≤ w i)
    (hval : fc ≤ f c)
    (hg : ∀ i, |partial1 i f c| ≤ g i)
    (he : ∀ x ∈ D, ∀ i j, |partial2 j i f x| ≤ e i j) :
    ∀ x ∈ D, fc - (∑ i, w i * g i + (1 / 2) * ∑ i, ∑ j, w i * w j * e i j) ≤ f x := by
  have hC2' : ∀ x ∈ D, ContDiffAt ℝ 2 (fun y => -f y) x := fun x hx => (hC2 x hx).neg
  have hg' : ∀ i, |partial1 i (fun y => -f y) c| ≤ g i := by
    intro i
    rw [partial1_neg, abs_neg]
    exact hg i
  have he' : ∀ x ∈ D, ∀ i j, |partial2 j i (fun y => -f y) x| ≤ e i j := by
    intro x hx i j
    rw [partial2_neg, abs_neg]
    exact he x hx i j
  have h := taylor3_upper (f := fun y => -f y) (D := D) (c := c) (w := w)
    (fc := -fc) (g := g) (e := e) hc hconv hC2' hw (by linarith) hg' he'
  intro x hx
  have := h x hx
  linarith

#print axioms partial1_neg
#print axioms taylor3_lower

end Kepler.Text.TaylorSecond
