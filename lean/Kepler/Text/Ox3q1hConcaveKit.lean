/-
Ox3q1hConcaveKit: the HasDerivAt2->rebate bridge for the ox3q1h corner
tables (lane `ox3q1h-nogate-w1`).

Given a slice function `f` along an axis with
* global first-derivative differentiability (`Differentiable ℝ f`),
* a `HasDerivAt` computation of `deriv f` with explicit value `F t` on
  the axis interior (the second-derivative formula, supplied by the
  tree's `Gamma4Concave`/`Gamma4Deriv*` layer per slot),
* an upper bound `F t <= K` on the axis interior,

this kit produces the shifted-concavity hypothesis
`ConcaveOn ℝ (Icc (lo i) (hi i)) (fun t => f (update y i t) - K i/2*t*t)`
consumed by `Ox3q1hSliceRebate.slice_hper`, and hence the full per-slice
`hper` premise of `Ox3q1hRebate.descend_step_le`.

Numeric `K` values (dyadic, outward) live in the data layer
(`corner184/KENV.tsv`); no numerics here.
-/
import Mathlib
import Kepler.Text.Ox3q1hSliceRebate

open Set Filter Topology

namespace Kepler.Text

/-- Bridge: if `f` is differentiable, `deriv f` carries a `HasDerivAt`
computation with value `F t` on the open interval, and `F t <= K` there,
then `f - K/2·(·)²` is concave on `[a, b]` (the shifted-concavity
hypothesis of `rebate_of_concave_shifted`). -/
theorem concave_shifted_of_deriv2_le {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    {K : ℝ} (hf' : Differentiable ℝ f)
    (hd2 : ∀ t ∈ Set.Ioo a b, HasDerivAt (deriv f) (F t) t)
    (hbnd : ∀ t ∈ Set.Ioo a b, F t ≤ K) :
    ConcaveOn ℝ (Set.Icc a b) (fun t => f t - K / 2 * t * t) := by
  have hdiffq : Differentiable ℝ (fun t => (K / 2) * t * t) :=
    ((differentiable_const (K / 2)).mul differentiable_id).mul differentiable_id
  have hshift : Differentiable ℝ (fun t => f t - (K / 2) * t * t) :=
    hf'.sub hdiffq
  have hfn : deriv f - (fun s : ℝ => K * s)
      = (fun s : ℝ => deriv f s - K * s) := by
    funext s
    simp [Pi.sub_apply]
  -- derivative of the quadratic term: K * t
  have hKq : ∀ t : ℝ, deriv (fun t => K / 2 * t * t) t = K * t := by
    intro t
    have hc : HasDerivAt (fun x => K / 2 * x) ((K / 2) * 1) t :=
      HasDerivAt.const_mul (K / 2) (hasDerivAt_id t)
    have h := hc.mul (hasDerivAt_id t)
    rw [show (fun x => K / 2 * x) * id = fun x => K / 2 * x * x from rfl] at h
    rw [mul_one, mul_one] at h
    exact h.deriv.trans (by simp only [id_eq]; ring)
  have hdeq : ∀ t ∈ Set.Ioo a b,
      (deriv (fun t => f t - (K / 2) * t * t)) t = deriv f t - K * t := by
    intro t ht
    rw [deriv_fun_sub hf'.differentiableAt hdiffq.differentiableAt,
      hKq t]
  have h1 : DifferentiableOn ℝ (fun t => f t - (K / 2) * t * t)
      (Set.Ioo a b) :=
    hshift.differentiableOn
  have h2 : DifferentiableOn ℝ (deriv (fun t => f t - (K / 2) * t * t))
      (Set.Ioo a b) := by
    intro t ht
    have hKst : HasDerivAt (fun s => K * s) K t := by
      have h := (hasDerivAt_id t).const_mul K
      rw [mul_one] at h
      exact h
    have heq2 : (deriv (fun s => f s - (K / 2) * s * s)) =ᶠ[𝓝[Set.Ioo a b] t]
        (fun s => deriv f s - K * s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hdeq s hs
    have hsub : HasDerivAt (deriv f - fun s => K * s) (F t - K) t :=
      (hd2 t ht).sub hKst
    have hw := HasDerivAt.hasDerivWithinAt (s := Set.Ioo a b) hsub
    exact HasDerivWithinAt.differentiableWithinAt
      (hw.congr_of_eventuallyEq_of_mem heq2 ht)
  have h3 : ∀ t ∈ Set.Ioo a b,
      deriv^[2] (fun t => f t - (K / 2) * t * t) t ≤ 0 := by
    intro t ht
    have hKst : HasDerivAt (fun s => K * s) K t := by
      have h := (hasDerivAt_id t).const_mul K
      rw [mul_one] at h
      exact h
    have heqN : (deriv (fun s => f s - (K / 2) * s * s)) =ᶠ[𝓝 t]
        (fun s => deriv f s - K * s) :=
      Filter.Eventually.mono (isOpen_Ioo.mem_nhds ht) fun s hs => hdeq s hs
    show deriv (deriv (fun t => f t - (K / 2) * t * t)) t ≤ 0
    rw [Filter.EventuallyEq.deriv_eq heqN, deriv_fun_sub (hd2 t ht).differentiableAt
      hKst.differentiableAt, (hd2 t ht).deriv, hKst.deriv]
    linarith [hbnd t ht]
  have hint : Set.Ioo a b = interior (Set.Icc a b) := interior_Icc.symm
  refine concaveOn_of_deriv2_nonpos (convex_Icc _ _)
    hshift.differentiableOn.continuousOn ?_ ?_ ?_
  · rw [← hint]; exact h1
  · rw [← hint]; exact h2
  · rw [← hint]; exact h3

/-- Slot-lift: for coordinate `i`, shifted-concavity certificates of all
`i`-axis slices of `f` over the outward box, produced from a
`HasDerivAt` computation of the slice derivative with value `F y t` and
the uniform bound `F y t <= K i`. -/
theorem slice_shifted_concave_of_deriv2 {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {lo hi K : Fin n → ℝ} {i : Fin n} (hlohi : lo i ≤ hi i)
    (F : (Fin n → ℝ) → ℝ → ℝ)
    (hf' : ∀ y : Fin n → ℝ, Differentiable ℝ
      (fun t => f (Function.update y i t)))
    (hd2 : ∀ y : Fin n → ℝ, ∀ t ∈ Set.Icc (lo i) (hi i),
      HasDerivAt (deriv (fun t => f (Function.update y i t))) (F y t) t)
    (hbnd : ∀ y : Fin n → ℝ, ∀ t ∈ Set.Icc (lo i) (hi i), F y t ≤ K i) :
    ∀ y : Fin n → ℝ, ConcaveOn ℝ (Set.Icc (lo i) (hi i))
      (fun t => f (Function.update y i t) - K i / 2 * t * t) :=
  fun y =>
    concave_shifted_of_deriv2_le hlohi (hf' y)
      (fun t ht => hd2 y t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
      (fun t ht => hbnd y t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

/-- Full `hper`-premise production for coordinate `i` from a
`HasDerivAt2` layer with bound `K i`: this is exactly the per-slice
premise consumed by `Ox3q1hRebate.descend_step_le` /
`Ox3q1hSliceRebate.exists_vertex_rebate_of_shifted_concave`. -/
theorem slice_hper_of_deriv2 {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {lo hi K : Fin n → ℝ} {i : Fin n} (hK : 0 ≤ K i) (hlohi : lo i ≤ hi i)
    (F : (Fin n → ℝ) → ℝ → ℝ)
    (hf' : ∀ y : Fin n → ℝ, Differentiable ℝ
      (fun t => f (Function.update y i t)))
    (hd2 : ∀ y : Fin n → ℝ, ∀ t ∈ Set.Icc (lo i) (hi i),
      HasDerivAt (deriv (fun t => f (Function.update y i t))) (F y t) t)
    (hbnd : ∀ y : Fin n → ℝ, ∀ t ∈ Set.Icc (lo i) (hi i), F y t ≤ K i)
    (y : Fin n → ℝ) :
    ∀ t ∈ Set.Icc (lo i) (hi i),
      f (Function.update y i t) ≥
        min (f (Function.update y i (lo i)))
          (f (Function.update y i (hi i)))
        - K i * (hi i - lo i) ^ 2 / 8 :=
  slice_hper hK hlohi (slice_shifted_concave_of_deriv2 hlohi F hf' hd2 hbnd) y

/-! ### Axiom audit -/

#print axioms concave_shifted_of_deriv2_le
#print axioms slice_shifted_concave_of_deriv2
#print axioms slice_hper_of_deriv2

end Kepler.Text
