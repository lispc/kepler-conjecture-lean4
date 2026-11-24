/-
Kepler.Text.TaylorSecond.MatanNegKit — lane `wt1-matan-negkit-w1` (2026-11-24),
wt1 gap **G3**: the `matan` negative-branch (`t ∈ (-1, 0]`) interval bracket kit.

`matan` (IneqClosureDefs, HOL sphere.hl:728-731) is `arctan(√t)/√t` for `t > 0`
but `log((1+√-t)/(1-√-t)) / (2·√-t)` for `t < 0` — the artanh branch.  Mathlib
has no atanh series brackets and the landed `NliBanks12` only carries order-3
artanh brackets on `|t| ≤ 1/4`; the wt1 Route B negative leaves (255 crossing
zero / 204 fully negative out of 6,989 certified leaves) need the generator-
consumable exact-rational brackets assembled here.

Content.
* §0 `HasDerivAt Real.artanh (1/(1-x²)) x` (via `artanh_eq_half_log` and the
  landed log-form derivative `nb12_hasDerivAt_artanh`) and the order-5 artanh
  partial sum `lkB5 = u + u³/3 + u⁵/5 + u⁷/7 + u⁹/9` with its derivative.
* §1 the two series-gap bounds, both by `monotoneOn_of_deriv_nonneg`:
  - lower: `lkB5 u ≤ artanh u` for `0 ≤ u < 1` (gap derivative `u^10/(1-u²)`);
  - upper: `artanh u ≤ lkB5 u + u·(uh^10/(1-uh²))` for `0 ≤ u ≤ uh < 1`
    (gap derivative ≤ 0 by the factorwise tail comparison `u^10/(1-u²) ≤
    uh^10/(1-uh²)`), with corollary `artanh u ≤ u/(1-u²)`.
* §2 the negative-branch identity `matan (-(u²)) = artanh u / u` and
  monotonicity of `g u = artanh u / u` on `(0,1)` (derivative
  `(u/(1-u²) - artanh u)/u² ≥ 0` via the corollary).
* §3 generator-facing point enclosure `lkB_matan_neg_pt`: for rational
  `-1 < tI < 0` and rational sqrt brackets `ql² ≤ -tI ≤ qh²`, `0 < ql ≤ qh < 1`
  (the brackets themselves come from the landed InvSqrt/√ base), with exact
  rational endpoints
    `matan tI ∈ [lkB5r ql / ql, lkB5r qh / qh + qh^10 / (1 - qh ^ 2)]`.
  Numerical audit (lane scripts/probe_recipe.py, exact Fraction + mpmath
  200dps): both directions hold at every sampled point; the N=5 bracket width
  is ≪ 1e-6 for `u = √(-tI) ≲ 0.2` and ≈ 1.0e-6 at `u = 0.25` — for larger `u`
  the generator must re-emit this file with a larger N (same proof skeletons;
  `docs/pitfall-register.md` PR-32: regenerate, never regex-patch).
* §4 transports: the branch-agnostic strict-antitone slot transport
  (`nb12w_matan_strictAntiOn` covers all of `(-1, ∞)`, so the **same** lemma
  is the negative-slot assembly and the cross-zero composition — endpoint
  enclosures may come from different branches); negative slot wrapper;
  `matan 0 = 1` for the zero slot point.
* §5 negative-branch `matanD` interval ops (same expression as the landed
  positive-branch ops, reciprocal signs flipped: `1+TI > 0`, `2·TI < 0`), the
  branch-agnostic `matanDD` point enclosure (`tI ≠ 0`), and a sound
  factor-interval `matanDD` slot enclosure for negative slots (through
  `e(t) = 1/(1+t) - matan t`; `3/(4t²)` is antitone in `t²`, and
  `1/(2t(1+t)²)` is enclosed by the all-corners product of the factor
  intervals `2·TI` and `(1+TI)⁻¹` — no monotonicity assumption on `matanDD`
  over the negative branch is used anywhere).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.QInterval
import Kepler.Text.Wt1TowerKit
import Mathlib.Analysis.SpecialFunctions.Artanh

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Kepler.Text
open Kepler.NliBanks12

/-! ## 0. `artanh` derivative and the order-5 partial sum -/

/-- `HasDerivAt Real.artanh (1/(1-x²)) x` on `(-1, 1)`: bridge the landed
log-form derivative (`nb12_hasDerivAt_artanh`) to `Real.artanh` through
`artanh_eq_half_log`. -/
theorem lkB_hasDerivAt_artanh {x : ℝ} (h1 : x < 1) (hm1 : -1 < x) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have hd := nb12_hasDerivAt_artanh (ne_of_lt h1) (ne_of_gt hm1)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hm1 h1] with u hu
  show Real.artanh u = Real.log ((1 + u) / (1 - u)) / 2
  exact (Real.artanh_eq_half_log
    (Set.mem_Icc.mpr ⟨hu.1.le, hu.2.le⟩)).trans (by ring)

/-- The order-5 `artanh` partial sum: `u + u³/3 + u⁵/5 + u⁷/7 + u⁹/9`. -/
noncomputable def lkB5 (u : ℝ) : ℝ := u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / 7 + u ^ 9 / 9

theorem lkB5_hasDerivAt (u : ℝ) : HasDerivAt lkB5 (1 + u ^ 2 + u ^ 4 + u ^ 6 + u ^ 8) u := by
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (u ^ 2) u := by
    have := (hasDerivAt_pow 3 u).div_const 3
    simpa [pow_succ] using this
  have h5 : HasDerivAt (fun x : ℝ => x ^ 5 / 5) (u ^ 4) u := by
    have := (hasDerivAt_pow 5 u).div_const 5
    simpa [pow_succ] using this
  have h7 : HasDerivAt (fun x : ℝ => x ^ 7 / 7) (u ^ 6) u := by
    have := (hasDerivAt_pow 7 u).div_const 7
    simpa [pow_succ] using this
  have h9 : HasDerivAt (fun x : ℝ => x ^ 9 / 9) (u ^ 8) u := by
    have := (hasDerivAt_pow 9 u).div_const 9
    simpa [pow_succ] using this
  have h := ((((hasDerivAt_id u).add h3).add h5).add h7).add h9
  rw [show lkB5 = fun x : ℝ => x + x ^ 3 / 3 + x ^ 5 / 5 + x ^ 7 / 7 + x ^ 9 / 9 from rfl]
  exact h

theorem lkB5_deriv (u : ℝ) : deriv lkB5 u = 1 + u ^ 2 + u ^ 4 + u ^ 6 + u ^ 8 :=
  (lkB5_hasDerivAt u).deriv

theorem lkB5_differentiable : Differentiable ℝ lkB5 := fun u => (lkB5_hasDerivAt u).differentiableAt

theorem lkB5_continuous : Continuous lkB5 := lkB5_differentiable.continuous

theorem lkB5_zero : lkB5 0 = 0 := by unfold lkB5; norm_num

theorem lkB5_nonneg {u : ℝ} (h0 : 0 ≤ u) : 0 ≤ lkB5 u := by
  have h3 : (0:ℝ) ≤ u ^ 3 := pow_nonneg h0 3
  have h5 : (0:ℝ) ≤ u ^ 5 := pow_nonneg h0 5
  have h7 : (0:ℝ) ≤ u ^ 7 := pow_nonneg h0 7
  have h9 : (0:ℝ) ≤ u ^ 9 := pow_nonneg h0 9
  unfold lkB5
  linarith

/-- `Real.artanh` is continuous on `[0, s]` for any `s < 1` (agrees there with
the log-form, whose continuity is the landed `nb12_continuousOn_logRatio`). -/
theorem lkB_artanh_continuousOn {s : ℝ} (hs1 : s < 1) :
    ContinuousOn Real.artanh (Set.Icc 0 s) := by
  refine ContinuousOn.congr (nb12_continuousOn_logRatio hs1) ?_
  intro x hx
  have hxm : x ∈ Set.Icc (-1) 1 := Set.mem_Icc.mpr ⟨by linarith [hx.1], by linarith [hx.2, hs1]⟩
  show Real.artanh x = Real.log ((1 + x) / (1 - x)) / 2
  exact (Real.artanh_eq_half_log hxm).trans (by ring)

/-! ## 1. The two series-gap bounds -/

/-- Derivative of the gap `artanh - lkB5` is `u^10/(1-u²)` on `(-1, 1)`. -/
theorem lkB_gap_deriv {u : ℝ} (h1 : u < 1) (hm1 : -1 < u) :
    HasDerivAt (fun x : ℝ => Real.artanh x - lkB5 x) (u ^ 10 / (1 - u ^ 2)) u := by
  have h := (lkB_hasDerivAt_artanh h1 hm1).sub (lkB5_hasDerivAt u)
  refine h.congr_deriv ?_
  have hne : (1 : ℝ) - u ^ 2 ≠ 0 := by
    intro hh
    have hu2 : u ^ 2 < 1 := by nlinarith [hm1, h1]
    linarith
  field_simp
  ring

/-- **Lower series bracket**: `lkB5 u ≤ artanh u` for `0 ≤ u < 1`
(the gap derivative `u^10/(1-u²)` is nonnegative, the gap is `0` at `u = 0`). -/
theorem lkB5_le_artanh {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : lkB5 u ≤ Real.artanh u := by
  have hcont : ContinuousOn (fun x : ℝ => Real.artanh x - lkB5 x) (Set.Icc 0 u) :=
    (lkB_artanh_continuousOn h1).sub lkB5_continuous.continuousOn
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => Real.artanh x - lkB5 x)
      (interior (Set.Icc 0 u)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact ((lkB_hasDerivAt_artanh (lt_trans hx.2 h1) (by linarith [hx.1])).sub
      (lkB5_hasDerivAt x)).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (fun x : ℝ => Real.artanh x - lkB5 x) (Set.Icc 0 u) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 u) hcont hdiff (by
      intro x hx
      rw [interior_Icc] at hx
      rw [(lkB_gap_deriv (lt_trans hx.2 h1) (by linarith [hx.1])).deriv]
      have hpos : (0:ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, h1]
      exact div_nonneg (by positivity) hpos.le)
  have h0eq : (fun x : ℝ => Real.artanh x - lkB5 x) 0 = 0 := by
    simp [Real.artanh_zero, lkB5_zero]
  have hval := hmono (Set.mem_Icc.mpr ⟨le_refl 0, h0⟩) (Set.mem_Icc.mpr ⟨h0, le_refl u⟩) h0
  rw [h0eq] at hval
  linarith

/-- **Upper series bracket**: for `0 ≤ u ≤ uh < 1`,
`artanh u ≤ lkB5 u + u * (uh ^ 10 / (1 - uh ^ 2))` — the gap derivative is
`uh^10/(1-uh²) - u^10/(1-u²) ≥ 0` on `[0, uh]`, since `u^10 ≤ uh^10` and
`1/(1-u²) ≤ 1/(1-uh²)` factorwise. -/
theorem artanh_le_lkB5_add {u uh : ℝ} (h0 : 0 ≤ u) (hu : u ≤ uh) (h1 : uh < 1) :
    Real.artanh u ≤ lkB5 u + u * (uh ^ 10 / (1 - uh ^ 2)) := by
  have hM0 : (0:ℝ) ≤ uh ^ 10 / (1 - uh ^ 2) := by
    have hpos : (0:ℝ) < 1 - uh ^ 2 := by
      have h01 : (0:ℝ) ≤ uh := le_trans h0 hu
      nlinarith
    exact div_nonneg (by positivity) hpos.le
  have hcont : ContinuousOn
      (fun x : ℝ => lkB5 x + x * (uh ^ 10 / (1 - uh ^ 2)) - Real.artanh x)
      (Set.Icc 0 uh) :=
    (lkB5_continuous.continuousOn.add
      (Continuous.continuousOn
        (continuous_id.mul continuous_const))).sub (lkB_artanh_continuousOn h1)
  have hdiff : DifferentiableOn ℝ
      (fun x : ℝ => lkB5 x + x * (uh ^ 10 / (1 - uh ^ 2)) - Real.artanh x)
      (interior (Set.Icc 0 uh)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact (((lkB5_hasDerivAt x).add
        ((hasDerivAt_id x).mul (hasDerivAt_const x (uh ^ 10 / (1 - uh ^ 2))))).sub
      (lkB_hasDerivAt_artanh (lt_trans hx.2 h1) (by linarith [hx.1, h0, hu]))).differentiableAt
      |>.differentiableWithinAt
  have hmono : MonotoneOn
      (fun x : ℝ => lkB5 x + x * (uh ^ 10 / (1 - uh ^ 2)) - Real.artanh x)
      (Set.Icc 0 uh) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 uh) hcont hdiff ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : (0:ℝ) ≤ x := hx.1.le
    have hx0l : (0:ℝ) < x := hx.1
    have hx1 : x < 1 := lt_trans hx.2 h1
    have hxa : x ≤ uh := hx.2.le
    have hder : HasDerivAt
        (fun x : ℝ => lkB5 x + x * (uh ^ 10 / (1 - uh ^ 2)) - Real.artanh x)
        (uh ^ 10 / (1 - uh ^ 2) - x ^ 10 / (1 - x ^ 2)) x := by
      refine (((lkB5_hasDerivAt x).add
          ((hasDerivAt_id x).mul (hasDerivAt_const x (uh ^ 10 / (1 - uh ^ 2))))).sub
        (lkB_hasDerivAt_artanh hx1 (by linarith [hx.1, h0, hu]))).congr_deriv ?_
      have hne : (1 : ℝ) - x ^ 2 ≠ 0 := by
        intro hh
        nlinarith
      field_simp
      ring
    rw [hder.deriv]
    -- the factorwise tail comparison: x^10/(1-x²) ≤ uh^10/(1-uh²)
    have hx2 : (0:ℝ) ≤ x ^ 10 := by positivity
    have hpow : x ^ 10 ≤ uh ^ 10 := pow_le_pow_left₀ hx0 hxa 10
    have hdenx : (0:ℝ) < 1 - x ^ 2 := by nlinarith
    have hdenu : (0:ℝ) < 1 - uh ^ 2 := by
      have h01 : (0:ℝ) ≤ uh := le_trans h0 hu
      nlinarith
    have hdenord : (1:ℝ) - uh ^ 2 ≤ 1 - x ^ 2 := by nlinarith
    have hinv : 1 / (1 - x ^ 2) ≤ 1 / (1 - uh ^ 2) := by
      rw [one_div, one_div]
      exact inv_anti₀ hdenu hdenord
    have htail : x ^ 10 / (1 - x ^ 2) ≤ uh ^ 10 / (1 - uh ^ 2) := by
      have hsplit : uh ^ 10 / (1 - uh ^ 2) = uh ^ 10 * (1 / (1 - uh ^ 2)) := by
        field_simp
      have hsplitx : x ^ 10 / (1 - x ^ 2) = x ^ 10 * (1 / (1 - x ^ 2)) := by
        field_simp
      rw [hsplitx, hsplit]
      calc x ^ 10 * (1 / (1 - x ^ 2))
          ≤ uh ^ 10 * (1 / (1 - x ^ 2)) :=
            mul_le_mul_of_nonneg_right hpow
              (div_nonneg (by norm_num) hdenx.le)
        _ ≤ uh ^ 10 * (1 / (1 - uh ^ 2)) :=
            mul_le_mul_of_nonneg_left hinv (pow_nonneg (le_trans h0 hu) 10)
    exact sub_nonneg.mpr htail
  have h0eq : (fun x : ℝ => lkB5 x + x * (uh ^ 10 / (1 - uh ^ 2)) - Real.artanh x) 0 = 0 := by
    simp [Real.artanh_zero, lkB5_zero]
  have hval := hmono (Set.mem_Icc.mpr ⟨le_refl 0, le_trans h0 hu⟩)
    (Set.mem_Icc.mpr ⟨h0, hu⟩) h0
  rw [h0eq] at hval
  linarith

/-- Corollary: `artanh u ≤ u / (1 - u²)` for `0 ≤ u < 1` — the order-1
majorant that drives the monotonicity of `artanh u / u`. -/
theorem lkB_artanh_le_div {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) :
    Real.artanh u ≤ u / (1 - u ^ 2) := by
  have hup := artanh_le_lkB5_add h0 (le_refl u) h1
  have hpos : (0:ℝ) < 1 - u ^ 2 := by nlinarith
  have hb : lkB5 u ≤ (u - u ^ 11) / (1 - u ^ 2) := by
    have hb1 : lkB5 u ≤ u + u ^ 3 + u ^ 5 + u ^ 7 + u ^ 9 := by
      have h3 : (0:ℝ) ≤ u ^ 3 := pow_nonneg h0 3
      have h5 : (0:ℝ) ≤ u ^ 5 := pow_nonneg h0 5
      have h7 : (0:ℝ) ≤ u ^ 7 := pow_nonneg h0 7
      have h9 : (0:ℝ) ≤ u ^ 9 := pow_nonneg h0 9
      unfold lkB5
      linarith
    rw [le_div_iff₀ hpos]
    -- goal: lkB5 u * (1 - u²) ≤ u - u¹¹
    have hkey : (u + u ^ 3 + u ^ 5 + u ^ 7 + u ^ 9) * (1 - u ^ 2) = u - u ^ 11 := by ring
    have hstep : lkB5 u * (1 - u ^ 2)
        ≤ (u + u ^ 3 + u ^ 5 + u ^ 7 + u ^ 9) * (1 - u ^ 2) :=
      mul_le_mul_of_nonneg_right hb1 hpos.le
    rw [hkey] at hstep
    linarith
  have hu11 : u * (u ^ 10 / (1 - u ^ 2)) = u ^ 11 / (1 - u ^ 2) := by
    rw [mul_div, show u * u ^ 10 = u ^ 11 from by ring]
  have hjoin : (u - u ^ 11) / (1 - u ^ 2) + u ^ 11 / (1 - u ^ 2) = u / (1 - u ^ 2) := by
    rw [← add_div, show u - u ^ 11 + u ^ 11 = u from by ring]
  rw [hu11] at hup
  linarith [hup, hb, hjoin]

/-! ## 2. Negative-branch identity and `artanh u / u` monotonicity -/

/-- **Negative-branch identity**: for `0 < u < 1`, `matan (-(u ^ 2)) = artanh u / u`. -/
theorem lkB_matan_neg_eq {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    matan (-(u ^ 2)) = Real.artanh u / u := by
  unfold matan
  rw [if_neg (show -(u ^ 2) ≠ 0 from by
      intro hh
      have h2 : u ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h0)
      exact h2 (by rw [neg_eq_zero] at hh; exact hh)),
    if_neg (show ¬ (-(u ^ 2) > 0) from by
      intro hh
      linarith [sq_nonneg u])]
  rw [show -(-(u ^ 2)) = u ^ 2 from by ring]
  rw [show Real.sqrt (u ^ 2) = u from Real.sqrt_sq h0.le]
  have hum : u ∈ Set.Icc (-1) 1 := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  rw [Real.artanh_eq_half_log hum]
  field_simp

/-- `g u = artanh u / u` is monotone on `[a, b] ⊆ (0, 1)`; its derivative is
`(u/(1-u²) - artanh u)/u² ≥ 0` by `lkB_artanh_le_div`. -/
theorem lkB_g_mono {a b : ℝ} (h0 : 0 < a) (hab : a ≤ b) (h1 : b < 1) :
    MonotoneOn (fun u : ℝ => Real.artanh u / u) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun u : ℝ => Real.artanh u / u) (Set.Icc a b) := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le h0 hxa
    have hx1 : x < 1 := lt_of_le_of_lt hxb h1
    exact (((lkB_hasDerivAt_artanh hx1 (by linarith [hxa, h0])).div (hasDerivAt_id x)
      (ne_of_gt hx0)).differentiableAt).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun u : ℝ => Real.artanh u / u)
      (interior (Set.Icc a b)) := by
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hxa, hxb⟩ := hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le h0 hxa.le
    exact ((lkB_hasDerivAt_artanh (lt_trans hxb h1) (by linarith [hxa, h0])).div
      (hasDerivAt_id x) (ne_of_gt hx0)).differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff ?_
  intro x hx
  rw [interior_Icc] at hx
  obtain ⟨hxa, hxb⟩ := hx
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le h0 hxa.le
  have hx1 : x < 1 := lt_trans hxb h1
  have hder : HasDerivAt (fun u : ℝ => Real.artanh u / u)
      ((x / (1 - x ^ 2) - Real.artanh x) / x ^ 2) x := by
    refine ((lkB_hasDerivAt_artanh hx1 (by linarith [hxa, h0])).div (hasDerivAt_id x)
      (ne_of_gt hx0)).congr_deriv ?_
    have hne : (1 : ℝ) - x ^ 2 ≠ 0 := by
      intro hh
      nlinarith
    simp only [id_eq]
    field_simp
  rw [hder.deriv]
  have hmajor := lkB_artanh_le_div hx0.le hx1
  exact div_nonneg (by linarith) (pow_nonneg hx0.le 2)

/-! ## 3. Generator-facing exact-rational point enclosure -/

/-- Exact-rational mirror of `lkB5` (the generator computes the bracket
endpoints by pure ℚ arithmetic). -/
def lkB5r (q : ℚ) : ℚ := q + q ^ 3 / 3 + q ^ 5 / 5 + q ^ 7 / 7 + q ^ 9 / 9

theorem lkB5r_cast (q : ℚ) : ((lkB5r q : ℚ) : ℝ) = lkB5 ((q : ℚ) : ℝ) := by
  simp only [lkB5r, lkB5, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]

/-- **Negative-branch point enclosure** (G3 final product): for rational
`tI` with `-1 < tI < 0` and rational sqrt brackets `ql² ≤ -tI ≤ qh²` with
`0 < ql ≤ qh < 1` (produced from the landed InvSqrt/√ base),
`matan tI ∈ [lkB5r ql / ql, (lkB5r qh + qh * (qh ^ 10 / (1 - qh ^ 2))) / qh]`
(the upper endpoint equals `lkB5r qh / qh + qh ^ 10 / (1 - qh ^ 2)`; this
grouping makes the Lean proof compose directly) — both endpoints exact
rationals. -/
theorem lkB_matan_neg_pt (tI ql qh : ℚ) (V : QInterval)
    (htm1 : -1 < tI) (ht0 : tI < 0)
    (hq0 : (0:ℚ) < ql) (horder : ql ≤ qh) (hq1 : qh < 1)
    (hql2 : ((ql : ℚ) : ℝ) ^ 2 ≤ -((tI : ℚ) : ℝ))
    (hqh2 : -((tI : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) ^ 2)
    (hV : V = QInterval.mk (lkB5r ql / ql)
      ((lkB5r qh + qh * (qh ^ 10 / (1 - qh ^ 2))) / qh)) :
    V.mem (matan ((tI : ℚ) : ℝ)) := by
  have ht0r : ((tI : ℚ) : ℝ) < 0 := by exact_mod_cast ht0
  have hneg : (0:ℝ) < -((tI : ℚ) : ℝ) := by linarith
  obtain ⟨s, hsd⟩ : ∃ z : ℝ, z = Real.sqrt (-((tI : ℚ) : ℝ)) := ⟨_, rfl⟩
  have hs0 : (0:ℝ) < s := by
    rw [hsd]
    exact Real.sqrt_pos.mpr hneg
  have hsq : s ^ 2 = -((tI : ℚ) : ℝ) := by
    rw [hsd]
    exact Real.sq_sqrt hneg.le
  have hq0r : (0:ℝ) < ((ql : ℚ) : ℝ) := Rat.cast_pos.mpr hq0
  have hqhr0 : (0:ℝ) ≤ ((qh : ℚ) : ℝ) := by
    have h : (0:ℚ) ≤ qh := le_trans (le_of_lt hq0) horder
    exact_mod_cast h
  have hordr : ((ql : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) := Rat.cast_le.mpr horder
  have hq1r : ((qh : ℚ) : ℝ) < 1 := by exact_mod_cast hq1
  have hqlr : ((ql : ℚ) : ℝ) ≤ s := by
    rw [hsd]
    exact Real.le_sqrt_of_sq_le hql2
  have hshr : s ≤ ((qh : ℚ) : ℝ) := by
    rw [hsd]
    exact (Real.sqrt_le_left hqhr0).mpr hqh2
  have mql : ((ql : ℚ) : ℝ) ∈ Set.Icc ((ql : ℚ) : ℝ) ((qh : ℚ) : ℝ) :=
    ⟨le_refl ((ql : ℚ) : ℝ), hordr⟩
  have ms : s ∈ Set.Icc ((ql : ℚ) : ℝ) ((qh : ℚ) : ℝ) :=
    ⟨hqlr, hshr⟩
  have mqh : ((qh : ℚ) : ℝ) ∈ Set.Icc ((ql : ℚ) : ℝ) ((qh : ℚ) : ℝ) :=
    ⟨hordr, le_refl ((qh : ℚ) : ℝ)⟩
  -- the value identity and the g-chain
  have hmeq : matan ((tI : ℚ) : ℝ) = Real.artanh s / s := by
    rw [show ((tI : ℚ) : ℝ) = -(s ^ 2) from by rw [hsq]; ring]
    exact lkB_matan_neg_eq hs0 (lt_of_le_of_lt hshr hq1r)
  have hmono := lkB_g_mono hq0r hordr hq1r
  have hglower : Real.artanh ((ql:ℚ):ℝ) / ((ql:ℚ):ℝ)
      ≤ Real.artanh s / s :=
    hmono mql ms hqlr
  have hgupper : Real.artanh s / s ≤ Real.artanh ((qh:ℚ):ℝ) / ((qh:ℚ):ℝ) :=
    hmono ms mqh hshr
  -- rational bracket of the g-endpoints
  have hglb : ((lkB5r ql / ql : ℚ) : ℝ)
      ≤ Real.artanh ((ql:ℚ):ℝ) / ((ql:ℚ):ℝ) := by
    have hlow := lkB5_le_artanh hq0r.le (lt_of_le_of_lt hordr hq1r)
    have hage : (0:ℝ) ≤ Real.artanh ((ql : ℚ) : ℝ) := Real.artanh_nonneg hq0r.le
    rw [Rat.cast_div, lkB5r_cast]
    exact div_le_div₀ hage hlow hq0r (le_refl _)
  have hq0rC : (0:ℝ) < ((qh : ℚ) : ℝ) := lt_of_lt_of_le hq0r hordr
  have hghb : Real.artanh ((qh:ℚ):ℝ) / ((qh:ℚ):ℝ)
      ≤ (((lkB5r qh + qh * (qh ^ 10 / (1 - qh ^ 2))) / qh : ℚ) : ℝ) := by
    have hupp := artanh_le_lkB5_add (le_of_lt hq0rC) (le_refl _) hq1r
    have hcastR : (((lkB5r qh + qh * (qh ^ 10 / (1 - qh ^ 2))) / qh : ℚ) : ℝ)
        = (lkB5 ((qh : ℚ) : ℝ) + ((qh : ℚ) : ℝ)
            * (((qh : ℚ) : ℝ) ^ 10 / (1 - ((qh : ℚ) : ℝ) ^ 2)))
          / ((qh : ℚ) : ℝ) := by
      simp only [Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_one, Rat.cast_sub, lkB5r_cast]
    rw [hcastR]
    rw [div_le_iff₀ hq0rC]
    rw [div_mul_cancel₀ _ (ne_of_gt hq0rC)]
    exact hupp
  rw [hV, QInterval.mem]
  constructor
  · calc ((lkB5r ql / ql : ℚ) : ℝ)
        ≤ Real.artanh ((ql:ℚ):ℝ) / ((ql:ℚ):ℝ) := hglb
      _ ≤ Real.artanh s / s := hglower
      _ = matan ((tI : ℚ) : ℝ) := hmeq.symm
  · calc matan ((tI : ℚ) : ℝ) = Real.artanh s / s := hmeq
      _ ≤ Real.artanh ((qh:ℚ):ℝ) / ((qh:ℚ):ℝ) := hgupper
      _ ≤ (((lkB5r qh + qh * (qh ^ 10 / (1 - qh ^ 2))) / qh : ℚ) : ℝ) := hghb

/-! ## 4. Transports (negative slots and the cross-zero composition) -/

/-- Branch-agnostic antitone slot transport: for `-1 < lo ≤ t ≤ hi`,
`matan t ∈ [Vh.lo, Vl.hi]` given point enclosures at the endpoints.  Because
`nb12w_matan_strictAntiOn` is antitone on the **whole** `(-1, ∞)`, this single
lemma serves both as the negative-slot assembly (`lo < hi ≤ 0`, both
enclosures from `lkB_matan_neg_pt`) **and** as the cross-zero composition
(`tlo < 0 < thi`, the `tlo` enclosure from `lkB_matan_neg_pt`, the `thi`
enclosure from the positive kit / exact point data).  Endpoint direction
warning: the **more negative** endpoint `lo` carries the *upper* edge
(`matan` is decreasing in `t`). -/
theorem lkB_matan_transport (lo hi t : ℝ) (hm : -1 < lo) (hlt : lo ≤ t) (htu : t ≤ hi)
    (Vl Vh : QInterval) (hVl : Vl.mem (matan lo)) (hVh : Vh.mem (matan hi)) :
    (QInterval.mk Vh.lo Vl.hi).mem (matan t) := by
  have h1 : matan t ≤ matan lo :=
    nb12w_matan_strictAntiOn.antitoneOn (Set.mem_Ioi.mpr hm)
      (Set.mem_Ioi.mpr (by linarith)) hlt
  have h2 : matan hi ≤ matan t :=
    nb12w_matan_strictAntiOn.antitoneOn (Set.mem_Ioi.mpr (by linarith))
      (Set.mem_Ioi.mpr (by linarith)) htu
  rw [QInterval.mem]
  exact ⟨le_trans hVh.1 h2, le_trans h1 hVl.2⟩

/-- Negative-branch slot bracket: for a rational slot `TI` with
`-1 < TI.lo ≤ TI.hi ≤ 0` and point enclosures at both endpoints, every slot
point `t` satisfies `matan t ∈ [Vh.lo, Vl.hi]`. -/
theorem lkB_matan_neg_slot (TI : QInterval) (hm : -1 < TI.lo) (hz : TI.hi ≤ 0)
    (Vl Vh : QInterval)
    (hVl : Vl.mem (matan ((TI.lo : ℚ) : ℝ))) (hVh : Vh.mem (matan ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (QInterval.mk Vh.lo Vl.hi).mem (matan t) := by
  intro t h1t h2t
  exact lkB_matan_transport ((TI.lo : ℚ) : ℝ) ((TI.hi : ℚ) : ℝ) t
    (by exact_mod_cast hm) h1t h2t Vl Vh hVl hVh

/-- `matan` at the removable singularity: `matan 0 = 1` (the zero slot point
of a cross-zero composition). -/
theorem lkB_matan_zero : matan 0 = 1 := by unfold matan; rw [if_pos rfl]

/-- Explicit cross-zero composition: for `tlo < 0 < thi` with `-1 < tlo`, the
mixed-branch endpoint enclosures bracket `matan` on the whole slot — the
negative-side enclosure `Vl` (at `tlo`) provides the upper edge, the
positive-side enclosure `Vh` (at `thi`) the lower edge. -/
theorem lkB_matan_cross (tlo thi t : ℝ) (hm : -1 < tlo) (hzlo : tlo < 0) (hzhi : 0 < thi)
    (hlt : tlo ≤ t) (htu : t ≤ thi)
    (Vl Vh : QInterval) (hVl : Vl.mem (matan tlo)) (hVh : Vh.mem (matan thi)) :
    (QInterval.mk Vh.lo Vl.hi).mem (matan t) :=
  lkB_matan_transport tlo thi t hm hlt htu Vl Vh hVl hVh

/-! ## 5. `matanD` / `matanDD` on the negative branch -/

/-- Negative-branch `matanD` interval ops: for `-1 < TI.lo ≤ TI.hi < 0` the
clean form `matanD t = (1/(2t))·(1/(1+t) - matan t)` is enclosed by the same
interval expression as the landed positive-branch ops, with the reciprocal
sign side-conditions flipped: `1 + TI > 0` (so its `inv` takes `Or.inl`) and
`2·TI < 0` (so its `inv` takes `Or.inr`). -/
theorem lkB_matanD_ops_neg (TI VI : QInterval) (hm1 : (-1:ℚ) < TI.lo) (hneg : TI.hi < 0)
    (horder : TI.lo ≤ TI.hi)
    (hVI : ∀ x : ℝ, ((TI.lo : ℚ) : ℝ) ≤ x → x ≤ ((TI.hi : ℚ) : ℝ) → VI.mem (matan x)) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      ((((QInterval.const (1:ℚ)).add TI).inv.sub VI).mul
        (((QInterval.const (2:ℚ)).mul TI).inv)).mem (matanD t) := by
  intro t h1t h2t
  have hthr : ((TI.hi : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
  have htneg : t < 0 := lt_of_le_of_lt h2t hthr
  have ht0 : t ≠ 0 := by
    intro hh
    have hz : t ≤ 0 := hh.le
    linarith
  rw [matanD_of_ne ht0]
  rw [show (1 / (2 * t)) * (1 / (1 + t) - matan t)
      = ((((1:ℚ) : ℝ) + t)⁻¹ - matan t) * ((((2:ℚ) : ℝ) * t)⁻¹) from by
    rw [one_div, one_div, Rat.cast_one, Rat.cast_ofNat]
    ring]
  have h1pos : (0:ℚ) < ((QInterval.const (1:ℚ)).add TI).lo := by
    show (0:ℚ) < (1:ℚ) + TI.lo
    linarith
  have hlo0 : TI.lo < 0 := lt_of_le_of_lt horder hneg
  have h2neg : ((QInterval.const (2:ℚ)).mul TI).hi < 0 := by
    show max (max ((2:ℚ) * TI.lo) ((2:ℚ) * TI.hi)) (max ((2:ℚ) * TI.lo) ((2:ℚ) * TI.hi)) < 0
    simp only [max_lt_iff]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  have hA : (((QInterval.const (1:ℚ)).add TI)).mem ((((1:ℚ) : ℝ)) + t) :=
    QInterval.mem_add QInterval.mem_const ⟨h1t, h2t⟩
  have hAi := QInterval.mem_inv hA (Or.inl h1pos)
  have hsub := QInterval.mem_sub hAi (hVI t h1t h2t)
  have hB : (((QInterval.const (2:ℚ)).mul TI)).mem ((((2:ℚ) : ℝ)) * t) :=
    QInterval.mem_mul QInterval.mem_const ⟨h1t, h2t⟩
  have hBi := QInterval.mem_inv hB (Or.inr h2neg)
  exact QInterval.mem_mul hsub hBi

/-- Branch-agnostic `matanDD` point enclosure from a coherent `e`-interval
(`e(t) = 1/(1+t) - matan t`): the proof is pure interval arithmetic away from
`t = 0`, so the same statement covers **both** branches — the negative-branch
consumption is `tI < 0` here. -/
theorem lkB_matanDD_pt (tI : ℚ) (V E D : QInterval) (ht0 : tI ≠ 0)
    (hV : V.mem (matan ((tI : ℚ) : ℝ)))
    (hE : E = (QInterval.const (1 / (1 + tI))).sub V)
    (hD : D = (((QInterval.const (3 / (4 * tI * tI))).mul E).neg).sub
      (QInterval.const (1 / (2 * tI * (1 + tI) ^ 2)))) :
    D.mem (matanDD ((tI : ℚ) : ℝ)) := by
  have ht0r : ((tI : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ht0
  have hAc : (QInterval.const (1 / (1 + tI))).mem (1 / (1 + ((tI : ℚ) : ℝ))) := by
    simp only [QInterval.const, QInterval.mem, Rat.cast_div, Rat.cast_one, Rat.cast_add]
    exact ⟨le_of_eq rfl, le_of_eq rfl⟩
  have hsub := QInterval.mem_sub hAc hV
  have hcastC : (((3 / (4 * tI * tI) : ℚ) : ℝ))
      = (3:ℝ) / (4 * ((tI : ℚ) : ℝ) ^ 2) := by
    rw [Rat.cast_div, Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_ofNat]
    congr 1
    ring
  have hconst : (QInterval.const (3 / (4 * tI * tI))).mem
      ((3:ℝ) / (4 * ((tI : ℚ) : ℝ) ^ 2)) := by
    have h := QInterval.mem_const (q := (3 / (4 * tI * tI) : ℚ))
    rw [hcastC] at h
    exact h
  have hterm1 := QInterval.mem_neg (QInterval.mem_mul hconst hsub)
  have hcastT : (((1 / (2 * tI * (1 + tI) ^ 2) : ℚ) : ℝ))
      = (1:ℝ) / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2) := by
    rw [Rat.cast_div, Rat.cast_mul, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_one, Rat.cast_ofNat]
  have hT : (QInterval.const (1 / (2 * tI * (1 + tI) ^ 2))).mem
      ((1:ℝ) / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2)) := by
    have h := QInterval.mem_const (q := (1 / (2 * tI * (1 + tI) ^ 2) : ℚ))
    rw [hcastT] at h
    exact h
  have hmem := QInterval.mem_sub hterm1 hT
  rw [matanDD_of_ne ht0r]
  rw [show -((3 : ℝ) / (4 * ((tI : ℚ) : ℝ) ^ 2))
        * (1 / (1 + ((tI : ℚ) : ℝ)) - matan ((tI : ℚ) : ℝ))
        - 1 / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2)
      = -((3 : ℝ) / (4 * ((tI : ℚ) : ℝ) ^ 2)
          * (1 / (1 + ((tI : ℚ) : ℝ)) - matan ((tI : ℚ) : ℝ)))
        - 1 / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2) from by ring]
  subst hE
  rw [hD]
  exact hmem

/-- Soundness helper for `lkB_matanDD_ops_neg`: on a negative slot
`TI.lo ≤ t ≤ TI.hi < 0` the coefficient `3/(4·t·t)` lies in the exact-rational
coefficient interval `[3/(4·TI.lo²), 3/(4·TI.hi²)]` (t² is decreasing in t on
the negatives, so `3/(4t²)` is *increasing* in t there). -/
theorem lkB_coef_mem (TI : QInterval) (horder : TI.lo ≤ TI.hi) (hneg : TI.hi < 0) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (QInterval.mk (3 / (4 * TI.lo * TI.lo)) (3 / (4 * TI.hi * TI.hi))).mem
        (3 / (4 * t * t)) := by
  intro t h1t h2t
  have hthr : ((TI.hi : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
  have hord : ((TI.lo : ℚ) : ℝ) ≤ ((TI.hi : ℚ) : ℝ) := Rat.cast_le.mpr horder
  have hsqhi : (0:ℝ) < 4 * ((TI.hi : ℚ) : ℝ) * ((TI.hi : ℚ) : ℝ) := by nlinarith [hthr]
  have hsqlo : (0:ℝ) < 4 * ((TI.lo : ℚ) : ℝ) * ((TI.lo : ℚ) : ℝ) := by
    have h1 : ((TI.lo : ℚ) : ℝ) < 0 := lt_of_le_of_lt hord hthr
    nlinarith [h1]
  have h4tt : (0:ℝ) < 4 * t * t := by nlinarith [hthr, h2t]
  have hbig : 4 * ((TI.hi : ℚ) : ℝ) * ((TI.hi : ℚ) : ℝ) ≤ 4 * t * t := by
    nlinarith [hthr, h2t]
  have hsmall : 4 * t * t ≤ 4 * ((TI.lo : ℚ) : ℝ) * ((TI.lo : ℚ) : ℝ) := by
    have h2 : t ≤ 0 := le_trans h2t hthr.le
    nlinarith [hord, hthr, h1t, h2]
  rw [QInterval.mem]
  constructor
  · show ((3 / (4 * TI.lo * TI.lo) : ℚ) : ℝ) ≤ (3:ℝ) / (4 * t * t)
    simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    rw [div_le_div_iff₀ hsqlo h4tt]
    linarith
  · show (3:ℝ) / (4 * t * t) ≤ ((3 / (4 * TI.hi * TI.hi) : ℚ) : ℝ)
    simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    rw [div_le_div_iff₀ h4tt hsqhi]
    linarith

/-- Negative-branch `matanDD` **slot** enclosure, sound without any
monotonicity assumption on `matanDD`: every slot point `t` (with
`-1 < TI.lo ≤ t ≤ TI.hi < 0`) satisfies
`matanDD t ∈ (coef·E).neg - ((2TI)⁻¹·B⁻¹)·B⁻¹` where `coef` is the exact
coefficient interval of `3/(4t²)`, `E` brackets `e(t) = 1/(1+t) - matan t`
through `VI`, and the `1/(2t(1+t)²)` term is enclosed by the all-corners
product of the factor intervals `(2·TI)⁻¹` and `(1+TI)⁻¹`. -/
theorem lkB_matanDD_ops_neg (TI VI : QInterval) (hm1 : (-1:ℚ) < TI.lo) (hneg : TI.hi < 0)
    (horder : TI.lo ≤ TI.hi)
    (hVI : ∀ x : ℝ, ((TI.lo : ℚ) : ℝ) ≤ x → x ≤ ((TI.hi : ℚ) : ℝ) → VI.mem (matan x)) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      ((((QInterval.mk (3 / (4 * TI.lo * TI.lo)) (3 / (4 * TI.hi * TI.hi))).mul
          (((QInterval.const (1:ℚ)).add TI).inv.sub VI)).neg).sub
        ((((QInterval.const (2:ℚ)).mul TI).inv.mul
          ((QInterval.const (1:ℚ)).add TI).inv).mul
          ((QInterval.const (1:ℚ)).add TI).inv)).mem (matanDD t) := by
  intro t h1t h2t
  have hm1r : (-1:ℝ) < ((TI.lo : ℚ) : ℝ) := by exact_mod_cast hm1
  have hthr : ((TI.hi : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
  have htneg : t < 0 := lt_of_le_of_lt h2t hthr
  have ht0 : t ≠ 0 := by
    intro hh
    have hz : t ≤ 0 := hh.le
    linarith
  have h1t0 : (1:ℝ) + t ≠ 0 := by
    intro hh
    have hz : (0:ℝ) ≤ 1 + t := by linarith
    linarith [h1t, hm1r]
  rw [matanDD_of_ne ht0]
  rw [show (3:ℝ) / (4 * t ^ 2) = 3 / (4 * t * t) from by
    rw [show (4:ℝ) * t ^ 2 = 4 * t * t from by ring]]
  rw [show 1 / (2 * t * (1 + t) ^ 2) = (2 * t)⁻¹ * (1 + t)⁻¹ * (1 + t)⁻¹ from by
    rw [one_div, mul_inv, ← inv_pow, pow_two]
    ring]
  rw [one_div]
  rw [neg_mul]
  have hcoef := lkB_coef_mem TI horder hneg t h1t h2t
  have hA0 : (((QInterval.const (1:ℚ)).add TI)).mem ((((1:ℚ) : ℝ)) + t) :=
    QInterval.mem_add QInterval.mem_const ⟨h1t, h2t⟩
  rw [Rat.cast_one] at hA0
  have h1pos : (0:ℚ) < ((QInterval.const (1:ℚ)).add TI).lo := by
    show (0:ℚ) < (1:ℚ) + TI.lo
    linarith
  have hAi := QInterval.mem_inv hA0 (Or.inl h1pos)
  have hsub := QInterval.mem_sub hAi (hVI t h1t h2t)
  have hterm1 := QInterval.mem_neg (QInterval.mem_mul hcoef hsub)
  have hB0 : (((QInterval.const (2:ℚ)).mul TI)).mem ((((2:ℚ) : ℝ)) * t) :=
    QInterval.mem_mul QInterval.mem_const ⟨h1t, h2t⟩
  rw [Rat.cast_ofNat] at hB0
  have hlo0 : TI.lo < 0 := lt_of_le_of_lt horder hneg
  have h2neg : ((QInterval.const (2:ℚ)).mul TI).hi < 0 := by
    show max (max ((2:ℚ) * TI.lo) ((2:ℚ) * TI.hi)) (max ((2:ℚ) * TI.lo) ((2:ℚ) * TI.hi)) < 0
    simp only [max_lt_iff]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  have hBi := QInterval.mem_inv hB0 (Or.inr h2neg)
  have hterm2 := QInterval.mem_mul (QInterval.mem_mul hBi hAi) hAi
  exact QInterval.mem_sub hterm1 hterm2

/-! ## Axiom audit (standard three only: propext / Classical.choice / Quot.sound) -/

#print axioms lkB_hasDerivAt_artanh
#print axioms lkB5_hasDerivAt
#print axioms lkB5_deriv
#print axioms lkB5_zero
#print axioms lkB5_nonneg
#print axioms lkB_artanh_continuousOn
#print axioms lkB_gap_deriv
#print axioms lkB5_le_artanh
#print axioms artanh_le_lkB5_add
#print axioms lkB_artanh_le_div
#print axioms lkB_matan_neg_eq
#print axioms lkB_g_mono
#print axioms lkB5r_cast
#print axioms lkB_matan_neg_pt
#print axioms lkB_matan_transport
#print axioms lkB_matan_neg_slot
#print axioms lkB_matan_zero
#print axioms lkB_matan_cross
#print axioms lkB_matanD_ops_neg
#print axioms lkB_matanDD_pt
#print axioms lkB_coef_mem
#print axioms lkB_matanDD_ops_neg

end Kepler.Text.TaylorSecond
