/-
Kepler.Text.TaylorSecond.MatanDDNegTransport — lane `wt1-matanDD-neg-transport-w1`
(2026-11-24), wt1 gap **G3 (final piece)**: the `matanDD` endpoint-coherent /
interval transport on the **negative branch and across zero** (the 204 fully
negative + 255 zero-crossing Route B leaves of 6,989 need a `matanDD` slot).

Context.  `MatanNegKit.lean` (landed `1aae10ca`) carries the factor-interval
`matanDD` slot enclosure `lkB_matanDD_ops_neg`, which is **sound without any
monotonicity assumption on `matanDD`** — but (a) it needs `TI.hi < 0` (both
reciprocal slots must be sign-definite), so it cannot cover zero-crossing
leaves, and (b) its all-corners factor products are `2.1×`–`1.1e4×` wider than
the endpoint brackets measured on the audited test slots
(`scripts/probe_dd_neg.py` S6), because the terms `1/(2t)` and
`1/(2t(1+t)^2)` cancel catastrophically near `0` while `1/(2t(1+t)^2)` is not
monotone on `(-1,0)` (its maximum sits at `t = -1/3`), so plain endpoint
products are unsound for that factor.  The emission lane therefore needs the
**monotone** route; this file supplies it.

Mathematical content (sign probed numerically *before* formalisation,
`scripts/probe_dd_neg.py` S1/S2, PR-55: `matanDD = matan''` and
`matan''' t = -∫₀¹ 6u⁶/(1+tu²)⁴ du < 0` for every `t > -1`, so `matanDD` is
strictly **decreasing on all of `(-1, ∞)`** — the negative branch and `t = 0`
included).
* §1 `lkB_matanDD_hasDerivAt`: the closed-form derivative
  `matanDD' t = 15(1/(1+t) - matan t)/(8t³) + 5/(4t²(1+t)²) + 1/(t(1+t)³)`
  for every `t ∈ (-1,∞) \ {0}` (generalises the landed positive-branch
  `matanDD_hasDerivAt_of_pos` of `Wt1MatanDDAnti`).
* §2 `lkB_matan_le_rat_neg`: the rational upper bound
  `matan t < (15 + 40t + 33t²)/(15(1+t)³)` on `(-1,0)`.  Proof: substitute
  `u = √(-t)`, use the landed order-7 artanh bracket `nb12w_artanh_le_sub7`,
  and compare with the exact identity
  `(15-40s+33s²)/(15(1-s)³) - (1 + s/3 + s²/5 + s³/(7(1-s)))
     = s³(16/35 + 2s/105 + 2s²/35)/(1-s)³`, `s = -t` (all terms positive);
  this replaces the factor-interval detour used by `lkB_matanDD_ops_neg`.
* §3 `lkB_matanDD_deriv_neg_of_neg` + `lkB_matanDD_strictAntiOn_neg`:
  `matanDD' t = N(t)/(8t³(1+t)³)` with `N > 0` and denominator `< 0`, so
  `matanDD` is strictly decreasing on `(-1, 0)`.
* §4 `lkB_matanDD_tendsto_zero` (punctured `𝓝[≠] 0`): the removable
  singularity value `matanDD 0 = 2/5` is a genuine limit.  Proof: the
  landed both-branch cubic bracket `nb12w_matan_bracket3`
  (`|matan t - (1 - t/3 + t²/5)| ≤ (4/21)|t|³` for `|t| ≤ 1/4`) makes the
  remainder `(3/(4t²))·δ → 0`, and the repaired factor is an explicit
  rational function with no pole:
  `-(3/(4t²))(1/(1+t) - (1 - t/3 + t²/5)) - 1/(2t(1+t)²)
     = (2/5 + t/20 + 3t²/20)/(1+t)²` (value `2/5` at `0`).
* §5 `lkB_matanDD_antitoneOn`: `AntitoneOn matanDD (Set.Ioi (-1))`, glued
  from §3, the landed positive branch `matanDD_strictAntiOn_pos`, and §4 at
  the crossing point (`matanDD y ≤ 2/5 ≤ matanDD x` for `y > 0 > x`).
* §6 the transport products (same interface invariant as the landed
  `lkB_matanDD_ops_neg`: exact-rational `t` interval + `matan`/`matanD`
  brackets in, exact-rational `matanDD` interval out):
  - `lkB_matanDD_transport` / `lkB_matanDD_slot`: reversed-endpoint
    evaluation on an arbitrary slot with `-1 < TI.lo` (negative, positive,
    and zero-crossing all in one statement);
  - `lkBDDpt` / `lkBDDpt_mem`: the point `matanDD` bracket built from a
    `matan` point bracket (same-endpoint pairing; `LeafChain` record: mixing
    endpoints yields an empty interval, but `lkBDDpt` at a single
    `tI` is branch-clean);
  - `lkBDDpt_of_matanD` / `lkBDDpt_of_matanD_mem`: the same from a `matanD`
    point bracket — `matanDD t = -(3/(2t))·matanD t - 1/(2t(1+t)²)`
    (`matanDD_eq_matanD_of_ne`, landed) is pure rectangle arithmetic;
  - `lkB_matanDD_slot_from_matan` / `lkB_matanDD_slot_from_matanD`: the
    generator-facing slot forms (endpoint brackets → `matanDD` slot
    interval) covering negative **and** zero-crossing leaves;
  - `lkB_matanDD_slot_zero_hi` / `lkB_matanDD_slot_zero_lo`: the
    zero-split convenience forms (a leaf split at `0` uses the exact
    removable value `2/5`);
  - `lkBddOpsNeg` / `lkB_matanDD_ops_neg_slot`: the **monotonicity-free**
    fallback with the identical input interface (the landed
    `lkB_matanDD_ops_neg` fed by the landed `lkB_matan_neg_slot`), kept for
    independent re-certification of negative slots; soundness first, but
    `2.1×`–`1.1e4×` wider than §6's endpoint brackets on the audited
    test slots (`scripts/probe_dd_neg.py` S6).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.MatanNegKit
import Kepler.Text.Wt1MatanDDAnti

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Kepler.Text
open Filter
open scoped Topology

/-! ## 1. The closed-form derivative of `matanDD` on `(-1, ∞) \ {0}` -/

/-- **Derivative of `matanDD` off zero, both branches**: for `-1 < t`, `t ≠ 0`,
`matanDD' t = 15(1/(1+t) - matan t)/(8t³) + 5/(4t²(1+t)²) + 1/(t(1+t)³)`.
Same proof skeleton as the landed `matanDD_hasDerivAt_of_pos`; only the
eventual-agreement neighbourhood is sign-split. -/
theorem lkB_matanDD_hasDerivAt {t : ℝ} (ht1 : -1 < t) (ht0 : t ≠ 0) :
    HasDerivAt matanDD
      (15 * (1 / (1 + t) - matan t) / (8 * t ^ 3) +
        5 / (4 * t ^ 2 * (1 + t) ^ 2) + 1 / (t * (1 + t) ^ 3)) t := by
  have h1t : (1 : ℝ) + t ≠ 0 := by linarith
  have h3over : HasDerivAt (fun u : ℝ => 3 / (2 * u)) (-(3 / (2 * t ^ 2))) t := by
    have h := (hasDerivAt_const t (3 : ℝ)).div
      ((hasDerivAt_id t).const_mul 2) (mul_ne_zero two_ne_zero ht0)
    convert h using 1 <;> first | rfl |
      ((try simp only [id_eq]); (field_simp [ht0]; ring))
  have hcoef : HasDerivAt (fun u : ℝ => -(3 / (2 * u))) (3 / (2 * t ^ 2)) t := by
    convert h3over.neg using 1 <;> first | rfl | ring
  have hbase : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
    simpa using (hasDerivAt_id t).const_add 1
  have hsq : HasDerivAt (fun u : ℝ => (1 + u) ^ 2) (2 * (1 + t)) t := by
    convert hbase.pow 2 using 1 <;> first | rfl | ring
  have hden : HasDerivAt (fun u : ℝ => 2 * u * (1 + u) ^ 2)
      (2 * (1 + t) ^ 2 + 2 * t * (2 * (1 + t))) t := by
    convert ((hasDerivAt_id t).const_mul 2).mul hsq using 1 <;>
      first | rfl | ((try simp only [id_eq]); ring)
  have hposinv : HasDerivAt (fun u : ℝ => 1 / (2 * u * (1 + u) ^ 2))
      (-1 / (2 * t ^ 2 * (1 + t) ^ 2) - 1 / (t * (1 + t) ^ 3)) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).div hden
      (mul_ne_zero (mul_ne_zero two_ne_zero ht0) (pow_ne_zero 2 h1t))
    convert h using 1 <;> first | rfl | (field_simp [ht0, h1t]; ring)
  have hform : HasDerivAt
      (fun u : ℝ => -(3 / (2 * u)) * matanD u - 1 / (2 * u * (1 + u) ^ 2))
      (15 * (1 / (1 + t) - matan t) / (8 * t ^ 3) +
        5 / (4 * t ^ 2 * (1 + t) ^ 2) + 1 / (t * (1 + t) ^ 3)) t := by
    have h := hcoef.mul (matanD_hasDerivAt ht1) |>.sub hposinv
    refine h.congr_deriv ?_
    rw [matanD_of_ne ht0, matanDD_of_ne ht0]
    field_simp [ht0, h1t]
    ring
  refine hform.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ u in 𝓝 t, u ≠ 0 := by
    rcases lt_or_gt_of_ne ht0 with hlt | hgt
    · filter_upwards [Ioo_mem_nhds (by linarith : t - 1 < t)
        (by linarith : t < t / 2)] with u hu
      exact ne_of_lt (by linarith [hu.2])
    · filter_upwards [Ioo_mem_nhds (by linarith : t / 2 < t)
        (by linarith : t < t + 1)] with u hu
      exact ne_of_gt (by linarith [hu.1])
  filter_upwards [hev] with u hu
  exact matanDD_eq_matanD_of_ne hu

/-! ## 2. The rational upper bound on `matan` over the negative branch -/

/-- **`matan t < (15 + 40t + 33t²)/(15(1+t)³)` for `-1 < t < 0`** — the sign
of `matanDD'`'s numerator.  Substituting `u = √(-t)`, `s = u² = -t`, the
landed order-7 artanh bracket gives
`matan t = artanh(u)/u ≤ 1 + s/3 + s²/5 + s³/(7(1-s))`, and the exact
difference to the claim is `s³(16/35 + 2s/105 + 2s²/35)/(1-s)³ > 0`. -/
theorem lkB_matan_le_rat_neg {t : ℝ} (ht1 : -1 < t) (ht0 : t < 0) :
    matan t < (15 + 40 * t + 33 * t ^ 2) / (15 * (1 + t) ^ 3) := by
  have hpos : (0 : ℝ) < -t := by linarith
  have hu2 : Real.sqrt (-t) ^ 2 = -t := Real.sq_sqrt hpos.le
  have hs0 : (0 : ℝ) < Real.sqrt (-t) := Real.sqrt_pos.mpr hpos
  have hs1 : Real.sqrt (-t) < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    linarith
  have harg : t = -(Real.sqrt (-t) ^ 2) := by rw [hu2]; ring
  have hmeq : matan t = Real.artanh (Real.sqrt (-t)) / Real.sqrt (-t) := by
    conv_lhs => rw [harg]
    exact lkB_matan_neg_eq hs0 hs1
  have hlog : Real.artanh (Real.sqrt (-t)) =
      Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2 := by
    rw [Real.artanh_eq_half_log
      (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)]
    ring
  have hden : (1 : ℝ) - Real.sqrt (-t) ^ 2 = 1 + t := by rw [hu2]; ring
  have hs3 : Real.sqrt (-t) ^ 3 = Real.sqrt (-t) * (-t) := by
    calc Real.sqrt (-t) ^ 3 = Real.sqrt (-t) * Real.sqrt (-t) ^ 2 := by ring
      _ = Real.sqrt (-t) * (-t) := by rw [hu2]
  have hs5 : Real.sqrt (-t) ^ 5 = Real.sqrt (-t) * t ^ 2 := by
    calc Real.sqrt (-t) ^ 5 = Real.sqrt (-t) * (Real.sqrt (-t) ^ 2) ^ 2 := by ring
      _ = Real.sqrt (-t) * (-t) ^ 2 := by rw [hu2]
      _ = Real.sqrt (-t) * t ^ 2 := by ring
  have hs7 : Real.sqrt (-t) ^ 7 = -(Real.sqrt (-t) * t ^ 3) := by
    calc Real.sqrt (-t) ^ 7 = Real.sqrt (-t) * (Real.sqrt (-t) ^ 2) ^ 3 := by ring
      _ = Real.sqrt (-t) * (-t) ^ 3 := by rw [hu2]
      _ = -(Real.sqrt (-t) * t ^ 3) := by ring
  -- the order-7 artanh bracket, divided by `√(-t) > 0`
  have hU : Real.artanh (Real.sqrt (-t)) / Real.sqrt (-t)
      ≤ 1 + (-t) / 3 + (-t) ^ 2 / 5 + (-t) ^ 3 / (7 * (1 + t)) := by
    rw [hlog, div_le_iff₀ hs0]
    refine le_trans (nb12w_artanh_le_sub7 hs0.le hs1) (le_of_eq ?_)
    rw [hden, hs3, hs5, hs7]
    field_simp
    try ring
  -- the exact difference is `s³(16/35 + 2s/105 + 2s²/35)/(1-s)³`
  have hkey : 1 + (-t) / 3 + (-t) ^ 2 / 5 + (-t) ^ 3 / (7 * (1 + t))
      < (15 + 40 * t + 33 * t ^ 2) / (15 * (1 + t) ^ 3) := by
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have heq : (15 + 40 * t + 33 * t ^ 2) / (15 * (1 + t) ^ 3)
        - (1 + (-t) / 3 + (-t) ^ 2 / 5 + (-t) ^ 3 / (7 * (1 + t)))
        = (-t) ^ 3 * (16 / 35 + 2 * (-t) / 105 + 2 * (-t) ^ 2 / 35) / (1 + t) ^ 3 := by
      field_simp
      ring
    have hposr : (0 : ℝ) <
        (-t) ^ 3 * (16 / 35 + 2 * (-t) / 105 + 2 * (-t) ^ 2 / 35) / (1 + t) ^ 3 := by
      positivity
    linarith
  rw [hmeq]
  exact lt_of_le_of_lt hU hkey

/-! ## 3. `matanDD` is strictly decreasing on the negative branch -/

/-- `deriv matanDD t < 0` for `-1 < t < 0`: the combined form
`N(t)/(8t³(1+t)³)` has `N > 0` (§2) and a negative denominator. -/
theorem lkB_matanDD_deriv_neg_of_neg {t : ℝ} (ht1 : -1 < t) (ht0 : t < 0) :
    deriv matanDD t < 0 := by
  rw [(lkB_matanDD_hasDerivAt ht1 (ne_of_lt ht0)).deriv]
  have h1t : (1 : ℝ) + t ≠ 0 := by linarith
  have hcomb : 15 * (1 / (1 + t) - matan t) / (8 * t ^ 3) +
      5 / (4 * t ^ 2 * (1 + t) ^ 2) + 1 / (t * (1 + t) ^ 3)
      = (15 + 40 * t + 33 * t ^ 2 - 15 * (1 + t) ^ 3 * matan t)
        / (8 * t ^ 3 * (1 + t) ^ 3) := by
    field_simp
    ring
  rw [hcomb]
  have hle := lkB_matan_le_rat_neg ht1 ht0
  have hN : (0 : ℝ) < 15 + 40 * t + 33 * t ^ 2 - 15 * (1 + t) ^ 3 * matan t := by
    have h1tp : (0 : ℝ) < 1 + t := by linarith
    have hmul : 15 * (1 + t) ^ 3 * matan t
        < 15 * (1 + t) ^ 3 * ((15 + 40 * t + 33 * t ^ 2) / (15 * (1 + t) ^ 3)) :=
      mul_lt_mul_of_pos_left hle (by positivity)
    have hcancel : 15 * (1 + t) ^ 3 * ((15 + 40 * t + 33 * t ^ 2) / (15 * (1 + t) ^ 3))
        = 15 + 40 * t + 33 * t ^ 2 := by
      field_simp
    linarith [hmul, hcancel]
  have hD : 8 * t ^ 3 * (1 + t) ^ 3 < 0 := by
    have h3 : t ^ 3 < 0 := Odd.pow_neg (by norm_num : Odd 3) ht0
    have h8 : 8 * t ^ 3 < 0 := by nlinarith [h3]
    have h1tp : (0 : ℝ) < 1 + t := by linarith
    have h1p : (0 : ℝ) < (1 + t) ^ 3 := by positivity
    exact mul_neg_of_neg_of_pos h8 h1p
  exact div_neg_of_pos_of_neg hN hD

/-- `matanDD` is strictly decreasing on `(-1, 0)`. -/
theorem lkB_matanDD_strictAntiOn_neg : StrictAntiOn matanDD (Set.Ioo (-1) 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo (-1) 0) ?_ ?_
  · intro x hx
    exact (lkB_matanDD_hasDerivAt hx.1 (ne_of_lt hx.2)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    exact lkB_matanDD_deriv_neg_of_neg hx.1 hx.2

/-! ## 4. The removable-singularity limit at `t = 0` -/

/-- **`matanDD t → 2/5` as `t → 0` (punctured)**: the landing identity
`matanDD t = -(3/(4t²))(1/(1+t) - matan t) - 1/(2t(1+t)²)` splits into the
pole-free rational function `(2/5 + t/20 + 3t²/20)/(1+t)²` plus the
`O(t)` remainder `(3/(4t²))·(matan t - (1 - t/3 + t²/5))`, which the landed
both-branch cubic bracket `nb12w_matan_bracket3` bounds by `|t|/7`. -/
theorem lkB_matanDD_tendsto_zero :
    Tendsto matanDD (𝓝[≠] (0 : ℝ)) (𝓝 (2 / 5)) := by
  have hEm : matanDD =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ => -((3 : ℝ) / (4 * t ^ 2)) * (1 / (1 + t) - matan t)
        - 1 / (2 * t * (1 + t) ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact matanDD_of_ne ht
  refine Tendsto.congr' hEm.symm ?_
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |t| < 1 / 4 := by
    filter_upwards [nhdsWithin_le_nhds
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))] with t ht
    have h := Metric.mem_ball.mp ht
    simpa [Real.dist_eq, sub_zero] using h
  have hSplit : (fun t : ℝ => -((3 : ℝ) / (4 * t ^ 2)) * (1 / (1 + t) - matan t)
        - 1 / (2 * t * (1 + t) ^ 2)) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun t : ℝ => (2 / 5 + t / 20 + 3 * t ^ 2 / 20) / (1 + t) ^ 2
        + (3 / (4 * t ^ 2)) * (matan t - (1 - t / 3 + t ^ 2 / 5))) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htab
    have ht0 : t ≠ 0 := by simpa using ht
    have h1t : (1 : ℝ) + t ≠ 0 := by
      intro hh
      have ht1 : |t| = 1 := by
        have : t = -1 := by linarith
        rw [this]
        norm_num
      linarith
    field_simp
    ring
  refine Tendsto.congr' hSplit.symm ?_
  have hF : Tendsto (fun t : ℝ => (2 / 5 + t / 20 + 3 * t ^ 2 / 20) / (1 + t) ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (2 / 5)) := by
    have hcont : ContinuousAt
        (fun t : ℝ => (2 / 5 + t / 20 + 3 * t ^ 2 / 20) / (1 + t) ^ 2) 0 := by
      refine ContinuousAt.div ?_ ?_ (by norm_num)
      · fun_prop
      · fun_prop
    have h0 : (2 / 5 + (0 : ℝ) / 20 + 3 * (0 : ℝ) ^ 2 / 20) / (1 + 0) ^ 2 = 2 / 5 := by
      norm_num
    have h := hcont.tendsto
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have herr : Tendsto
      (fun t : ℝ => (3 / (4 * t ^ 2)) * (matan t - (1 - t / 3 + t ^ 2 / 5)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
        ‖(3 / (4 * t ^ 2)) * (matan t - (1 - t / 3 + t ^ 2 / 5))‖ ≤ |t| / 7 := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htab
      have ht0 : t ≠ 0 := by simpa using ht
      have ht2p : (0 : ℝ) < t ^ 2 := by
        rcases lt_or_gt_of_ne ht0 with h | h <;> nlinarith
      have habs : |t| < 1 / 4 := htab
      obtain ⟨h1, h2⟩ := abs_lt.mp habs
      have hbr := nb12w_matan_bracket3 h1.le h2.le
      have h3 : |(3 : ℝ) / (4 * t ^ 2)| = 3 / (4 * t ^ 2) := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < 3 / (4 * t ^ 2))]
      rw [Real.norm_eq_abs, abs_mul, h3]
      have hstep : (3 : ℝ) / (4 * t ^ 2) * |matan t - (1 - t / 3 + t ^ 2 / 5)|
          ≤ 3 / (4 * t ^ 2) * (4 * |t| ^ 3 / 21) :=
        mul_le_mul_of_nonneg_left hbr (by positivity)
      have hval : (3 : ℝ) / (4 * t ^ 2) * (4 * |t| ^ 3 / 21) = |t| / 7 := by
        have hcube : |t| ^ 3 = |t| * t ^ 2 := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, sq_abs t]
          ring
        rw [hcube]
        field_simp
        ring
      linarith [hstep, hval]
    have hlim : Tendsto (fun t : ℝ => |t| / 7) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have hcont : Continuous fun t : ℝ => |t| / 7 := by fun_prop
      have h := hcont.tendsto (0 : ℝ)
      have h0 : |(0 : ℝ)| / 7 = 0 := by norm_num
      rw [h0] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm' hbound hlim
  have hsum := Tendsto.add hF herr
  simpa using hsum

/-- `matanDD` is continuous at `0` (the value `2/5` is the punctured limit). -/
theorem lkB_matanDD_continuousAt_zero : ContinuousAt matanDD 0 := by
  rw [Metric.continuousAt_iff, matanDD_zero]
  intro ε hε
  have hp : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), dist (matanDD t) (2 / 5) < ε :=
    (Metric.tendsto_nhds.mp lkB_matanDD_tendsto_zero) ε hε
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hp
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [matanDD_zero]
    simpa using hε
  · exact hsub ⟨by simpa [Real.dist_eq, sub_zero] using hx, hx0⟩

/-! ## 5. Antitonicity on the whole domain `(-1, ∞)` -/

/-- Value comparison at the crossing point, negative side:
`matanDD 0 ≤ matanDD x` for `-1 < x < 0` (the punctured limit squeezes from
the left where `matanDD` is decreasing). -/
theorem lkB_matanDD_zero_le_of_neg {x : ℝ} (hx1 : -1 < x) (hx0 : x < 0) :
    matanDD 0 ≤ matanDD x := by
  have hleft : Tendsto matanDD (𝓝[<] (0 : ℝ)) (𝓝 (2 / 5)) :=
    lkB_matanDD_tendsto_zero.mono_left (nhdsWithin_mono 0 (fun z hz => ne_of_lt hz))
  have hA : ∀ᶠ z : ℝ in 𝓝[<] (0 : ℝ), matanDD z ≤ matanDD x := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hx0)]
      with z hz0 hzx
    have hzx' : x < z := hzx
    have hz0' : z < 0 := hz0
    exact (lkB_matanDD_strictAntiOn_neg.antitoneOn
      (Set.mem_Ioo.mpr ⟨hx1, hx0⟩) (Set.mem_Ioo.mpr ⟨by linarith, hz0'⟩) hzx'.le)
  have h := le_of_tendsto hleft hA
  rw [matanDD_zero]
  exact h

/-- Value comparison at the crossing point, positive side:
`matanDD y ≤ matanDD 0` for `0 < y`. -/
theorem lkB_matanDD_le_zero_of_pos {y : ℝ} (hy0 : 0 < y) :
    matanDD y ≤ matanDD 0 := by
  have hright : Tendsto matanDD (𝓝[>] (0 : ℝ)) (𝓝 (2 / 5)) :=
    lkB_matanDD_tendsto_zero.mono_left (nhdsWithin_mono 0 (fun z hz => ne_of_gt hz))
  have hA : ∀ᶠ z : ℝ in 𝓝[>] (0 : ℝ), matanDD y ≤ matanDD z := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hy0)]
      with z hz0 hzy
    have hz0' : 0 < z := hz0
    have hzy' : z < y := hzy
    exact (matanDD_strictAntiOn_pos.antitoneOn
      (Set.mem_Ioi.mpr hz0') (Set.mem_Ioi.mpr hy0) hzy'.le)
  have h := ge_of_tendsto hright hA
  rw [matanDD_zero]
  exact h

/-- **`matanDD` is antitone on `(-1, ∞)`** — negative branch, positive branch
(landed), and the crossing point glued by the limit value `2/5`. -/
theorem lkB_matanDD_antitoneOn : AntitoneOn matanDD (Set.Ioi (-1)) := by
  intro x hx y hy hxy
  rw [Set.mem_Ioi] at hx hy
  rcases lt_trichotomy y 0 with hyneg | heqy | hypos
  · -- y < 0, hence x < 0
    rcases lt_or_eq_of_le hxy with hlt | heq
    · exact (lkB_matanDD_strictAntiOn_neg.antitoneOn
        (Set.mem_Ioo.mpr ⟨hx, lt_trans hlt hyneg⟩)
        (Set.mem_Ioo.mpr ⟨by linarith, hyneg⟩) hlt.le)
    · exact le_of_eq (by rw [heq])
  · -- y = 0
    rw [heqy]
    rcases lt_or_eq_of_le hxy with hlt | heq
    · have hlt0 : x < 0 := by rw [heqy] at hlt; exact hlt
      exact lkB_matanDD_zero_le_of_neg hx hlt0
    · exact le_of_eq (by rw [heq, heqy])
  · -- 0 < y
    rcases lt_trichotomy x 0 with hxneg | heqx | hxpos
    · -- x < 0 < y
      exact le_trans (lkB_matanDD_le_zero_of_pos hypos)
        (lkB_matanDD_zero_le_of_neg hx hxneg)
    · -- x = 0 < y
      rw [heqx]
      exact lkB_matanDD_le_zero_of_pos hypos
    · exact (matanDD_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr hxpos)
        (Set.mem_Ioi.mpr (lt_of_lt_of_le hxpos hxy)) hxy)

/-! ## 6. Transport products (generator interface) -/

/-- **Endpoint-coherent `matanDD` transport, whole domain**: for
`-1 < lo ≤ t ≤ hi`, `matanDD t` lies between the endpoint values in reverse
order.  Covers negative slots, zero-crossing slots and positive slots in one
statement (this is what `lkB_matanDD_ops_neg` cannot do: it needs
`TI.hi < 0`). -/
theorem lkB_matanDD_transport (lo hi t : ℝ) (hm : -1 < lo) (hlt : lo ≤ t)
    (htu : t ≤ hi) (Dl Dh : QInterval) (hDl : Dl.mem (matanDD lo))
    (hDh : Dh.mem (matanDD hi)) :
    (QInterval.mk Dh.lo Dl.hi).mem (matanDD t) := by
  have htm : -1 < t := lt_of_lt_of_le hm hlt
  have hhm : -1 < hi := lt_of_lt_of_le htm htu
  have h1 : matanDD hi ≤ matanDD t :=
    lkB_matanDD_antitoneOn (Set.mem_Ioi.mpr htm) (Set.mem_Ioi.mpr hhm) htu
  have h2 : matanDD t ≤ matanDD lo :=
    lkB_matanDD_antitoneOn (Set.mem_Ioi.mpr hm) (Set.mem_Ioi.mpr htm) hlt
  rw [QInterval.mem]
  exact ⟨le_trans hDh.1 h1, le_trans h2 hDl.2⟩

/-- Rational-slot form of `lkB_matanDD_transport`: exact-rational `t` interval
plus the two endpoint `matanDD` brackets give the slot's `matanDD` interval. -/
theorem lkB_matanDD_slot (TI : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (_horder : TI.lo ≤ TI.hi) (Dl Dh : QInterval)
    (hDl : Dl.mem (matanDD ((TI.lo : ℚ) : ℝ)))
    (hDh : Dh.mem (matanDD ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (QInterval.mk Dh.lo Dl.hi).mem (matanDD t) := by
  intro t h1t h2t
  exact lkB_matanDD_transport _ _ t (by exact_mod_cast hm) h1t h2t Dl Dh hDl hDh

/-- Exact-rational point bracket for `matanDD` built from a `matan` point
bracket at the **same** `tI` (generator-facing `lkB_matanDD_pt` instance). -/
def lkBDDpt (V : QInterval) (tI : ℚ) : QInterval :=
  (((QInterval.const (3 / (4 * tI * tI))).mul
      ((QInterval.const (1 / (1 + tI))).sub V)).neg).sub
    (QInterval.const (1 / (2 * tI * (1 + tI) ^ 2)))

theorem lkBDDpt_mem (V : QInterval) (tI : ℚ) (ht0 : tI ≠ 0)
    (hV : V.mem (matan ((tI : ℚ) : ℝ))) :
    (lkBDDpt V tI).mem (matanDD ((tI : ℚ) : ℝ)) :=
  lkB_matanDD_pt tI V ((QInterval.const (1 / (1 + tI))).sub V) (lkBDDpt V tI)
    ht0 hV rfl rfl

/-- Exact-rational point bracket for `matanDD` built from a `matanD` point
bracket at the same `tI` (the landed identity
`matanDD t = -(3/(2t))·matanD t - 1/(2t(1+t)²)` as rectangle arithmetic). -/
def lkBDDpt_of_matanD (MD : QInterval) (tI : ℚ) : QInterval :=
  ((QInterval.const (-(3 / (2 * tI)))).mul MD).sub
    (QInterval.const (1 / (2 * tI * (1 + tI) ^ 2)))

theorem lkBDDpt_of_matanD_mem (MD : QInterval) (tI : ℚ) (ht0 : tI ≠ 0)
    (hMD : MD.mem (matanD ((tI : ℚ) : ℝ))) :
    (lkBDDpt_of_matanD MD tI).mem (matanDD ((tI : ℚ) : ℝ)) := by
  have ht0r : ((tI : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ht0
  rw [matanDD_eq_matanD_of_ne ht0r]
  have hcast1 : ((-(3 / (2 * tI)) : ℚ) : ℝ) = -(3 / (2 * ((tI : ℚ) : ℝ))) := by
    push_cast
    ring
  have hcast2 : ((1 / (2 * tI * (1 + tI) ^ 2) : ℚ) : ℝ)
      = 1 / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2) := by
    push_cast
    ring
  have hc1 : (QInterval.const (-(3 / (2 * tI)))).mem (-(3 / (2 * ((tI : ℚ) : ℝ)))) := by
    have h := QInterval.mem_const (q := (-(3 / (2 * tI)) : ℚ))
    rwa [hcast1] at h
  have hc2 : (QInterval.const (1 / (2 * tI * (1 + tI) ^ 2))).mem
      (1 / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2)) := by
    have h := QInterval.mem_const (q := (1 / (2 * tI * (1 + tI) ^ 2) : ℚ))
    rwa [hcast2] at h
  exact QInterval.mem_sub (QInterval.mem_mul hc1 hMD) hc2

/-- **Generator-facing zero-crossing-ready slot theorem** (`matan` brackets
in → `matanDD` interval out), same-endpoint pairing `Vl ↔ TI.lo`,
`Vh ↔ TI.hi`.  No sign condition on `TI`; only `-1 < TI.lo`. -/
theorem lkB_matanDD_slot_from_matan (TI Vl Vh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi) (hl0 : TI.lo ≠ 0) (hh0 : TI.hi ≠ 0)
    (hVl : Vl.mem (matan ((TI.lo : ℚ) : ℝ)))
    (hVh : Vh.mem (matan ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (QInterval.mk (lkBDDpt Vh TI.hi).lo (lkBDDpt Vl TI.lo).hi).mem (matanDD t) :=
  lkB_matanDD_slot TI hm horder (lkBDDpt Vl TI.lo) (lkBDDpt Vh TI.hi)
    (lkBDDpt_mem Vl TI.lo hl0 hVl) (lkBDDpt_mem Vh TI.hi hh0 hVh)

/-- Slot theorem from `matanD` endpoint brackets (same interface, `matanD`
data instead of `matan` data). -/
theorem lkB_matanDD_slot_from_matanD (TI MDl MDh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi) (hl0 : TI.lo ≠ 0) (hh0 : TI.hi ≠ 0)
    (hMDl : MDl.mem (matanD ((TI.lo : ℚ) : ℝ)))
    (hMDh : MDh.mem (matanD ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (QInterval.mk (lkBDDpt_of_matanD MDh TI.hi).lo
        (lkBDDpt_of_matanD MDl TI.lo).hi).mem (matanDD t) :=
  lkB_matanDD_slot TI hm horder (lkBDDpt_of_matanD MDl TI.lo)
    (lkBDDpt_of_matanD MDh TI.hi)
    (lkBDDpt_of_matanD_mem MDl TI.lo hl0 hMDl)
    (lkBDDpt_of_matanD_mem MDh TI.hi hh0 hMDh)

/-- `matanDD` at the removable singularity, as a point bracket (the
zero-endpoint value used when a leaf is split at `0`). -/
theorem lkBDD_zero_mem : (QInterval.const (2 / 5)).mem (matanDD 0) := by
  rw [matanDD_zero]
  simpa using QInterval.mem_const (q := (2 / 5 : ℚ))

/-- Zero-split convenience: a slot `[tlo, 0]` ending at the singularity. -/
theorem lkB_matanDD_slot_zero_hi (TI Vl : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (horder : TI.lo ≤ TI.hi) (hhi : TI.hi = 0) (hl0 : TI.lo ≠ 0)
    (hVl : Vl.mem (matan ((TI.lo : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ 0 →
      (QInterval.mk (2 / 5) (lkBDDpt Vl TI.lo).hi).mem (matanDD t) := by
  have hDh : (QInterval.const (2 / 5)).mem (matanDD ((TI.hi : ℚ) : ℝ)) := by
    rw [hhi]
    simpa using lkBDD_zero_mem
  have h := lkB_matanDD_slot TI hm horder (lkBDDpt Vl TI.lo) (QInterval.const (2 / 5))
    (lkBDDpt_mem Vl TI.lo hl0 hVl) hDh
  intro t h1t h2t
  refine h t h1t ?_
  rw [hhi]
  simpa using h2t

/-- Zero-split convenience: a slot `[0, thi]` starting at the singularity. -/
theorem lkB_matanDD_slot_zero_lo (TI Vh : QInterval) (hlo : TI.lo = 0)
    (horder : 0 ≤ TI.hi) (hh0 : TI.hi ≠ 0)
    (hVh : Vh.mem (matan ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, 0 ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (QInterval.mk (lkBDDpt Vh TI.hi).lo (2 / 5)).mem (matanDD t) := by
  have hm : (-1 : ℚ) < TI.lo := by rw [hlo]; norm_num
  have hDl : (QInterval.const (2 / 5)).mem (matanDD ((TI.lo : ℚ) : ℝ)) := by
    rw [hlo]
    simpa using lkBDD_zero_mem
  have h := lkB_matanDD_slot TI hm (by rw [hlo]; exact horder) (QInterval.const (2 / 5))
    (lkBDDpt Vh TI.hi) hDl (lkBDDpt_mem Vh TI.hi hh0 hVh)
  intro t h1t h2t
  refine h t ?_ h2t
  rw [hlo]
  simpa using h1t

/-! ## 7. Monotonicity-free fallback (landed `lkB_matanDD_ops_neg` on slots) -/

/-- The `lkB_matanDD_ops_neg` slot expression as a named constructor
(exact-rational interval, no monotonicity assumption). -/
def lkBddOpsNeg (TI VI : QInterval) : QInterval :=
  (((QInterval.mk (3 / (4 * TI.lo * TI.lo)) (3 / (4 * TI.hi * TI.hi))).mul
      (((QInterval.const (1 : ℚ)).add TI).inv.sub VI)).neg).sub
    ((((QInterval.const (2 : ℚ)).mul TI).inv.mul
      ((QInterval.const (1 : ℚ)).add TI).inv).mul
      ((QInterval.const (1 : ℚ)).add TI).inv)

/-- **Monotonicity-free negative-slot `matanDD` bracket, endpoint-coherent**:
`matan` brackets at the endpoints of a slot with `TI.hi < 0` in, `matanDD`
interval out (landed `lkB_matanDD_ops_neg` fed by the landed
`lkB_matan_neg_slot`).  Sound on the whole slot with no `matanDD`
monotonicity input; kept as the independent fallback (wider, see
`scripts/probe_dd_neg.py` S6). -/
theorem lkB_matanDD_ops_neg_slot (TI Vl Vh : QInterval) (hm : (-1 : ℚ) < TI.lo)
    (hneg : TI.hi < 0) (horder : TI.lo ≤ TI.hi)
    (hVl : Vl.mem (matan ((TI.lo : ℚ) : ℝ)))
    (hVh : Vh.mem (matan ((TI.hi : ℚ) : ℝ))) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      (lkBddOpsNeg TI (QInterval.mk Vh.lo Vl.hi)).mem (matanDD t) := by
  intro t h1t h2t
  exact lkB_matanDD_ops_neg TI (QInterval.mk Vh.lo Vl.hi) hm hneg horder
    (lkB_matan_neg_slot TI hm hneg.le Vl Vh hVl hVh) t h1t h2t

/-! ## Axiom audit (standard three only: propext / Classical.choice / Quot.sound) -/

#print axioms lkB_matanDD_hasDerivAt
#print axioms lkB_matan_le_rat_neg
#print axioms lkB_matanDD_deriv_neg_of_neg
#print axioms lkB_matanDD_strictAntiOn_neg
#print axioms lkB_matanDD_tendsto_zero
#print axioms lkB_matanDD_continuousAt_zero
#print axioms lkB_matanDD_zero_le_of_neg
#print axioms lkB_matanDD_le_zero_of_pos
#print axioms lkB_matanDD_antitoneOn
#print axioms lkB_matanDD_transport
#print axioms lkB_matanDD_slot
#print axioms lkBDDpt_mem
#print axioms lkBDDpt_of_matanD_mem
#print axioms lkB_matanDD_slot_from_matan
#print axioms lkB_matanDD_slot_from_matanD
#print axioms lkBDD_zero_mem
#print axioms lkB_matanDD_slot_zero_hi
#print axioms lkB_matanDD_slot_zero_lo
#print axioms lkB_matanDD_ops_neg_slot
#print axioms lkBDDpt
#print axioms lkBDDpt_of_matanD
#print axioms lkBddOpsNeg

end Kepler.Text.TaylorSecond
