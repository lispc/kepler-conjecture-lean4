/-
Kepler.Text.Wt1TowerKit — lane `cell3-wt1-tower-build-w1` (2026-11-20),
phase 1 of the wt1 second-order tower (route A′), piece 2 of 3:
the `matan` derivative kit up to second order.

Mathematical content (SCOUT.md §1.5, §3.2):
* `matanD` / `matanDD`: the clean algebraic forms of `matan'` and `matan''`,
  `matanD t = (1/(2t)) * (1/(1+t) - matan t)` and
  `matanDD t = -(3/(4t^2)) * (1/(1+t) - matan t) - 1/(2t(1+t)^2)` for `t ≠ 0`,
  with the removable-singularity values `-1/3` resp. `2/5` at `t = 0`
  (`NliBanks12`/`NliBanks13` supply the three-branch first derivative in a
  different algebraic shape; `matanD_eq_deriv` bridges the two);
* `matan_hasDerivAt` (repackaging of `nb13_hasDerivAt_matan`) and the new
  second-order statement `matanD_hasDerivAt : HasDerivAt matanD (matanDD t) t`
  for every `t > -1`;
* the `t = 0` second derivative is a genuine squeeze argument: the cubic
  bracket `|matan t - (1 - t/3 + t^2/5)| ≤ (4/21)|t|^3` (both signs, via the
  order-7 alternating arctan/artanh brackets).  The `|t| < 1` series is
  one-sided-neutral: `matan t = Σ (-t)^n/(2n+1)`; the two branches differ
  only from the cubic term on, which is why the cubic bracket needs both
  the positive-branch `-t^3/7` tail and the negative-branch `4|t|^3/21` tail;
* `matanD_neg` / `nb12w_matan_strictAntiOn`: `matan` is strictly decreasing
  on `(-1, ∞)` (its derivative `matanD` is strictly negative there), the
  monotonicity input of the phase-2 slot certificates.

Value brackets for `matan` at `|t| > 1/4` (the "large-argument closed form
plus pi" range, e.g. `g_C ≤ 8.22`) are NOT in this file: they are
certificate-layer data (P1), generated in phase 2 from the same closed
forms (`matan t = arctan(√t)/√t` with `arctan s = π/2 - arctan(1/s)`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.NliBanks13

set_option maxHeartbeats 4000000

namespace Kepler.Text
open Kepler.NliBanks12
open Kepler.NliBanks13
open Filter
open scoped Topology

/-! ## 1. The clean algebraic forms of `matan'` and `matan''` -/

/-- Clean form of `matan'`: `(1/(2t)) * (1/(1+t) - matan t)` for `t ≠ 0`,
continuation `-1/3` at `0`. -/
noncomputable def matanD (t : ℝ) : ℝ :=
  if t = 0 then -(1 / 3) else (1 / (2 * t)) * (1 / (1 + t) - matan t)

/-- Clean form of `matan''`:
`-(3/(4t^2)) * (1/(1+t) - matan t) - 1/(2t(1+t)^2)` for `t ≠ 0`,
continuation `2/5` at `0`. -/
noncomputable def matanDD (t : ℝ) : ℝ :=
  if t = 0 then 2 / 5
  else -((3 : ℝ) / (4 * t ^ 2)) * (1 / (1 + t) - matan t) - 1 / (2 * t * (1 + t) ^ 2)

theorem matanD_zero : matanD 0 = -(1 / 3) := by
  unfold matanD
  rw [if_pos rfl]

theorem matanD_of_ne {t : ℝ} (ht : t ≠ 0) :
    matanD t = (1 / (2 * t)) * (1 / (1 + t) - matan t) := by
  unfold matanD
  rw [if_neg ht]

theorem matanDD_zero : matanDD 0 = 2 / 5 := by
  unfold matanDD
  rw [if_pos rfl]

theorem matanDD_of_ne {t : ℝ} (ht : t ≠ 0) :
    matanDD t = -((3 : ℝ) / (4 * t ^ 2)) * (1 / (1 + t) - matan t) -
      1 / (2 * t * (1 + t) ^ 2) := by
  unfold matanDD
  rw [if_neg ht]

/-- Bridge to the three-branch `NliBanks13` form (`= matanDeriv`). -/
theorem matanD_eq_deriv {t : ℝ} (ht : -1 < t) : matanD t = matanDeriv t := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [matanD_of_ne (ne_of_lt h), nb13_matanDeriv_neg h]
    have hpos : (0 : ℝ) < -t := by linarith
    unfold matan
    rw [if_neg (ne_of_lt h), if_neg (not_lt.mpr h.le)]
    unfold matanDerivNeg
    set s := Real.sqrt (-t) with hsdef
    have hs : s ≠ 0 := by
      rw [hsdef]
      exact Real.sqrt_ne_zero'.mpr hpos
    have hs2 : s ^ 2 = -t := by
      rw [hsdef]
      exact Real.sq_sqrt hpos.le
    have hs1 : (1 : ℝ) - s ^ 2 ≠ 0 := by
      have hlt : s ^ 2 < 1 := by rw [hs2]; linarith
      intro hh; linarith
    have ht' : t = -(s ^ 2) := by linarith
    rw [ht']
    field_simp [hs, hs1]
    ring
  · subst h
    rw [matanD_zero, nb13_matanDeriv_zero]
  · rw [matanD_of_ne (ne_of_gt h), nb13_matanDeriv_pos h]
    have hpos : (0 : ℝ) < t := h
    unfold matan
    rw [if_neg (ne_of_gt h), if_pos h]
    unfold matanDerivPos
    set s := Real.sqrt t with hsdef
    have hs : s ≠ 0 := by
      rw [hsdef]
      exact Real.sqrt_ne_zero'.mpr hpos
    have hs2 : s ^ 2 = t := by
      rw [hsdef]
      exact Real.sq_sqrt h.le
    have ht' : t = s ^ 2 := by linarith
    rw [ht']
    field_simp [hs]

/-- **First derivative of `matan` in clean form**, for every `t > -1`. -/
theorem matan_hasDerivAt {t : ℝ} (ht : -1 < t) : HasDerivAt matan (matanD t) t := by
  rw [matanD_eq_deriv ht]
  exact nb13_hasDerivAt_matan ht

/-! ## 2. Order-7 series brackets for the cubic `matan` bracket -/

/-- `s - s³/3 + s⁵/5 - s⁷/7 ≤ arctan s` for `s ≥ 0` (alternating series,
truncation after the negative term; derivative of the gap is `s⁸/(1+s²)`). -/
theorem nb12w_arctan_ge_sub7 {s : ℝ} (hs : 0 ≤ s) :
    s - s ^ 3 / 3 + s ^ 5 / 5 - s ^ 7 / 7 ≤ Real.arctan s := by
  have h := nb12_nonneg_of_deriv
    (f := fun x : ℝ => Real.arctan x - x + x ^ 3 / 3 - x ^ 5 / 5 + x ^ 7 / 7)
    (hC := ((Real.continuous_arctan.sub continuous_id).add
      ((continuous_pow 3).div_const 3)).sub ((continuous_pow 5).div_const 5) |>.add
        ((continuous_pow 7).div_const 7))
    (hD := ((Real.differentiable_arctan.sub differentiable_id).add
      ((differentiable_pow 3).div_const 3)).sub ((differentiable_pow 5).div_const 5) |>.add
        ((differentiable_pow 7).div_const 7))
    (h0 := by norm_num)
    (hd := by
      intro x _
      have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
        have := (hasDerivAt_pow 3 x).div_const 3
        simpa [pow_succ] using this
      have h5 : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (x ^ 4) x := by
        have := (hasDerivAt_pow 5 x).div_const 5
        simpa [pow_succ] using this
      have h7 : HasDerivAt (fun y : ℝ => y ^ 7 / 7) (x ^ 6) x := by
        have := (hasDerivAt_pow 7 x).div_const 7
        simpa [pow_succ] using this
      have hderiv : HasDerivAt
          (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3 - y ^ 5 / 5 + y ^ 7 / 7)
          (1 / (1 + x ^ 2) - 1 + x ^ 2 - x ^ 4 + x ^ 6) x :=
        (((Real.hasDerivAt_arctan x).sub (hasDerivAt_id x)).add h3).sub h5 |>.add h7
      rw [hderiv.deriv]
      have : 1 / (1 + x ^ 2) - 1 + x ^ 2 - x ^ 4 + x ^ 6 = x ^ 8 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity) s hs
  linarith

/-- `s + s³/3 + s⁵/5 ≤ log((1+s)/(1-s))/2` for `0 ≤ s < 1` (all-positive
series, truncation after the order-5 term; derivative of the gap is
`s⁶/(1-s²)`). -/
theorem nb12w_artanh_ge_sub5 {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    s + s ^ 3 / 3 + s ^ 5 / 5 ≤ Real.log ((1 + s) / (1 - s)) / 2 := by
  have hcont : ContinuousOn
      (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2 - u - u ^ 3 / 3 - u ^ 5 / 5)
      (Set.Icc 0 s) := by
    have hlog := nb12_continuousOn_logRatio (s := s) hs1
    have hp1 : ContinuousOn (fun u : ℝ => u) (Set.Icc 0 s) := continuous_id.continuousOn
    have hp3 : ContinuousOn (fun u : ℝ => u ^ 3 / 3) (Set.Icc 0 s) := by fun_prop
    have hp5 : ContinuousOn (fun u : ℝ => u ^ 5 / 5) (Set.Icc 0 s) := by fun_prop
    exact ((hlog.sub hp1).sub hp3).sub hp5
  have hdiff : ∀ u ∈ Set.Ioo (0 : ℝ) s,
      HasDerivAt
        (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2 - u - u ^ 3 / 3 - u ^ 5 / 5)
        (u ^ 6 / (1 - u ^ 2)) u := by
    intro u hu
    have hu1 : u < 1 := lt_trans hu.2 hs1
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (u ^ 2) u := by
      have := (hasDerivAt_pow 3 u).div_const 3
      simpa [pow_succ] using this
    have h5 : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (u ^ 4) u := by
      have := (hasDerivAt_pow 5 u).div_const 5
      simpa [pow_succ] using this
    have := ((nb12_hasDerivAt_artanh (ne_of_lt hu1)
      (ne_of_gt (by linarith [hu.1] : (-1 : ℝ) < u))).sub (hasDerivAt_id u)).sub h3 |>.sub h5
    refine this.congr_deriv ?_
    have hlt : u ^ 2 < 1 := by
      have h1 : u * u < 1 * u := mul_lt_mul_of_pos_right hu1 hu.1
      nlinarith [h1, hu1]
    have hu2 : (1 : ℝ) - u ^ 2 ≠ 0 := by
      intro hh; nlinarith
    field_simp
    ring
  have hmono : MonotoneOn
      (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2 - u - u ^ 3 / 3 - u ^ 5 / 5)
      (Set.Icc 0 s) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 s) hcont ?_ ?_
    · intro u hu
      rw [interior_Icc] at hu
      exact (hdiff u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu1 : u < 1 := lt_trans hu.2 hs1
      rw [(hdiff u hu).deriv]
      have hd : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [hu.1, hu1]
      positivity
  have h0 : (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2 - u - u ^ 3 / 3 - u ^ 5 / 5)
      0 = 0 := by norm_num
  have := hmono (Set.mem_Icc.mpr ⟨le_rfl, hs⟩) (Set.mem_Icc.mpr ⟨hs, le_rfl⟩) hs
  rw [h0] at this
  linarith

/-- `log((1+s)/(1-s))/2 ≤ s + s³/3 + s⁵/5 + s⁷/(7(1-s²))` for `0 ≤ s < 1`
(the residual of the all-positive series is bounded by the geometric tail
`s⁷/(7(1-s²))`; derivative of the gap is `2s⁸/(7(1-s²)²)`). -/
theorem nb12w_artanh_le_sub7 {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    Real.log ((1 + s) / (1 - s)) / 2 ≤
      s + s ^ 3 / 3 + s ^ 5 / 5 + s ^ 7 / (7 * (1 - s ^ 2)) := by
  have hcont : ContinuousOn
      (fun u : ℝ => u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / (7 * (1 - u ^ 2)) -
        Real.log ((1 + u) / (1 - u)) / 2)
      (Set.Icc 0 s) := by
    have hlog := nb12_continuousOn_logRatio (s := s) hs1
    have hpoly : ContinuousOn (fun u : ℝ => u + u ^ 3 / 3 + u ^ 5 / 5) (Set.Icc 0 s) := by
      fun_prop
    have hrat : ContinuousOn (fun u : ℝ => u ^ 7 / (7 * (1 - u ^ 2))) (Set.Icc 0 s) := by
      refine ContinuousOn.div (continuous_pow 7).continuousOn ?_ ?_
      · have hden : Continuous (fun u : ℝ => 7 * (1 - u ^ 2)) := by
          have h2 : Continuous fun u : ℝ => u ^ 2 := continuous_pow 2
          exact continuous_const.mul (continuous_const.sub h2)
        exact hden.continuousOn
      · intro u hu
        have hlt : u < 1 := lt_of_le_of_lt hu.2 hs1
        have hpos : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [hu.1, hlt]
        have h7 : (0 : ℝ) < 7 * (1 - u ^ 2) := by nlinarith [hpos]
        exact ne_of_gt h7
    exact (hpoly.add hrat).sub hlog
  have hdiff : ∀ u ∈ Set.Ioo (0 : ℝ) s,
      HasDerivAt
        (fun u : ℝ => u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / (7 * (1 - u ^ 2)) -
          Real.log ((1 + u) / (1 - u)) / 2)
        (2 * u ^ 8 / (7 * (1 - u ^ 2) ^ 2)) u := by
    intro u hu
    have hu1 : u < 1 := lt_trans hu.2 hs1
    have hden0 : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [hu.1, hu1]
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (u ^ 2) u := by
      have := (hasDerivAt_pow 3 u).div_const 3
      simpa [pow_succ] using this
    have h5 : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (u ^ 4) u := by
      have := (hasDerivAt_pow 5 u).div_const 5
      simpa [pow_succ] using this
    have hnum7 : HasDerivAt (fun y : ℝ => y ^ 7) (7 * u ^ 6) u := by
      have := hasDerivAt_pow 7 u
      simpa using this
    have hd2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
      have := hasDerivAt_pow 2 u
      simpa [pow_one, mul_comm] using this
    have hden7 : HasDerivAt (fun y : ℝ => 7 * (1 - y ^ 2)) (-(14 * u)) u := by
      have h : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * u)) u := by
        have hs1' := (hasDerivAt_const u (1 : ℝ)).sub hd2
        have hfun : ((fun _ : ℝ => (1 : ℝ)) - (fun y : ℝ => y ^ 2))
            = fun y : ℝ => 1 - y ^ 2 := by
          funext y; simp
        rw [hfun] at hs1'
        have hder : (0 : ℝ) - 2 * u = -(2 * u) := by ring
        rw [hder] at hs1'
        exact hs1'
      have hc : HasDerivAt (fun _ : ℝ => (7 : ℝ)) 0 u := hasDerivAt_const u 7
      have hm := hc.mul h
      have hfun : ((fun _ : ℝ => (7 : ℝ)) * (fun y : ℝ => (1 - y ^ 2)))
          = fun y : ℝ => 7 * (1 - y ^ 2) := by
        funext y; simp
      rw [hfun] at hm
      refine hm.congr_deriv ?_
      ring
    have hden_ne : (7 : ℝ) * (1 - u ^ 2) ≠ 0 := by
      have hpos : (0 : ℝ) < 1 - u ^ 2 := by nlinarith [hu.1, hu1]
      positivity
    have h7 : HasDerivAt (fun y : ℝ => y ^ 7 / (7 * (1 - y ^ 2)))
        (((7 * u ^ 6) * (7 * (1 - u ^ 2)) - u ^ 7 * (-(14 * u))) /
          (7 * (1 - u ^ 2)) ^ 2) u :=
      hnum7.div hden7 hden_ne
    have hall := ((((hasDerivAt_id u).add h3).add h5).add h7).sub
      (nb12_hasDerivAt_artanh (ne_of_lt hu1)
        (ne_of_gt (by linarith [hu.1] : (-1 : ℝ) < u)))
    refine hall.congr_deriv ?_
    have h1u2 : (1 : ℝ) - u ^ 2 ≠ 0 := by positivity
    have h7u2 : (7 : ℝ) * (1 - u ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have hmono : MonotoneOn
      (fun u : ℝ => u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / (7 * (1 - u ^ 2)) -
        Real.log ((1 + u) / (1 - u)) / 2)
      (Set.Icc 0 s) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 s) hcont ?_ ?_
    · intro u hu
      rw [interior_Icc] at hu
      exact (hdiff u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu1 : u < 1 := lt_trans hu.2 hs1
      rw [(hdiff u hu).deriv]
      have hu2 : u ^ 2 < 1 := by
        have h1 : u * u < 1 * u := mul_lt_mul_of_pos_right hu1 hu.1
        nlinarith [h1, hu1]
      have hden : (0 : ℝ) < 7 * (1 - u ^ 2) ^ 2 := by nlinarith [hu2]
      positivity
  have h0 : (fun u : ℝ => u + u ^ 3 / 3 + u ^ 5 / 5 + u ^ 7 / (7 * (1 - u ^ 2)) -
      Real.log ((1 + u) / (1 - u)) / 2) 0 = 0 := by norm_num
  have := hmono (Set.mem_Icc.mpr ⟨le_rfl, hs⟩) (Set.mem_Icc.mpr ⟨hs, le_rfl⟩) hs
  rw [h0] at this
  linarith

/-! ## 3. Cubic bracket for `matan` on `|t| ≤ 1/4` -/

/-- Positive-branch cubic two-sided bracket. -/
theorem nb12w_matan_pos_bracket3 {t : ℝ} (ht : 0 < t) :
    1 - t / 3 + t ^ 2 / 5 - t ^ 3 / 7 ≤ matan t ∧ matan t ≤ 1 - t / 3 + t ^ 2 / 5 := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hs3 : (Real.sqrt t) ^ 3 = Real.sqrt t * t := by
    calc (Real.sqrt t) ^ 3 = Real.sqrt t * Real.sqrt t ^ 2 := by ring
      _ = Real.sqrt t * t := by rw [hs2]
  have hs5 : (Real.sqrt t) ^ 5 = Real.sqrt t * t ^ 2 := by
    calc (Real.sqrt t) ^ 5 = Real.sqrt t * (Real.sqrt t ^ 2) ^ 2 := by ring
      _ = Real.sqrt t * t ^ 2 := by rw [hs2]
  have hs7 : (Real.sqrt t) ^ 7 = Real.sqrt t * t ^ 3 := by
    calc (Real.sqrt t) ^ 7 = Real.sqrt t * (Real.sqrt t ^ 2) ^ 3 := by ring
      _ = Real.sqrt t * t ^ 3 := by rw [hs2]
  unfold matan
  rw [if_neg (ne_of_gt ht), if_pos ht, div_le_iff₀ hs, le_div_iff₀ hs]
  constructor
  · have hge : Real.sqrt t - Real.sqrt t ^ 3 / 3 + Real.sqrt t ^ 5 / 5 -
        Real.sqrt t ^ 7 / 7 ≤ Real.arctan (Real.sqrt t) := nb12w_arctan_ge_sub7 hs.le
    rw [hs3, hs5, hs7] at hge
    calc (1 - t / 3 + t ^ 2 / 5 - t ^ 3 / 7) * Real.sqrt t
        = Real.sqrt t - Real.sqrt t * t / 3 + Real.sqrt t * t ^ 2 / 5
            - Real.sqrt t * t ^ 3 / 7 := by ring
      _ ≤ Real.arctan (Real.sqrt t) := hge
  · have hle : Real.arctan (Real.sqrt t) ≤ Real.sqrt t - Real.sqrt t ^ 3 / 3 +
        (Real.sqrt t) ^ 5 / 5 := nb12_arctan_le_sub5 hs.le
    rw [hs3, hs5] at hle
    calc Real.arctan (Real.sqrt t)
        ≤ Real.sqrt t - Real.sqrt t * t / 3 + Real.sqrt t * t ^ 2 / 5 := hle
      _ = (1 - t / 3 + t ^ 2 / 5) * Real.sqrt t := by ring

/-- Negative-branch cubic two-sided bracket (upper tail in `|t|`). -/
theorem nb12w_matan_neg_bracket3 {t : ℝ} (ht : t < 0) (ht4 : -(1 / 4) ≤ t) :
    1 - t / 3 + t ^ 2 / 5 ≤ matan t ∧
      matan t ≤ 1 - t / 3 + t ^ 2 / 5 + 4 * |t| ^ 3 / 21 := by
  have hpos : (0 : ℝ) < -t := by linarith
  have hs : (0 : ℝ) < Real.sqrt (-t) := Real.sqrt_pos.mpr hpos
  have hs2 : Real.sqrt (-t) ^ 2 = -t := Real.sq_sqrt hpos.le
  have hsle : Real.sqrt (-t) ≤ 1 / 2 := by
    have h1 : -t ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (-t) ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 1 / 2 := by
        rw [show ((1 / 2 : ℝ) ^ 2) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs1 : Real.sqrt (-t) < 1 := by linarith
  have hs3 : (Real.sqrt (-t)) ^ 3 = Real.sqrt (-t) * (-t) := by
    calc (Real.sqrt (-t)) ^ 3 = Real.sqrt (-t) * Real.sqrt (-t) ^ 2 := by ring
      _ = Real.sqrt (-t) * (-t) := by rw [hs2]
  have hs5 : (Real.sqrt (-t)) ^ 5 = Real.sqrt (-t) * t ^ 2 := by
    calc (Real.sqrt (-t)) ^ 5 = Real.sqrt (-t) * (Real.sqrt (-t) ^ 2) ^ 2 := by ring
      _ = Real.sqrt (-t) * t ^ 2 := by rw [hs2]; ring
  have hs7 : (Real.sqrt (-t)) ^ 7 = -(Real.sqrt (-t) * t ^ 3) := by
    calc (Real.sqrt (-t)) ^ 7 = Real.sqrt (-t) * (Real.sqrt (-t) ^ 2) ^ 3 := by ring
      _ = Real.sqrt (-t) * (-t) ^ 3 := by rw [hs2]
      _ = -(Real.sqrt (-t) * t ^ 3) := by ring
  have hL := nb12w_artanh_ge_sub5 hs.le hs1
  have hU := nb12w_artanh_le_sub7 hs.le hs1
  rw [hs3, hs5] at hL
  rw [hs3, hs5, hs7] at hU
  have htabs : |t| = -t := abs_of_neg ht
  unfold matan
  rw [if_neg (ne_of_lt ht), if_neg (not_lt.mpr ht.le)]
  constructor
  · rw [show Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / (2 * Real.sqrt (-t))
        = (Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2) / Real.sqrt (-t) by
      field_simp]
    rw [le_div_iff₀ hs]
    calc (1 - t / 3 + t ^ 2 / 5) * Real.sqrt (-t)
        = Real.sqrt (-t) + Real.sqrt (-t) * (-t) / 3 + Real.sqrt (-t) * t ^ 2 / 5 := by ring
      _ ≤ Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2 := hL
  · rw [show Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / (2 * Real.sqrt (-t))
        = (Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2) / Real.sqrt (-t) by
      field_simp]
    rw [div_le_iff₀ hs]
    have htail : -(Real.sqrt (-t) * t ^ 3) / (7 * (1 - Real.sqrt (-t) ^ 2)) ≤
        (4 * |t| ^ 3 / 21) * Real.sqrt (-t) := by
      have hs0 : (0 : ℝ) ≤ Real.sqrt (-t) := Real.sqrt_nonneg (-t)
      have h1t : (0 : ℝ) < 1 + t := by linarith
      have hden : (0 : ℝ) < 7 * (1 + t) := by positivity
      have hden_eq : (1 : ℝ) - Real.sqrt (-t) ^ 2 = 1 + t := by rw [hs2]; ring
      rw [hden_eq, htabs]
      have hleft : -(Real.sqrt (-t) * t ^ 3) = Real.sqrt (-t) * (-t) ^ 3 := by
        rw [show (-t) ^ 3 = -(t ^ 3) by ring]; ring
      rw [hleft]
      rw [show (4 * (-t) ^ 3 / 21) * Real.sqrt (-t)
          = Real.sqrt (-t) * (-t) ^ 3 * (4 / 21) by ring]
      rw [div_le_iff₀ hden]
      have hcoef : (1 : ℝ) ≤ (4 / 21) * (7 * (1 + t)) := by linarith
      have hprod : Real.sqrt (-t) * (-t) ^ 3
          ≤ Real.sqrt (-t) * (-t) ^ 3 * ((4 / 21) * (7 * (1 + t))) := by
        calc Real.sqrt (-t) * (-t) ^ 3 = Real.sqrt (-t) * (-t) ^ 3 * 1 := by ring
          _ ≤ Real.sqrt (-t) * (-t) ^ 3 * ((4 / 21) * (7 * (1 + t))) :=
              mul_le_mul_of_nonneg_left hcoef (by positivity)
      rw [show Real.sqrt (-t) * (-t) ^ 3 * (4 / 21) * (7 * (1 + t))
          = Real.sqrt (-t) * (-t) ^ 3 * ((4 / 21) * (7 * (1 + t))) by ring]
      exact hprod
    calc Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2
        ≤ Real.sqrt (-t) + Real.sqrt (-t) * (-t) / 3 + Real.sqrt (-t) * t ^ 2 / 5
            + (-(Real.sqrt (-t) * t ^ 3) / (7 * (1 - Real.sqrt (-t) ^ 2))) := hU
      _ ≤ Real.sqrt (-t) + Real.sqrt (-t) * (-t) / 3 + Real.sqrt (-t) * t ^ 2 / 5
            + (4 * |t| ^ 3 / 21) * Real.sqrt (-t) := by linarith [htail]
      _ = (1 - t / 3 + t ^ 2 / 5 + 4 * |t| ^ 3 / 21) * Real.sqrt (-t) := by ring

/-- **`matan` cubic bracket** (both branches, `|t| ≤ 1/4`):
`|matan t - (1 - t/3 + t^2/5)| ≤ (4/21)·|t|³`. -/
theorem nb12w_matan_bracket3 {t : ℝ} (ht : -(1 / 4) ≤ t) (ht' : t ≤ 1 / 4) :
    |matan t - (1 - t / 3 + t ^ 2 / 5)| ≤ 4 * |t| ^ 3 / 21 := by
  rcases lt_trichotomy t 0 with h | h | h
  · obtain ⟨h1, h2⟩ := nb12w_matan_neg_bracket3 h ht
    rw [abs_le]
    constructor <;> linarith
  · subst h
    unfold matan
    rw [if_pos rfl]
    norm_num
  · obtain ⟨h1, h2⟩ := nb12w_matan_pos_bracket3 h
    have h3 : t ^ 3 / 7 ≤ 4 * |t| ^ 3 / 21 := by
      rw [abs_of_pos h]; nlinarith
    rw [abs_le]
    constructor <;> nlinarith [h1, h2, h3, abs_nonneg t]

/-! ## 4. The second derivative at `t = 0` -/

/-- Slope bound for `matanD` at `0`: on `|y| ≤ 1/4`, `y ≠ 0`,
`|(matanD y - matanD 0)/y - 2/5| ≤ (16/21)|y|`. -/
theorem nb12w_matanD_slope {y : ℝ} (hy1 : -(1 / 4) ≤ y) (hy2 : y ≤ 1 / 4) (hy0 : y ≠ 0) :
    |(matanD y - matanD 0) / y - 2 / 5| ≤ 16 * |y| / 21 := by
  have hb := nb12w_matan_bracket3 hy1 hy2
  have h1y : (0 : ℝ) < 1 + y := by linarith
  have hy : y ≠ 0 := hy0
  have hid : (matanD y - matanD 0) / y - 2 / 5
      = -y / (2 * (1 + y)) + (-(matan y - (1 - y / 3 + y ^ 2 / 5)) / (2 * y ^ 2)) := by
    rw [matanD_of_ne hy0, matanD_zero]
    field_simp
    ring
  rw [hid]
  refine le_trans (abs_add_le (-y / (2 * (1 + y)))
    (-(matan y - (1 - y / 3 + y ^ 2 / 5)) / (2 * y ^ 2))) ?_
  have ha0 : |y / (2 * (1 + y))| ≤ 2 * |y| / 3 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos h1y]
    have hinv : 1 / (2 * (1 + y)) ≤ 2 / 3 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hmm := mul_le_mul_of_nonneg_left hinv (abs_nonneg y)
    calc |y| / (2 * (1 + y)) = |y| * (1 / (2 * (1 + y))) := by ring
      _ ≤ |y| * (2 / 3) := hmm
      _ = 2 * |y| / 3 := by ring
  have ha : |-y / (2 * (1 + y))| ≤ 2 * |y| / 3 := by
    rw [show -y / (2 * (1 + y)) = -(y / (2 * (1 + y))) by ring, abs_neg]
    exact ha0
  have hb2 : |-(matan y - (1 - y / 3 + y ^ 2 / 5)) / (2 * y ^ 2)| ≤ 2 * |y| / 21 := by
    have hnum : |matan y - (1 - y / 3 + y ^ 2 / 5)| ≤ 4 * |y| ^ 3 / 21 := hb
    have hpos : (0 : ℝ) < 2 * y ^ 2 := by positivity
    rw [abs_div, abs_neg, abs_of_pos hpos]
    rw [div_le_iff₀ hpos]
    have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [hnum, abs_nonneg y]
  linarith

/-- **Second derivative of `matan` at `0`.** -/
theorem matanD_hasDerivAt_zero : HasDerivAt matanD (2 / 5) 0 := by
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun y : ℝ => 16 * |y| / 21)
    (Filter.Eventually.of_forall (fun y => by positivity)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))]
      with y hyne hyball
    have hyabs : |y| < 1 / 4 := by
      have h := Metric.mem_ball.mp hyball
      simpa [Real.dist_eq, sub_zero] using h
    obtain ⟨h1, h2⟩ := abs_lt.mp hyabs
    have hy0 : y ≠ 0 := hyne
    rw [slope_def_field]
    simpa using nb12w_matanD_slope h1.le h2.le hy0
  · have hc : Continuous fun y : ℝ => 16 * |y| / 21 := by fun_prop
    have ht := hc.tendsto (0 : ℝ)
    have h0 : (16 * |(0 : ℝ)| / 21) = 0 := by norm_num
    rw [h0] at ht
    exact ht.mono_left nhdsWithin_le_nhds

/-! ## 5. The second derivative off `t = 0`, and the unified statement -/

/-- **Second derivative of `matan` for `t ≠ 0`** (inside the analytic domain). -/
theorem matanD_hasDerivAt_of_ne {t : ℝ} (ht : t ≠ 0) (ht1 : -1 < t) :
    HasDerivAt matanD (matanDD t) t := by
  have h1t : (1 : ℝ) + t ≠ 0 := by linarith
  have hform : HasDerivAt (fun u : ℝ => (1 / (2 * u)) * (1 / (1 + u) - matan u))
      (matanDD t) t := by
    have h1 : HasDerivAt (fun u : ℝ => (1 : ℝ) + u) 1 t := by
      simpa using (hasDerivAt_id t).const_add 1
    have h2 : HasDerivAt (fun u : ℝ => 1 / (1 + u)) (-(1 / (1 + t) ^ 2)) t := by
      have h := h1.inv h1t
      have hfun : ((fun u : ℝ => 1 + u)⁻¹ : ℝ → ℝ) = fun u : ℝ => 1 / (1 + u) := by
        funext u
        rw [Pi.inv_apply, one_div]
      rw [hfun] at h
      refine h.congr_deriv ?_
      simp only [neg_div, one_div]
    have h3 : HasDerivAt (fun u : ℝ => 1 / (1 + u) - matan u)
        (-(1 / (1 + t) ^ 2) - matanD t) t := by
      have := h2.sub (matan_hasDerivAt ht1)
      exact this
    have h4 : HasDerivAt (fun u : ℝ => 1 / (2 * u)) (-(1 / (2 * t ^ 2))) t := by
      have hu : HasDerivAt (fun u : ℝ => 2 * u) 2 t := by
        simpa using (hasDerivAt_id t).const_mul 2
      have h := hu.inv (by positivity)
      have hfun : ((fun u : ℝ => 2 * u)⁻¹ : ℝ → ℝ) = fun u : ℝ => 1 / (2 * u) := by
        funext u
        rw [Pi.inv_apply, one_div]
      rw [hfun] at h
      refine h.congr_deriv ?_
      field_simp
    have h := h4.mul h3
    refine h.congr_deriv ?_
    rw [matanDD_of_ne ht, matanD_of_ne ht]
    field_simp
    ring
  refine hform.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ u in 𝓝 t, u ≠ 0 := by
    rcases lt_or_gt_of_ne ht with hlt | hgt
    · filter_upwards [Ioo_mem_nhds (show t - 1 < t by linarith)
        (show t < 0 by linarith)] with u hu
      linarith [hu.2]
    · filter_upwards [Ioo_mem_nhds (show 0 < t by linarith)
        (show t < t + 1 by linarith)] with u hu
      linarith [hu.1]
  filter_upwards [hev] with u hu
  exact matanD_of_ne hu

/-- **Second derivative of `matan`, unified**:
`HasDerivAt matanD (matanDD t) t` for every `t > -1`. -/
theorem matanD_hasDerivAt {t : ℝ} (ht : -1 < t) : HasDerivAt matanD (matanDD t) t := by
  rcases eq_or_ne t 0 with h | h
  · subst h
    rw [matanDD_zero]
    exact matanD_hasDerivAt_zero
  · exact matanD_hasDerivAt_of_ne h ht

/-! ## 6. Strict negativity of `matanD` and monotonicity of `matan` -/

/-- `s/(1+s²) < arctan s` for `s > 0` (derivative of the gap is
`2s²/(1+s²)² > 0`, and the gap vanishes at `0`). -/
theorem nb12w_arctan_gt_div {s : ℝ} (hs : 0 < s) :
    s / (1 + s ^ 2) < Real.arctan s := by
  have hcont : ContinuousOn (fun x : ℝ => Real.arctan x - x / (1 + x ^ 2))
      (Set.Ici 0) := by
    refine (Real.continuous_arctan.continuousOn).sub ?_
    refine ContinuousOn.div continuous_id.continuousOn ?_ ?_
    · exact (continuous_const.add (continuous_pow 2)).continuousOn
    · intro x hx
      have : (0 : ℝ) < 1 + x ^ 2 := by positivity
      exact ne_of_gt this
  have h := strictMonoOn_of_deriv_pos (D := Set.Ici (0 : ℝ))
    (f := fun x : ℝ => Real.arctan x - x / (1 + x ^ 2)) (convex_Ici 0) hcont
    (fun x hx => by
      have hx0 : (0 : ℝ) < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
      have hd : HasDerivAt (fun y : ℝ => Real.arctan y - y / (1 + y ^ 2))
          (2 * x ^ 2 / (1 + x ^ 2) ^ 2) x := by
        have hden : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
          have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
            have := hasDerivAt_pow 2 x
            simpa [pow_one, mul_comm] using this
          have hc := (hasDerivAt_const x (1 : ℝ)).add h2
          have hfun : ((fun _ : ℝ => (1 : ℝ)) + (fun y : ℝ => y ^ 2))
              = fun y : ℝ => 1 + y ^ 2 := by funext y; simp
          rw [hfun] at hc
          have hder : (0 : ℝ) + 2 * x = 2 * x := by ring
          rw [hder] at hc
          exact hc
        have hquot : HasDerivAt (fun y : ℝ => y / (1 + y ^ 2))
            ((1 * (1 + x ^ 2) - x * (2 * x)) / (1 + x ^ 2) ^ 2) x :=
          (hasDerivAt_id x).div hden (by positivity)
        have hsub := (Real.hasDerivAt_arctan x).sub hquot
        refine hsub.congr_deriv ?_
        field_simp
        ring
      rw [hd.deriv]
      positivity)
    (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs.le) hs
  simpa using h

/-- `artanh s < s/(1-s²)` for `0 < s < 1` (derivative of the gap is
`-2s²/(1-s²)² < 0`, and the gap vanishes at `0`). -/
theorem nb12w_artanh_lt_div {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    Real.log ((1 + s) / (1 - s)) / 2 < s / (1 - s ^ 2) := by
  have hcont : ContinuousOn
      (fun x : ℝ => Real.log ((1 + x) / (1 - x)) / 2 - x / (1 - x ^ 2)) (Set.Icc 0 s) := by
    refine (nb12_continuousOn_logRatio (s := s) hs1).sub ?_
    refine ContinuousOn.div continuous_id.continuousOn ?_ ?_
    · exact (continuous_const.sub (continuous_pow 2)).continuousOn
    · intro x hx
      have hlt : x < 1 := lt_of_le_of_lt hx.2 hs1
      have hpos : (0 : ℝ) < 1 - x ^ 2 := by nlinarith [hx.1, hlt]
      exact ne_of_gt hpos
  have h := strictAntiOn_of_deriv_neg (D := Set.Icc 0 s)
    (f := fun x : ℝ => Real.log ((1 + x) / (1 - x)) / 2 - x / (1 - x ^ 2))
    (convex_Icc 0 s) hcont
    (fun x hx => by
      rw [interior_Icc] at hx
      have hx0 : (0 : ℝ) < x := hx.1
      have hxs : x < s := hx.2
      have hx1 : (0 : ℝ) < 1 - x ^ 2 := by nlinarith
      have hd : HasDerivAt
          (fun y : ℝ => Real.log ((1 + y) / (1 - y)) / 2 - y / (1 - y ^ 2))
          (-(2 * x ^ 2 / (1 - x ^ 2) ^ 2)) x := by
        have hden : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
          have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
            have := hasDerivAt_pow 2 x
            simpa [pow_one, mul_comm] using this
          have hc := (hasDerivAt_const x (1 : ℝ)).sub h2
          have hfun : ((fun _ : ℝ => (1 : ℝ)) - (fun y : ℝ => y ^ 2))
              = fun y : ℝ => 1 - y ^ 2 := by funext y; simp
          rw [hfun] at hc
          have hder : (0 : ℝ) - 2 * x = -(2 * x) := by ring
          rw [hder] at hc
          exact hc
        have hquot : HasDerivAt (fun y : ℝ => y / (1 - y ^ 2))
            ((1 * (1 - x ^ 2) - x * (-(2 * x))) / (1 - x ^ 2) ^ 2) x :=
          (hasDerivAt_id x).div hden (by positivity)
        have hsub := (nb12_hasDerivAt_artanh (ne_of_lt (by linarith : x < 1))
          (ne_of_gt (by linarith : (-1 : ℝ) < x))).sub hquot
        refine hsub.congr_deriv ?_
        field_simp
        ring
      rw [hd.deriv]
      have hpos : (0 : ℝ) < 2 * x ^ 2 / (1 - x ^ 2) ^ 2 := by positivity
      linarith)
    (Set.mem_Icc.mpr ⟨le_rfl, hs.le⟩) (Set.mem_Icc.mpr ⟨hs.le, le_rfl⟩) hs
  simpa using h

/-- **`matan'` is strictly negative on the analytic domain** `t > -1`. -/
theorem matanD_neg {t : ℝ} (ht : -1 < t) : matanD t < 0 := by
  rcases lt_trichotomy t 0 with h | h | h
  · rw [matanD_of_ne (ne_of_lt h)]
    have hpos : (0 : ℝ) < -t := by linarith
    have hs : (0 : ℝ) < Real.sqrt (-t) := Real.sqrt_pos.mpr hpos
    have hs1 : Real.sqrt (-t) < 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have hs2 : Real.sqrt (-t) ^ 2 = -t := Real.sq_sqrt hpos.le
    have hlt := nb12w_artanh_lt_div hs hs1
    have hm : matan t < 1 / (1 + t) := by
      unfold matan
      rw [if_neg (ne_of_lt h), if_neg (not_lt.mpr h.le)]
      rw [show Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / (2 * Real.sqrt (-t))
          = (Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2) / Real.sqrt (-t) by
        field_simp]
      rw [div_lt_iff₀ hs]
      have hEq : (1 : ℝ) / (1 + t) * Real.sqrt (-t)
          = Real.sqrt (-t) / (1 - Real.sqrt (-t) ^ 2) := by
        rw [hs2]; field_simp; ring
      rw [hEq]
      exact hlt
    have hE : 1 / (1 + t) - matan t > 0 := by linarith
    have hneg : (1 : ℝ) / (2 * t) < 0 := by
      rw [show (1 : ℝ) / (2 * t) = -(1 / (2 * -t)) by field_simp]
      have : (0 : ℝ) < 1 / (2 * -t) := by positivity
      linarith
    exact mul_neg_of_neg_of_pos hneg (by linarith)
  · subst h
    rw [matanD_zero]
    norm_num
  · rw [matanD_of_ne (ne_of_gt h)]
    have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr h
    have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt h.le
    have hgt := nb12w_arctan_gt_div hs
    have hm : 1 / (1 + t) < matan t := by
      unfold matan
      rw [if_neg (ne_of_gt h), if_pos h]
      rw [show (1 : ℝ) / (1 + t) = (Real.sqrt t / (1 + Real.sqrt t ^ 2)) / Real.sqrt t by
        rw [hs2]; field_simp]
      rw [div_lt_div_iff_of_pos_right hs]
      exact hgt
    have hE : 1 / (1 + t) - matan t < 0 := by linarith
    have hpos : (0 : ℝ) < 1 / (2 * t) := by positivity
    exact mul_neg_of_pos_of_neg hpos hE

/-- **`matan` is strictly decreasing on `(-1, ∞)`.** -/
theorem nb12w_matan_strictAntiOn : StrictAntiOn matan (Set.Ioi (-1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi (-1)) ?_ ?_
  · exact nb13_continuousOn_matan
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(matan_hasDerivAt hx).deriv]
    exact matanD_neg hx

/-! ## 7. Axiom audit -/

#print axioms matanD_zero
#print axioms matanD_of_ne
#print axioms matanDD_zero
#print axioms matanDD_of_ne
#print axioms matanD_eq_deriv
#print axioms matan_hasDerivAt
#print axioms nb12w_arctan_ge_sub7
#print axioms nb12w_artanh_ge_sub5
#print axioms nb12w_artanh_le_sub7
#print axioms nb12w_matan_pos_bracket3
#print axioms nb12w_matan_neg_bracket3
#print axioms nb12w_matan_bracket3
#print axioms nb12w_matanD_slope
#print axioms matanD_hasDerivAt_zero
#print axioms matanD_hasDerivAt_of_ne
#print axioms matanD_hasDerivAt
#print axioms nb12w_arctan_gt_div
#print axioms nb12w_artanh_lt_div
#print axioms matanD_neg
#print axioms nb12w_matan_strictAntiOn

end Kepler.Text
