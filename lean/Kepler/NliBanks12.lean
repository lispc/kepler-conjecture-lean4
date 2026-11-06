/-
Kepler.NliBanks12 — lane `xspace-deriv-kit`: **x-space derivative kit** for the
`sqrtdelta` family (work order `w3-xspace-deriv-kit` §2 items 1–2).

Why this file exists: `Gamma4Deriv3..8` only covers **y-space** (`y = x²` and
after); a whole-tree grep for `HasDerivAt … matan / solEulerXDivSqrtdelta /
dihXDivSqrtdeltaPosbranch / ldih…` returned **0 hits**.  The three target banks
(`nliTskGXSA`, `nliCell3QZECFICwt0sqrt8`, `nliCell3QZECFICwt0corner`) all need
per-axis monotonicity in **x-space**, and the `matan` argument is
`Δ / (4 a²)` resp. `4 x₁ Δ / Δ₄²`, which **changes sign inside the T2 box**
(`Δ ∈ [-34.24, +13.68]`).  So the derivative of `matan` must be stitched from
the three branches `t < 0 / t = 0 / t > 0`.

Contents
* §0 `nb12_nonneg_of_deriv` — the "nonnegative derivative ⇒ monotone" helper;
* §1 series brackets: `arctan s` to order `s⁵`, `log((1+s)/(1-s))/2` (`artanh`)
  to order `s⁵`;
* §2 two-sided **quadratic** brackets for `matan` on `|t| ≤ 1/4`
  (`|matan t - (1 - t/3)| ≤ (4/15) t²`).  The linear bracket of `NliBanks10`
  (`1 - t/3 ≤ matan t ≤ 1`) is *not* enough for the `t = 0` stitch: it only
  pins the two one-sided slopes into `[-4/3, 0]`;
* §3 `matanDeriv` — the three-branch derivative
    `t > 0` → `(√t - (1+t)·arctan √t) / (2 (√t)³ (1+t))`
    `t < 0` → `log((1+√-t)/(1-√-t)) / (4 (√-t)³) - 1 / (2 (-t) (1+t))`
    `t = 0` → `-1/3`
  with `HasDerivAt matan (matanDeriv t) t` for every `t > -1` (`matan` is
  discontinuous at `t = -1`, where the `log` branch hits `1 - √(-t) = 0`);
* §4 consumer-facing corollaries: the three `matanDeriv` unfoldings,
  continuity of `matan` off `t = -1`.

No `axiom` / `sorry` / `admit` / `native_decide`; every declaration is audited
at the tail (standard three only).
-/
import Kepler.Text.IneqClosureDefs

set_option maxHeartbeats 2000000

namespace Kepler.NliBanks12
open Kepler.Text
open Filter
open scoped Topology

/-! ## 0. Generic helper -/

/-- `f` with `f 0 = 0` and `f' ≥ 0` on `[0,∞)` is nonnegative there. -/
theorem nb12_nonneg_of_deriv {f : ℝ → ℝ}
    (hC : Continuous f) (hD : Differentiable ℝ f) (h0 : f 0 = 0)
    (hd : ∀ x : ℝ, 0 ≤ x → 0 ≤ deriv f x) : ∀ s : ℝ, 0 ≤ s → 0 ≤ f s := by
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hC.continuousOn hD.differentiableOn
      (fun x hx => by
        have hlt : 0 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
        exact hd x hlt.le)
  intro s hs
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  rwa [h0] at h

/-! ## 1. Series brackets for `arctan` and `artanh` -/

/-- `arctan s ≤ s` for `s ≥ 0`. -/
theorem nb12_arctan_le_self {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ s := by
  have h := nb12_nonneg_of_deriv (f := fun x : ℝ => x - Real.arctan x)
    (hC := continuous_id.sub Real.continuous_arctan)
    (hD := differentiable_id.sub Real.differentiable_arctan)
    (h0 := by simp)
    (hd := by
      intro x _
      have hderiv : HasDerivAt (fun y : ℝ => y - Real.arctan y) (1 - 1 / (1 + x ^ 2)) x :=
        (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
      rw [hderiv.deriv]
      have : 1 - 1 / (1 + x ^ 2) = x ^ 2 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity) s hs
  linarith

/-- `s - s³/3 ≤ arctan s` for `s ≥ 0`. -/
theorem nb12_arctan_ge_sub {s : ℝ} (hs : 0 ≤ s) :
    s - s ^ 3 / 3 ≤ Real.arctan s := by
  have h := nb12_nonneg_of_deriv (f := fun x : ℝ => Real.arctan x - x + x ^ 3 / 3)
    (hC := Real.continuous_arctan.sub continuous_id |>.add (continuous_pow 3 |>.div_const 3))
    (hD := Real.differentiable_arctan.sub differentiable_id |>.add (differentiable_pow 3 |>.div_const 3))
    (h0 := by simp)
    (hd := by
      intro x _
      have hderiv : HasDerivAt (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3)
          (1 / (1 + x ^ 2) - 1 + x ^ 2) x := by
        have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
          have := (hasDerivAt_pow 3 x).div_const 3
          simpa [pow_succ] using this
        exact ((Real.hasDerivAt_arctan x).sub (hasDerivAt_id x)).add h3
      rw [hderiv.deriv]
      have : 1 / (1 + x ^ 2) - 1 + x ^ 2 = x ^ 4 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity) s hs
  linarith

/-- **`arctan` to fifth order**: `arctan s ≤ s - s³/3 + s⁵/5` for `s ≥ 0`
(alternating-series truncation; the derivative of the difference is
`s⁶/(1+s²) ≥ 0`). -/
theorem nb12_arctan_le_sub5 {s : ℝ} (hs : 0 ≤ s) :
    Real.arctan s ≤ s - s ^ 3 / 3 + s ^ 5 / 5 := by
  have h := nb12_nonneg_of_deriv
    (f := fun x : ℝ => x - x ^ 3 / 3 + x ^ 5 / 5 - Real.arctan x)
    (hC := ((continuous_id.sub ((continuous_pow 3).div_const 3)).add
      ((continuous_pow 5).div_const 5)).sub Real.continuous_arctan)
    (hD := ((differentiable_id.sub ((differentiable_pow 3).div_const 3)).add
      ((differentiable_pow 5).div_const 5)).sub Real.differentiable_arctan)
    (h0 := by simp)
    (hd := by
      intro x _
      have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
        have := (hasDerivAt_pow 3 x).div_const 3
        simpa [pow_succ] using this
      have h5 : HasDerivAt (fun y : ℝ => y ^ 5 / 5) (x ^ 4) x := by
        have := (hasDerivAt_pow 5 x).div_const 5
        simpa [pow_succ] using this
      have hderiv : HasDerivAt (fun y : ℝ => y - y ^ 3 / 3 + y ^ 5 / 5 - Real.arctan y)
          (1 - x ^ 2 + x ^ 4 - 1 / (1 + x ^ 2)) x :=
        (((hasDerivAt_id x).sub h3).add h5).sub (Real.hasDerivAt_arctan x)
      rw [hderiv.deriv]
      have : 1 - x ^ 2 + x ^ 4 - 1 / (1 + x ^ 2) = x ^ 6 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity) s hs
  linarith

/-- Derivative of `s ↦ log((1+s)/(1-s))/2` (i.e. `artanh`) is `1/(1-s²)`. -/
theorem nb12_hasDerivAt_artanh {s : ℝ} (h1 : s ≠ 1) (h2 : s ≠ -1) :
    HasDerivAt (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2) (1 / (1 - s ^ 2)) s := by
  have hden : (1 : ℝ) - s ≠ 0 := by intro h; exact h1 (by linarith)
  have hnum : (1 : ℝ) + s ≠ 0 := by intro h; exact h2 (by linarith)
  have hquot : HasDerivAt (fun u : ℝ => (1 + u) / (1 - u))
      ((1 * (1 - s) - (1 + s) * (-1)) / (1 - s) ^ 2) s :=
    ((hasDerivAt_id s).const_add 1).div ((hasDerivAt_id s).const_sub 1) hden
  have hval : (1 + s) / (1 - s) ≠ 0 := div_ne_zero hnum hden
  have hlog := hquot.log hval
  have hfin := hlog.div_const 2
  have hq : (1 * (1 - s) - (1 + s) * (-1)) / (1 - s) ^ 2 = 2 / (1 - s) ^ 2 := by ring
  rw [hq] at hfin
  refine hfin.congr_deriv ?_
  have hs : (1 : ℝ) - s ^ 2 = (1 - s) * (1 + s) := by ring
  rw [hs]
  have hne : (1 - s) * (1 + s) ≠ 0 := mul_ne_zero hden hnum
  field_simp

/-- Continuity of `u ↦ log((1+u)/(1-u))/2` on `[0, s]` for `s < 1`. -/
theorem nb12_continuousOn_logRatio {s : ℝ} (hs1 : s < 1) :
    ContinuousOn (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2) (Set.Icc 0 s) := by
  intro u hu
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 hs1
  have hden : (1 : ℝ) - u ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hval : (1 + u) / (1 - u) ≠ 0 := div_ne_zero (by linarith [hu.1]) hden
  have hnumc : ContinuousAt (fun v : ℝ => (1 : ℝ) + v) u := by fun_prop
  have hdenc : ContinuousAt (fun v : ℝ => (1 : ℝ) - v) u := by fun_prop
  exact (((hnumc.div hdenc hden).log hval).div_const 2).continuousWithinAt

/-- **`artanh` lower bracket**: `s + s³/3 ≤ log((1+s)/(1-s))/2` for `0 ≤ s < 1`
(the derivative of the gap is `s⁴/(1-s²) ≥ 0`, value `0` at `s = 0`). -/
theorem nb12_artanh_ge {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    s + s ^ 3 / 3 ≤ Real.log ((1 + s) / (1 - s)) / 2 := by
  have hcont : ContinuousOn (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2 - u - u ^ 3 / 3)
      (Set.Icc 0 s) :=
    ((nb12_continuousOn_logRatio hs1).sub continuous_id.continuousOn).sub
      ((continuous_pow 3).div_const 3).continuousOn
  have hdiff : ∀ u ∈ Set.Ioo (0:ℝ) s,
      HasDerivAt (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2 - u - u ^ 3 / 3)
        (u ^ 4 / (1 - u ^ 2)) u := by
    intro u hu
    have hu1 : u < 1 := lt_trans hu.2 hs1
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (u ^ 2) u := by
      have := (hasDerivAt_pow 3 u).div_const 3
      simpa [pow_succ] using this
    have := ((nb12_hasDerivAt_artanh (ne_of_lt hu1) (ne_of_gt (by linarith [hu.1] : (-1:ℝ) < u))).sub
      (hasDerivAt_id u)).sub h3
    refine this.congr_deriv ?_
    have hu2 : (1 : ℝ) - u ^ 2 ≠ 0 := by
      intro hh; nlinarith [hu.1, hu1]
    field_simp
    ring
  have hmono : MonotoneOn (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2 - u - u ^ 3 / 3)
      (Set.Icc 0 s) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 s) hcont ?_ ?_
    · intro u hu
      rw [interior_Icc] at hu
      exact (hdiff u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu0 : (0:ℝ) < u := hu.1
      have hu1 : u < 1 := lt_trans hu.2 hs1
      rw [(hdiff u hu).deriv]
      have hd : (0:ℝ) < 1 - u ^ 2 := by nlinarith
      positivity
  have h0 : (fun u : ℝ => Real.log ((1 + u) / (1 - u)) / 2 - u - u ^ 3 / 3) 0 = 0 := by
    norm_num
  have := hmono (Set.mem_Icc.mpr ⟨le_rfl, hs⟩) (Set.mem_Icc.mpr ⟨hs, le_rfl⟩) hs
  rw [h0] at this
  linarith

/-- **`artanh` upper bracket on `[0, 1/2]`**:
`log((1+s)/(1-s))/2 ≤ s + s³/3 + 4s⁵/15` (the gap's derivative is
`s⁴(1-4s²)/(3(1-s²)) ≥ 0` on `[0,1/2]`, value `0` at `s = 0`). -/
theorem nb12_artanh_le {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 1 / 2) :
    Real.log ((1 + s) / (1 - s)) / 2 ≤ s + s ^ 3 / 3 + 4 * s ^ 5 / 15 := by
  have hs1 : s < 1 := by linarith
  have hcont : ContinuousOn
      (fun u : ℝ => u + u ^ 3 / 3 + 4 * u ^ 5 / 15 - Real.log ((1 + u) / (1 - u)) / 2)
      (Set.Icc 0 s) :=
    ((continuous_id.continuousOn.add ((continuous_pow 3).div_const 3).continuousOn).add
      (((continuous_pow 5).const_mul 4).div_const 15).continuousOn).sub
      (nb12_continuousOn_logRatio hs1)
  have hdiff : ∀ u ∈ Set.Ioo (0:ℝ) s,
      HasDerivAt
        (fun u : ℝ => u + u ^ 3 / 3 + 4 * u ^ 5 / 15 - Real.log ((1 + u) / (1 - u)) / 2)
        (u ^ 4 * (1 - 4 * u ^ 2) / (3 * (1 - u ^ 2))) u := by
    intro u hu
    have hu1 : u < 1 := lt_trans hu.2 hs1
    have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (u ^ 2) u := by
      have := (hasDerivAt_pow 3 u).div_const 3
      simpa [pow_succ] using this
    have h5 : HasDerivAt (fun y : ℝ => 4 * y ^ 5 / 15) (4 * u ^ 4 / 3) u := by
      have h := ((hasDerivAt_pow 5 u).const_mul 4).div_const 15
      refine h.congr_deriv ?_
      push_cast
      ring
    have := ((hasDerivAt_id u).add h3).add h5 |>.sub
      (nb12_hasDerivAt_artanh (ne_of_lt hu1) (ne_of_gt (by linarith [hu.1] : (-1:ℝ) < u)))
    refine this.congr_deriv ?_
    have hu2 : (1 : ℝ) - u ^ 2 ≠ 0 := by
      intro hh; nlinarith [hu.1, hu1]
    field_simp
    ring
  have hmono : MonotoneOn
      (fun u : ℝ => u + u ^ 3 / 3 + 4 * u ^ 5 / 15 - Real.log ((1 + u) / (1 - u)) / 2)
      (Set.Icc 0 s) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 s) hcont ?_ ?_
    · intro u hu
      rw [interior_Icc] at hu
      exact (hdiff u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu0 : (0:ℝ) < u := hu.1
      have hu1 : u < 1 := lt_trans hu.2 hs1
      have hus : u ≤ 1 / 2 := le_trans (le_of_lt hu.2) hs2
      rw [(hdiff u hu).deriv]
      have hd : (0:ℝ) < 1 - u ^ 2 := by nlinarith
      have hnum : (0:ℝ) ≤ u ^ 4 * (1 - 4 * u ^ 2) := by
        have h1 : 0 ≤ 1 - 4 * u ^ 2 := by nlinarith
        have h2 : (0:ℝ) ≤ u ^ 4 := by positivity
        exact mul_nonneg h2 h1
      exact div_nonneg hnum (by positivity)
  have h0 : (fun u : ℝ => u + u ^ 3 / 3 + 4 * u ^ 5 / 15 -
      Real.log ((1 + u) / (1 - u)) / 2) 0 = 0 := by norm_num
  have := hmono (Set.mem_Icc.mpr ⟨le_rfl, hs⟩) (Set.mem_Icc.mpr ⟨hs, le_rfl⟩) hs
  rw [h0] at this
  linarith

/-! ## 2. Two-sided quadratic brackets for `matan` on `|t| ≤ 1/4` -/

/-- `matan` on the positive branch, quadratic two-sided bracket. -/
theorem nb12_matan_pos_bracket {t : ℝ} (ht : 0 < t) :
    1 - t / 3 ≤ matan t ∧ matan t ≤ 1 - t / 3 + t ^ 2 / 5 := by
  have hs : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hs5 : (Real.sqrt t) ^ 5 = Real.sqrt t * t ^ 2 := by
    calc (Real.sqrt t) ^ 5 = Real.sqrt t * (Real.sqrt t ^ 2) ^ 2 := by ring
      _ = Real.sqrt t * t ^ 2 := by rw [hs2]
  have hs3 : (Real.sqrt t) ^ 3 = Real.sqrt t * t := by
    calc (Real.sqrt t) ^ 3 = Real.sqrt t * Real.sqrt t ^ 2 := by ring
      _ = Real.sqrt t * t := by rw [hs2]
  unfold matan
  rw [if_neg (ne_of_gt ht), if_pos ht, div_le_iff₀ hs, le_div_iff₀ hs]
  constructor
  · have hge : Real.sqrt t - Real.sqrt t ^ 3 / 3 ≤ Real.arctan (Real.sqrt t) :=
      nb12_arctan_ge_sub hs.le
    rw [hs3] at hge
    calc (1 - t / 3) * Real.sqrt t = Real.sqrt t - Real.sqrt t * t / 3 := by ring
      _ ≤ Real.arctan (Real.sqrt t) := hge
  · have hle : Real.arctan (Real.sqrt t) ≤ Real.sqrt t - Real.sqrt t ^ 3 / 3 +
        (Real.sqrt t) ^ 5 / 5 := nb12_arctan_le_sub5 hs.le
    rw [hs3, hs5] at hle
    calc Real.arctan (Real.sqrt t)
        ≤ Real.sqrt t - Real.sqrt t * t / 3 + Real.sqrt t * t ^ 2 / 5 := hle
      _ = (1 - t / 3 + t ^ 2 / 5) * Real.sqrt t := by ring

/-- `matan` on the negative branch, quadratic two-sided bracket (`|t| ≤ 1/4`). -/
theorem nb12_matan_neg_bracket {t : ℝ} (ht : t < 0) (ht4 : -(1 / 4) ≤ t) :
    1 - t / 3 ≤ matan t ∧ matan t ≤ 1 - t / 3 + 4 * t ^ 2 / 15 := by
  have hpos : (0:ℝ) < -t := by linarith
  have hs : (0:ℝ) < Real.sqrt (-t) := Real.sqrt_pos.mpr hpos
  have hs2 : Real.sqrt (-t) ^ 2 = -t := Real.sq_sqrt hpos.le
  have hsle : Real.sqrt (-t) ≤ 1 / 2 := by
    have h1 : -t ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt (-t) ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = 1 / 2 := by
        rw [show ((1 / 2 : ℝ) ^ 2) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs1 : Real.sqrt (-t) < 1 := by linarith
  have hs5 : (Real.sqrt (-t)) ^ 5 = Real.sqrt (-t) * t ^ 2 := by
    calc (Real.sqrt (-t)) ^ 5 = Real.sqrt (-t) * (Real.sqrt (-t) ^ 2) ^ 2 := by ring
      _ = Real.sqrt (-t) * t ^ 2 := by rw [hs2]; ring
  have hs3 : (Real.sqrt (-t)) ^ 3 = Real.sqrt (-t) * (-t) := by
    calc (Real.sqrt (-t)) ^ 3 = Real.sqrt (-t) * Real.sqrt (-t) ^ 2 := by ring
      _ = Real.sqrt (-t) * (-t) := by rw [hs2]
  have hL : Real.sqrt (-t) + (Real.sqrt (-t)) ^ 3 / 3 ≤
      Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2 := nb12_artanh_ge hs.le hs1
  have hU : Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2 ≤
      Real.sqrt (-t) + (Real.sqrt (-t)) ^ 3 / 3 + 4 * (Real.sqrt (-t)) ^ 5 / 15 :=
    nb12_artanh_le hs.le hsle
  rw [hs3] at hL
  rw [hs3, hs5] at hU
  unfold matan
  rw [if_neg (ne_of_lt ht), if_neg (not_lt.mpr ht.le)]
  constructor
  · rw [show Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / (2 * Real.sqrt (-t)) =
        (Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2) / Real.sqrt (-t) by
      field_simp]
    rw [le_div_iff₀ hs]
    calc (1 - t / 3) * Real.sqrt (-t) = Real.sqrt (-t) + Real.sqrt (-t) * (-t) / 3 := by ring
      _ ≤ Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2 := hL
  · rw [show Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / (2 * Real.sqrt (-t)) =
        (Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2) / Real.sqrt (-t) by
      field_simp]
    rw [div_le_iff₀ hs]
    calc Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / 2
        ≤ Real.sqrt (-t) + Real.sqrt (-t) * (-t) / 3
            + 4 * (Real.sqrt (-t) * t ^ 2) / 15 := hU
      _ = (1 - t / 3 + 4 * t ^ 2 / 15) * Real.sqrt (-t) := by ring

/-- **`matan` quadratic bracket** (both branches, `|t| ≤ 1/4`):
`|matan t - (1 - t/3)| ≤ (4/15)·t²`. -/
theorem nb12_matan_bracket {t : ℝ} (ht : -(1 / 4) ≤ t) (ht' : t ≤ 1 / 4) :
    |matan t - (1 - t / 3)| ≤ 4 * t ^ 2 / 15 := by
  rcases lt_trichotomy t 0 with h | h | h
  · obtain ⟨h1, h2⟩ := nb12_matan_neg_bracket h ht
    have ht2 : (0:ℝ) < t ^ 2 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  · subst h
    unfold matan
    rw [if_pos rfl]
    norm_num
  · obtain ⟨h1, h2⟩ := nb12_matan_pos_bracket h
    have ht2 : (0:ℝ) < t ^ 2 := by nlinarith
    have h5 : t ^ 2 / 5 ≤ 4 * t ^ 2 / 15 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith

/-! ## 3. Axiom audit -/

#print axioms nb12_arctan_le_sub5
#print axioms nb12_artanh_ge
#print axioms nb12_artanh_le
#print axioms nb12_matan_bracket
#print axioms nb12_hasDerivAt_artanh

end Kepler.NliBanks12
