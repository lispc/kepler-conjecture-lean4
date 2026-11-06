/-
Kepler.NliBanks13 — lane `xspace-deriv-kit`, part 1b: the **three-branch
x-space derivative of `matan`** (work order `w3-xspace-deriv-kit` §2 item 1).

`matan` (HOL `sphere.hl:728-731`) is `atan(√t)/√t` for `t > 0` and
`artanh(√-t)/√-t` for `t < 0`, with the removable singularity at `t = 0`
filled by `1`.  The T2 box makes the argument (`Δ/(4a²)`, `4x₁Δ/Δ₄²`)
**change sign**, so a monotonicity certificate must stitch the three branches.

* `matanDerivPos` / `matanDerivNeg` / `matanDeriv` (the `t = 0` branch is
  `-1/3`), and `HasDerivAt matan (matanDeriv t) t` for **every** `t > -1`
  (`matan` is discontinuous at `t = -1`; every consumer stays in `(-1, 1)`);
* the unfoldings `nb13_matanDeriv_{zero,pos,neg}`;
* `nb13_continuousAt_matan` / `nb13_continuousOn_matan`: continuity on
  `(-1, ∞)`, needed when splitting an axis at a sign change of the argument.

No `axiom` / `sorry` / `admit` / `native_decide`; audit at the tail.
-/
import Kepler.NliBanks12

set_option maxHeartbeats 2000000

namespace Kepler.NliBanks13
open Kepler.Text
open Kepler.NliBanks12
open Filter
open scoped Topology

/-! ## 3. The three-branch derivative -/

/-- Positive branch of `matan'`: `(√t - (1+t) arctan √t) / (2 (√t)³ (1+t))`. -/
noncomputable def matanDerivPos (t : ℝ) : ℝ :=
  (Real.sqrt t - (1 + t) * Real.arctan (Real.sqrt t)) / (2 * (Real.sqrt t) ^ 3 * (1 + t))

/-- Negative branch of `matan'`:
`log((1+√-t)/(1-√-t)) / (4 (√-t)³) - 1 / (2 (-t) (1+t))`. -/
noncomputable def matanDerivNeg (t : ℝ) : ℝ :=
  Real.log ((1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t))) / (4 * (Real.sqrt (-t)) ^ 3) -
    1 / (2 * (-t) * (1 + t))

/-- **`matan'` at `0` is `-1/3`** (the removable-singularity stitch): the slope
is squeezed by the quadratic bracket, `|slope - (-1/3)| ≤ (4/15)|t|`. -/
theorem nb13_hasDerivAt_matan_zero : HasDerivAt matan (-(1 / 3)) 0 := by
  have hval : matan 0 = 1 := by unfold matan; rw [if_pos rfl]
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun y : ℝ => 4 * |y| / 15)
    (Filter.Eventually.of_forall (fun y => by positivity)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1 / 4))]
      with y hyne hyball
    have hyabs : |y| < 1 / 4 := by
      have h := Metric.mem_ball.mp hyball
      simpa [Real.dist_eq, sub_zero] using h
    obtain ⟨h1, h2⟩ := abs_lt.mp hyabs
    have hb := nb12_matan_bracket h1.le h2.le
    rw [slope_def_field, hval, sub_zero]
    have hy' : y ≠ 0 := hyne
    have hden : (0:ℝ) < |y| := abs_pos.mpr hy'
    rw [show (matan y - 1) / y - (-(1 / 3)) = (matan y - (1 - y / 3)) / y by
      field_simp; ring]
    rw [Real.norm_eq_abs, abs_div, div_le_iff₀ hden]
    calc |matan y - (1 - y / 3)| ≤ 4 * y ^ 2 / 15 := hb
      _ = 4 * |y| / 15 * |y| := by rw [← sq_abs]; ring
  · have hc : Continuous fun y : ℝ => 4 * |y| / 15 := by fun_prop
    have ht := hc.tendsto (0:ℝ)
    have h0 : (4 * |(0:ℝ)| / 15) = 0 := by norm_num
    rw [h0] at ht
    exact ht.mono_left nhdsWithin_le_nhds

/-- The pure-arithmetic core of the positive-branch chain rule. -/
theorem nb13_pos_deriv_alg {s t : ℝ} (hs : s ≠ 0) (hs2 : s ^ 2 = t) (ht : 1 + t ≠ 0) :
    ((1 / (1 + t) * (1 / (2 * s)) * s - Real.arctan s * (1 / (2 * s))) / s ^ 2) =
      (s - (1 + t) * Real.arctan s) / (2 * s ^ 3 * (1 + t)) := by
  subst hs2
  field_simp

/-- **`matan'` on the positive branch.** -/
theorem nb13_hasDerivAt_matan_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt matan (matanDerivPos t) t := by
  have hs : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have h1 : HasDerivAt (fun u : ℝ => Real.sqrt u) (1 / (2 * Real.sqrt t)) t :=
    Real.hasDerivAt_sqrt (ne_of_gt ht)
  have h2 : HasDerivAt (fun u : ℝ => Real.arctan (Real.sqrt u))
      (1 / (1 + t) * (1 / (2 * Real.sqrt t))) t := by
    have h := HasDerivAt.comp (h := fun u : ℝ => Real.sqrt u) (x := t)
      (Real.hasDerivAt_arctan (Real.sqrt t)) h1
    refine h.congr_deriv ?_
    show 1 / (1 + Real.sqrt t ^ 2) * (1 / (2 * Real.sqrt t)) =
      1 / (1 + t) * (1 / (2 * Real.sqrt t))
    rw [hsq]
  have h3 := h2.div h1 hs
  have hbase : HasDerivAt (fun u : ℝ => Real.arctan (Real.sqrt u) / Real.sqrt u)
      ((Real.sqrt t - (1 + t) * Real.arctan (Real.sqrt t)) /
        (2 * (Real.sqrt t) ^ 3 * (1 + t))) t := by
    refine h3.congr_deriv ?_
    have ht1 : (1 + t) ≠ 0 := by positivity
    exact nb13_pos_deriv_alg hs hsq ht1
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with u hu
  unfold matan
  rw [if_neg (ne_of_gt hu), if_pos hu]

/-- The pure-arithmetic core of the negative-branch chain rule. -/
theorem nb13_neg_deriv_alg {s u : ℝ} (hs : s ≠ 0) (hs2 : s ^ 2 = -u) (hs1 : s ≠ 1)
    (hsm : s ≠ -1) :
    (-(1 / (s * (1 - s) ^ 2)) / ((1 + s) / (1 - s)) * (2 * s) -
        Real.log ((1 + s) / (1 - s)) * -(1 / s)) / (2 * s) ^ 2 =
      Real.log ((1 + s) / (1 - s)) / (4 * s ^ 3) - 1 / (2 * -u * (1 + u)) := by
  have hu : u = -s ^ 2 := by linarith
  subst hu
  have h1s : (1 : ℝ) - s ≠ 0 := by intro h; exact hs1 (by linarith)
  have h1s' : (1 : ℝ) + s ≠ 0 := by intro h; exact hsm (by linarith)
  have hfac : (1 : ℝ) - s ^ 2 = (1 - s) * (1 + s) := by ring
  simp only [neg_neg]
  rw [show (1 : ℝ) + -(s ^ 2) = (1 - s) * (1 + s) from by ring]
  field_simp
  ring

/-- **`matan'` on the negative branch** (`-1 < t < 0`; the `log` branch has its
pole at `t = -1`). -/
theorem nb13_hasDerivAt_matan_neg {t : ℝ} (ht : t < 0) (ht1 : -1 < t) :
    HasDerivAt matan (matanDerivNeg t) t := by
  have hpos : (0:ℝ) < -t := by linarith
  have hs : Real.sqrt (-t) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hs1 : Real.sqrt (-t) ≠ 1 := by
    intro h
    have h2 : (-t) = 1 := by rw [← Real.sq_sqrt hpos.le, h]; norm_num
    linarith
  have hsq : Real.sqrt (-t) ^ 2 = -t := Real.sq_sqrt hpos.le
  have h1 : HasDerivAt (fun u : ℝ => Real.sqrt (-u)) (-(1 / (2 * Real.sqrt (-t)))) t := by
    have h := HasDerivAt.comp (h := fun u : ℝ => -u) (x := t)
      (Real.hasDerivAt_sqrt (ne_of_gt hpos)) (hasDerivAt_id t).neg
    refine h.congr_deriv ?_
    show 1 / (2 * Real.sqrt (-t)) * (-1) = -(1 / (2 * Real.sqrt (-t)))
    ring
  have hq : HasDerivAt (fun u : ℝ => (1 + Real.sqrt (-u)) / (1 - Real.sqrt (-u)))
      (-(1 / (Real.sqrt (-t) * (1 - Real.sqrt (-t)) ^ 2))) t := by
    have hnum : HasDerivAt (fun u : ℝ => (1 : ℝ) + Real.sqrt (-u))
        (-(1 / (2 * Real.sqrt (-t)))) t := h1.const_add 1
    have hden : HasDerivAt (fun u : ℝ => (1 : ℝ) - Real.sqrt (-u))
        (1 / (2 * Real.sqrt (-t))) t := by
      simpa using h1.const_sub 1
    have hdenne : (1 - Real.sqrt (-t)) ≠ 0 := by
      intro h; exact hs1 (sub_eq_zero.mp h).symm
    have := hnum.div hden hdenne
    refine this.congr_deriv ?_
    have hsne : Real.sqrt (-t) ≠ 0 := hs
    field_simp
    ring
  have hqval : (1 + Real.sqrt (-t)) / (1 - Real.sqrt (-t)) ≠ 0 := by
    intro h; rw [div_eq_zero_iff] at h
    rcases h with h | h
    · linarith [Real.sqrt_nonneg (-t)]
    · exact hs1 (sub_eq_zero.mp h).symm
  have hlog := hq.log hqval
  have h2s : HasDerivAt (fun u : ℝ => 2 * Real.sqrt (-u)) (-(1 / Real.sqrt (-t))) t := by
    have h := h1.const_mul 2
    refine h.congr_deriv ?_
    field_simp
  have h2sne : (2 * Real.sqrt (-t)) ≠ 0 := by positivity
  have hfin := hlog.div h2s h2sne
  have hbase : HasDerivAt
      (fun u : ℝ => Real.log ((1 + Real.sqrt (-u)) / (1 - Real.sqrt (-u))) /
        (2 * Real.sqrt (-u))) (matanDerivNeg t) t := by
    refine hfin.congr_deriv ?_
    unfold matanDerivNeg
    exact nb13_neg_deriv_alg hs hsq hs1 (by intro h; linarith [Real.sqrt_nonneg (-t)])
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht1 ht] with u hu
  have hu1 : Real.sqrt (-u) < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by linarith [hu.2]) (by linarith [hu.1])
  have hne : (1 - Real.sqrt (-u)) ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; linarith
  unfold matan
  rw [if_neg (ne_of_lt hu.2), if_neg (not_lt.mpr hu.2.le)]

/-- The three-branch x-space derivative of `matan`. -/
noncomputable def matanDeriv (t : ℝ) : ℝ :=
  if t = 0 then -(1 / 3) else if 0 < t then matanDerivPos t else matanDerivNeg t

/-- **The unified x-space derivative**: `HasDerivAt matan (matanDeriv t) t` for
every `t > -1` (`matan` is discontinuous at `t = -1`).  This is the `t<0 / t=0 /
t>0` stitch required when the argument changes sign inside a box. -/
theorem nb13_hasDerivAt_matan {t : ℝ} (ht : -1 < t) :
    HasDerivAt matan (matanDeriv t) t := by
  rcases lt_trichotomy t 0 with h | h | h
  · unfold matanDeriv
    rw [if_neg (ne_of_lt h), if_neg (not_lt.mpr h.le)]
    exact nb13_hasDerivAt_matan_neg h ht
  · subst h
    unfold matanDeriv
    rw [if_pos rfl]
    exact nb13_hasDerivAt_matan_zero
  · unfold matanDeriv
    rw [if_neg (ne_of_gt h), if_pos h]
    exact nb13_hasDerivAt_matan_pos h

/-! ## 4. Consumer-facing corollaries -/

theorem nb13_matanDeriv_zero : matanDeriv 0 = -(1 / 3) := by
  unfold matanDeriv; rw [if_pos rfl]

theorem nb13_matanDeriv_pos {t : ℝ} (ht : 0 < t) :
    matanDeriv t = matanDerivPos t := by
  unfold matanDeriv; rw [if_neg (ne_of_gt ht), if_pos ht]

theorem nb13_matanDeriv_neg {t : ℝ} (ht : t < 0) :
    matanDeriv t = matanDerivNeg t := by
  unfold matanDeriv; rw [if_neg (ne_of_lt ht), if_neg (not_lt.mpr ht.le)]

/-- `matan` is continuous on its analytic domain `(-1, ∞)` (at `t = 0` the two
branches meet; at `t = -1` the `log` branch has a pole: `matan` jumps to the
junk value `0`). -/
theorem nb13_continuousAt_matan {t : ℝ} (ht : -1 < t) : ContinuousAt matan t := by
  rcases lt_trichotomy t 0 with h | h | h
  · have ht1 : -1 < t := ht
    have hev : matan =ᶠ[𝓝 t]
        (fun u : ℝ => Real.log ((1 + Real.sqrt (-u)) / (1 - Real.sqrt (-u))) /
          (2 * Real.sqrt (-u))) := by
      filter_upwards [Ioo_mem_nhds ht1 h] with u hu
      have hu1 : Real.sqrt (-u) < 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (by linarith [hu.2]) (by linarith [hu.1])
      have hne : (1 - Real.sqrt (-u)) ≠ 0 := by
        intro hh; rw [sub_eq_zero] at hh; linarith
      unfold matan
      rw [if_neg (ne_of_lt hu.2), if_neg (not_lt.mpr hu.2.le)]
    have hc : ContinuousAt
        (fun u : ℝ => Real.log ((1 + Real.sqrt (-u)) / (1 - Real.sqrt (-u))) /
          (2 * Real.sqrt (-u))) t := by
      have hff : ContinuousAt (fun u : ℝ => Real.sqrt (-u)) t :=
        (Real.continuous_sqrt.comp continuous_neg).continuousAt
      have hs1 : Real.sqrt (-t) < 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
      refine ContinuousAt.div (f := fun u : ℝ => Real.log ((1 + Real.sqrt (-u)) / (1 - Real.sqrt (-u))))
        (g := fun u : ℝ => 2 * Real.sqrt (-u)) ?_ ?_ ?_
      · refine ContinuousAt.log (f := fun u : ℝ => (1 + Real.sqrt (-u)) / (1 - Real.sqrt (-u))) ?_ ?_
        · refine ContinuousAt.div (f := fun u : ℝ => 1 + Real.sqrt (-u))
            (g := fun u : ℝ => 1 - Real.sqrt (-u)) ?_ ?_ ?_
          · exact hff.const_add 1
          · exact hff.const_sub 1
          · intro hh; rw [sub_eq_zero] at hh; linarith
        · intro hh
          rw [div_eq_zero_iff] at hh
          rcases hh with hh | hh
          · linarith [Real.sqrt_nonneg (-t)]
          · linarith [hs1]
      · exact hff.const_mul 2
      · exact mul_ne_zero two_ne_zero (Real.sqrt_ne_zero'.mpr (by linarith : (0:ℝ) < -t))
    exact ContinuousAt.congr hc hev.symm
  · subst h
    have hval : matan 0 = 1 := by unfold matan; rw [if_pos rfl]
    rw [ContinuousAt, hval, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun y : ℝ => |y|)
      (Filter.Eventually.of_forall (fun y => by positivity)) ?_ ?_
    · filter_upwards [(Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1 / 4))] with y hyball
      have hyabs : |y| < 1 / 4 := by
        have h := Metric.mem_ball.mp hyball
        simpa [Real.dist_eq, sub_zero] using h
      obtain ⟨h1, h2⟩ := abs_lt.mp hyabs
      have hb := nb12_matan_bracket h1.le h2.le
      calc |matan y - 1| = |(matan y - (1 - y / 3)) + (-(y / 3))| := by congr 1; ring
        _ ≤ |matan y - (1 - y / 3)| + |-(y / 3)| := abs_add_le _ _
        _ ≤ 4 * y ^ 2 / 15 + |y| / 3 := by
            have h3 : |-(y / 3)| = |y| / 3 := by rw [abs_neg, abs_div]; norm_num
            linarith [hb, abs_nonneg (matan y - (1 - y / 3))]
        _ ≤ |y| := by
            rw [← sq_abs]
            have h4 : |y| ≤ 1 / 4 := le_of_lt hyabs
            nlinarith [abs_nonneg y]
    · have hc : Continuous fun y : ℝ => |y| := by fun_prop
      have ht2 := hc.tendsto (0:ℝ)
      simpa using ht2
  · have hev : matan =ᶠ[𝓝 t]
        (fun u : ℝ => Real.arctan (Real.sqrt u) / Real.sqrt u) := by
      filter_upwards [lt_mem_nhds h] with u hu
      unfold matan
      rw [if_neg (ne_of_gt hu), if_pos hu]
    have hc : ContinuousAt (fun u : ℝ => Real.arctan (Real.sqrt u) / Real.sqrt u) t := by
      refine ContinuousAt.div ?_ Real.continuous_sqrt.continuousAt ?_
      · exact Real.continuous_arctan.continuousAt.comp Real.continuous_sqrt.continuousAt
      · exact Real.sqrt_ne_zero'.mpr h
    exact ContinuousAt.congr hc hev.symm

/-- `matan` is continuous on `(-1, ∞)`. -/
theorem nb13_continuousOn_matan : ContinuousOn matan (Set.Ioi (-1)) := by
  intro t ht
  exact (nb13_continuousAt_matan ht).continuousWithinAt


/-! ## 6. Axiom audit -/

#print axioms nb13_hasDerivAt_matan_zero
#print axioms nb13_hasDerivAt_matan_pos
#print axioms nb13_hasDerivAt_matan_neg
#print axioms nb13_hasDerivAt_matan
#print axioms nb13_continuousAt_matan
#print axioms nb13_continuousOn_matan

end Kepler.NliBanks13
