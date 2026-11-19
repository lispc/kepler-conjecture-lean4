/-
Kepler.NliBanks19 — lane `cell3-wt-math-w1`: the bank `bank_QZECFICwt2A`
(Assembly debt `nliCell3QZECFICwt2A`, HOL ineq.hl:1443 `QZECFIC wt2 A`,
tags [Split[3;4]]) — math-reduce scaffold + box identities.

Current state: the bank is reduced (axioms-clean) to the explicit core
inequality `0 < w2aF y4 y5 y6` on the closed Delta region; the remaining
certificate is the y6/y5 walk + the 1D y4 bracket battery (see the lane
route map).  No `axiom` / `sorry` / `admit` / `native_decide`; audited at
the tail.
-/
import Kepler.NliBanks11
import Kepler.NliBanks13
import Kepler.NliBanks17  -- hminus envelope

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks19
open Kepler.Text
open Kepler.NliBanks11
open Kepler.NliBanks12
open Kepler.NliBanks13

/-! ## 1. Explicit form of `gamma3fXDivSqrtdelta m4 m5 m6` -/

/-- Explicit form of `gamma3fXDivSqrtdelta m4 m5 m6` (the `mk456` slots
1–3 are replaced by `2` before the rotations, so `x1 x2 x3` do not occur).
Generalization of `NliBanks18.nb18_unfold` keeping the three dihedral
coefficients symbolic. -/
theorem nb19_g3_unfold (m4 m5 m6 x1 x2 x3 x4 x5 x6 : ℝ) :
    gamma3fXDivSqrtdelta m4 m5 m6 x1 x2 x3 x4 x5 x6 =
      1 / 12 - (2 * mm1 / Real.pi) *
        (solEulerXDivSqrtdelta x5 2 x4 2 x6 2 + solEulerXDivSqrtdelta x6 2 x5 2 x4 2 +
          solEulerXDivSqrtdelta x4 2 x6 2 x5 2) +
        (8 * mm2 / Real.pi) *
          (lfun (Real.sqrt x4 * 0.5) * m4 * dihXDivSqrtdeltaPosbranch x4 2 x6 2 x5 2 +
            lfun (Real.sqrt x5 * 0.5) * m5 * dihXDivSqrtdeltaPosbranch x5 2 x4 2 x6 2 +
            lfun (Real.sqrt x6 * 0.5) * m6 * dihXDivSqrtdeltaPosbranch x6 2 x5 2 x4 2) := by
  simp only [gamma3fXDivSqrtdelta, scalar6, uni, mk456, compose6, projX4, projX5, projX6,
    projY4, projY5, projY6, constant6, two6, rotate4, rotate5, rotate6,
    Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  ring

/-- The `rotate4` pin for the `dih4` slot (restated from the definitional
valve `IneqClosureDefs` so downstream lemmas can rewrite with it). -/
theorem nb19_dih4_pin (x1 x2 x3 x4 x5 x6 : ℝ) :
    dih4XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 =
      dihXDivSqrtdeltaPosbranch x4 x2 x6 x1 x5 x3 := rfl

/-! ## 2. The wt2A kernel -/

/-- Left-hand kernel of `QZECFIC wt2 A` at `y1 = y2 = y3 = √2`. -/
noncomputable def w2aG (y4 y5 y6 : ℝ) : ℝ :=
  yOfX (gamma3fXDivSqrtdelta (h0cut y4) (h0cut y5) 1) (Real.sqrt 2) (Real.sqrt 2)
    (Real.sqrt 2) y4 y5 y6

/-- Right-hand kernel of `QZECFIC wt2 A` at `y1 = y2 = y3 = √2`. -/
noncomputable def w2aD (y4 y5 y6 : ℝ) : ℝ :=
  yOfX dih4XDivSqrtdeltaPosbranch (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6

/-- First-disjunct margin of `QZECFIC wt2 A`. -/
noncomputable def w2aF (y4 y5 y6 : ℝ) : ℝ := w2aG y4 y5 y6 / 2 - (0.008 : ℝ) * w2aD y4 y5 y6

/-- Explicit form of the left kernel (coordinates nonnegative). -/
theorem nb19_w2aG_explicit (y4 y5 y6 : ℝ) (h4 : 0 ≤ y4) (h5 : 0 ≤ y5) (h6 : 0 ≤ y6) :
    w2aG y4 y5 y6 =
      1 / 12 - (2 * mm1 / Real.pi) *
        (solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
          solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 +
          solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2) +
        (8 * mm2 / Real.pi) *
          (lfun (y4 * 0.5) * h0cut y4 * dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 +
            lfun (y5 * 0.5) * h0cut y5 * dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
            lfun (y6 * 0.5) * 1 * dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2) := by
  have hs4 : Real.sqrt (y4 * y4) = y4 := Real.sqrt_mul_self h4
  have hs5 : Real.sqrt (y5 * y5) = y5 := Real.sqrt_mul_self h5
  have hs6 : Real.sqrt (y6 * y6) = y6 := Real.sqrt_mul_self h6
  simp only [w2aG, yOfX, nb19_g3_unfold]
  rw [hs4, hs5, hs6]

/-- Explicit form of the right kernel (coordinates nonnegative). -/
theorem nb19_w2aD_explicit (y4 y5 y6 : ℝ) :
    w2aD y4 y5 y6 =
      dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [w2aD, yOfX, nb19_dih4_pin]
  rw [hs2]

/-! ## 3. `h0cut` pins -/

/-- `h0cut` is `{0,1}-valued and nonnegative. -/
theorem nb19_h0cut_nonneg (y : ℝ) : 0 ≤ h0cut y := by
  unfold h0cut
  split_ifs <;> norm_num

/-- `h0cut y ≤ 1`. -/
theorem nb19_h0cut_le_one (y : ℝ) : h0cut y ≤ 1 := by
  unfold h0cut
  split_ifs <;> norm_num

/-- The kink location: `2 * h0 = 2.52`. -/
theorem nb19_two_h0 : 2 * h0 = (2.52 : ℝ) := by
  rw [show h0 = (1.26 : ℝ) from rfl]
  norm_num

/-- `h0cut y = 1` iff `y ≤ 2 * h0`. -/
theorem nb19_h0cut_eq_one {y : ℝ} (h : y ≤ 2 * h0) : h0cut y = 1 := by
  unfold h0cut
  rw [if_pos h]

/-- `h0cut y = 0` iff `y > 2 * h0`. -/
theorem nb19_h0cut_eq_zero {y : ℝ} (h : 2 * h0 < y) : h0cut y = 0 := by
  unfold h0cut
  rw [if_neg (not_le.mpr h)]

/-- The product `h0cut y * lfun (y / 2)` is nonnegative for `y ≥ 0`: on
`{h0cut = 1}` we have `y ≤ 2 h0` so `lfun (y/2) = (h0 - y/2)/(h0 - 1) ≥ 0`;
on `{h0cut = 0}` the product vanishes.  This is the smoothing identity that
makes the `y4 = 2 h0` / `y5 = 2 h0` kinks invisible to the margin. -/
theorem nb19_h0cut_lfun_nonneg {y : ℝ} (h : 0 ≤ y) : 0 ≤ h0cut y * lfun (y * 0.5) := by
  have h0v : h0 = (1.26 : ℝ) := rfl
  by_cases hy : y ≤ 2 * h0
  · rw [nb19_h0cut_eq_one hy]
    have hl : (0 : ℝ) ≤ lfun (y * 0.5) := by
      unfold lfun
      have hh : y * 0.5 ≤ h0 := by linarith [hy, h0v]
      have h01 : (0 : ℝ) < h0 - 1 := by linarith [h0v]
      apply div_nonneg
      · linarith
      · linarith
    positivity
  · rw [nb19_h0cut_eq_zero (lt_of_not_ge hy)]
    norm_num

/-! ## 4. The `eta`/`delta` duality on the wt2A box -/

/-- `upsX` at three squares. -/
theorem nb19_ups_eq (a b c : ℝ) :
    upsX (a * a) (b * b) (c * c) = 4 * (b * b) * (c * c) - (a * a - b * b - c * c) ^ 2 := by
  rw [upsX]
  ring

/-- The three-coordinate Delta of the wt2A family at three squares. -/
theorem nb19_dlt_eq (a b c : ℝ) :
    deltaX (a * a) 2 (b * b) 2 (c * c) 2
      = 2 * upsX (a * a) (b * b) (c * c) - a * a * (b * b) * (c * c) := by
  rw [deltaX, upsX]
  ring

/-- `upsX > 0` on the wt2A Lean box `y4,y5 ∈ [2hminus, √8]`, `y6 ∈ [2, 2hminus]`. -/
theorem nb19_w2a_ups_pos {y4 y5 y6 : ℝ} (hy4 : 2 * hminus ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : 2 * hminus ≤ y5) (hy5' : y5 ≤ Real.sqrt 8) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * hminus) :
    0 < upsX (y4 * y4) (y5 * y5) (y6 * y6) := by
  have hhm := Kepler.NliBanks17.nb17_two_hminus_bounds
  have hsq8 : (Real.sqrt 8) * (Real.sqrt 8) = 8 := Real.mul_self_sqrt (by norm_num)
  have hy4pos : (0:ℝ) ≤ y4 := by linarith [hy4, hhm.1]
  have hy5pos : (0:ℝ) ≤ y5 := by linarith [hy5, hhm.1]
  have hy6pos : (0:ℝ) ≤ y6 := by linarith [hy6]
  have hw8 : y4 * y4 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy4pos hy4'
    rw [hsq8] at h
    exact h
  have hw8' : y5 * y5 ≤ (8:ℝ) := by
    have h := mul_self_le_mul_self hy5pos hy5'
    rw [hsq8] at h
    exact h
  have hw8'' : (24275329/4000000:ℝ) ≤ y4 * y4 := by
    have h := mul_self_le_mul_self (show (0:ℝ) ≤ (2.4635:ℝ) by norm_num)
      (show (2.4635:ℝ) ≤ y4 by linarith [hy4, hhm.1])
    norm_num at h
    exact h
  have hw8''' : (24275329/4000000:ℝ) ≤ y5 * y5 := by
    have h := mul_self_le_mul_self (show (0:ℝ) ≤ (2.4635:ℝ) by norm_num)
      (show (2.4635:ℝ) ≤ y5 by linarith [hy5, hhm.1])
    norm_num at h
    exact h
  have hb6 : (4:ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  have hy6b : y6 ≤ (2.46352:ℝ) := by linarith [hy6', hhm.2]
  have h6sq := mul_self_le_mul_self hy6pos hy6b
  rw [nb19_ups_eq]
  have hwle : y4 * y4 ≤ y5 * y5 + y6 * y6 := by linarith
  have hsum0 : (0:ℝ) ≤ y5 * y5 + y6 * y6 - y4 * y4 := by linarith
  have hsumub : y5 * y5 + y6 * y6 - y4 * y4 ≤ (8.01:ℝ) := by linarith
  have hsqle : (y5 * y5 + y6 * y6 - y4 * y4) * (y5 * y5 + y6 * y6 - y4 * y4)
      ≤ (8.01:ℝ) * (8.01:ℝ) := mul_self_le_mul_self hsum0 hsumub
  have hprod : (97:ℝ) ≤ 4 * (y5 * y5) * (y6 * y6) := by
    have h16 : (24.2753:ℝ) ≤ (y5 * y5) * (y6 * y6) := by nlinarith [hw8''', hb6]
    linarith
  have hsqub : ((8.01:ℝ)) * ((8.01:ℝ)) ≤ (64.17:ℝ) := by norm_num
  linarith [hprod, hsqle, hsqub]

/-- **Right disjunct of `QZECFIC wt2 A`**: on the wt2A box, negative three-
coordinate Delta forces `eta_y ^ 2 > 2`. -/
theorem nb19_w2a_eta_dlt_neg {y4 y5 y6 : ℝ} (hy4 : 2 * hminus ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : 2 * hminus ≤ y5) (hy5' : y5 ≤ Real.sqrt 8) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * hminus)
    (hd : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 < 0) :
    eta_y y4 y5 y6 ^ 2 > 2 := by
  have hups := nb19_w2a_ups_pos hy4 hy4' hy5 hy5' hy6 hy6'
  have htri := nb19_dlt_eq y4 y5 y6
  have hy4pos : (0:ℝ) ≤ y4 := by
    have h1 : (2.4635:ℝ) ≤ 2 * hminus := Kepler.NliBanks17.nb17_two_hminus_bounds.1
    linarith
  have hy5pos : (0:ℝ) ≤ y5 := by
    have h1 : (2.4635:ℝ) ≤ 2 * hminus := Kepler.NliBanks17.nb17_two_hminus_bounds.1
    linarith
  have hy6pos : (0:ℝ) ≤ y6 := by linarith [hy6]
  have hP : (0:ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6) :=
    mul_nonneg (mul_nonneg (mul_nonneg hy4pos hy4pos)
      (mul_nonneg hy5pos hy5pos)) (mul_nonneg hy6pos hy6pos)
  have hrel : 2 * upsX (y4 * y4) (y5 * y5) (y6 * y6)
      < y4 * y4 * (y5 * y5) * (y6 * y6) := by linarith
  have hquo : (0:ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6)
      / upsX (y4 * y4) (y5 * y5) (y6 * y6) := div_nonneg hP hups.le
  have hrw : eta_y y4 y5 y6 ^ 2
      = y4 * y4 * (y5 * y5) * (y6 * y6)
        / upsX (y4 * y4) (y5 * y5) (y6 * y6) := by
    simp only [eta_y, etaY, etaX, pow_two, Real.mul_self_sqrt hquo]
  rw [hrw, gt_iff_lt, lt_div_iff₀ hups]
  exact hrel

/-- **Converse**: on the wt2A box, `eta_y ^ 2 ≤ 2` forces the three-coordinate
Delta to be nonnegative (the left-disjunct region). -/
theorem nb19_w2a_delta_ge {y4 y5 y6 : ℝ} (hy4 : 2 * hminus ≤ y4) (hy4' : y4 ≤ Real.sqrt 8)
    (hy5 : 2 * hminus ≤ y5) (hy5' : y5 ≤ Real.sqrt 8) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * hminus)
    (he : eta_y y4 y5 y6 ^ 2 ≤ 2) :
    0 ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 := by
  have hups := nb19_w2a_ups_pos hy4 hy4' hy5 hy5' hy6 hy6'
  have htri := nb19_dlt_eq y4 y5 y6
  have hy4pos : (0:ℝ) ≤ y4 := by
    have h1 : (2.4635:ℝ) ≤ 2 * hminus := Kepler.NliBanks17.nb17_two_hminus_bounds.1
    linarith
  have hy5pos : (0:ℝ) ≤ y5 := by
    have h1 : (2.4635:ℝ) ≤ 2 * hminus := Kepler.NliBanks17.nb17_two_hminus_bounds.1
    linarith
  have hy6pos : (0:ℝ) ≤ y6 := by linarith [hy6]
  have hP : (0:ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6) :=
    mul_nonneg (mul_nonneg (mul_nonneg hy4pos hy4pos)
      (mul_nonneg hy5pos hy5pos)) (mul_nonneg hy6pos hy6pos)
  have hquo : (0:ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6)
      / upsX (y4 * y4) (y5 * y5) (y6 * y6) := div_nonneg hP hups.le
  have hrw : eta_y y4 y5 y6 ^ 2
      = y4 * y4 * (y5 * y5) * (y6 * y6)
        / upsX (y4 * y4) (y5 * y5) (y6 * y6) := by
    simp only [eta_y, etaY, etaX, pow_two, Real.mul_self_sqrt hquo]
  rw [hrw] at he
  have h2u : y4 * y4 * (y5 * y5) * (y6 * y6)
      ≤ 2 * upsX (y4 * y4) (y5 * y5) (y6 * y6) := (div_le_iff₀ hups).mp he
  linarith

/-! ## 5. Bank reduction scaffold -/

/-- `QZECFIC wt2 A` follows from the core margin inequality on the closed
Delta region.  Residual obligation (the analytic certificate):
`∀ y4 y5 y6` in the box with `deltaX (y4²) 2 (y5²) 2 (y6²) 2 ≥ 0`,
`0 < w2aF y4 y5 y6`. -/
theorem bank_QZECFICwt2A_of_core
    (hcore : ∀ y4 y5 y6 : ℝ, 2 * hminus ≤ y4 → y4 ≤ Real.sqrt 8 →
      2 * hminus ≤ y5 → y5 ≤ Real.sqrt 8 → 2 ≤ y6 → y6 ≤ 2 * hminus →
      0 ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 →
      0 < w2aF y4 y5 y6) :
    bank_QZECFICwt2A := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hy1 : y1 = Real.sqrt 2 := le_antisymm h1' h1
  have hy2 : y2 = Real.sqrt 2 := le_antisymm h2' h2
  have hy3 : y3 = Real.sqrt 2 := le_antisymm h3' h3
  by_cases heta : (2:ℝ) < eta_y y4 y5 y6 ^ 2
  · exact Or.inr heta
  · left
    have hd : 0 ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 :=
      nb19_w2a_delta_ge h4 h4' h5 h5' h6 h6' (le_of_not_gt heta)
    have hF := hcore y4 y5 y6 h4 h4' h5 h5' h6 h6' hd
    rw [hy1, hy2, hy3, ← w2aG, ← w2aD]
    unfold w2aF at hF
    rw [sub_pos] at hF
    exact hF

/-! ## 6. Axiom audit -/

#print axioms nb19_g3_unfold
#print axioms nb19_w2aG_explicit
#print axioms nb19_w2aD_explicit
#print axioms nb19_h0cut_lfun_nonneg
#print axioms nb19_w2a_ups_pos
#print axioms nb19_w2a_eta_dlt_neg
#print axioms nb19_w2a_delta_ge
#print axioms bank_QZECFICwt2A_of_core

end Kepler.NliBanks19
