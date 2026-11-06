/-
Kepler.NliBanks17 — lane `nli-tsk-w2`: the Marchal-root **upper** pinning
`hminus ≤ 1.23176`, the missing enabler for `nliTskRIBCYXUsym`.

## Why this file exists (and why it is not a bank proof)

The five remaining cone banks `nliTskXLLIPLS` / `nliTskRIBCYXUsym` /
`nliTskWKGUESBsym` / `nliTskIYOUOBFsym` / `nliTskIYOUOBFsharpv2` are **y-space
`gamma4fgcy · lmfun`** statements, not the x-space ring-algebraic kernel of
`nliTskGXSA`.  The T1 zero-derivative template (`NliBanks15/16`) therefore does
not apply: `gamma4fgcy` contains `sqrt`/`arctan`/`lmfun`, so the corner-walk
factorisations cannot be `ring`-expressed, and the only x↔y bridge in-tree
(PA21 `p21k_gamma4fgcy_div_sqrtdelta`) is `private` and consumes the
**unproved** Euler anchor `p21k_euler_anchor`.  See `DELIVERY.md` for the
per-bank gap table.

The `RIBCYXUsym` box `[2.001,2hminus]×[2,2hminus]⁵` is the one place where an
*arithmetic* fact is missing on top of the analytic kit: the whole box is
positive only because `2·hminus = 2.463508844…` stays left of the negative
valley of `t ↦ gamma4fgcy t 2 2 2 2 2 lmfun`, which starts at `t ≈ 2.4644`
(at `hminus = 1.29`, allowed by the recorded envelope `1.23175 ≤ hminus < 1.3`,
the bank is *false*: `gamma4fgcy (2·1.29) 2⁵ lmfun ≈ -2.6e-3` with
`2·1.29 = 2.58 > 2` and every ordering disjunct false).  So the statement is
**not** implied by the previously available envelope; an upper pinning is a
necessary enabler.  This file proves it.

## Contents (all standard three; no `sorry`/`axiom`/`native_decide`)

* `nb17_marchal_gt_lmfun_left` — `marchalQuartic h > lmfun h` on
  `[1.23176, 1.26]` (cleared quartic certificate, same shape as
  `Kepler.NliBanks7.marchalQuartic_lt_lmfun_123175`, reversed direction);
* `nb17_marchal_gt_lmfun_right` — `marchalQuartic h > lmfun h = 0` on
  `[1.26, 1.3)` (endpoint-convexity sign of `9h²−17h+3`);
* `nb17_marchal_gt_lmfun`, `nb17_hminus_le_123176`, `nb17_hminus_bounds`
  (`[1.23175, 1.23176]`), `nb17_two_hminus_bounds`
  (`2·hminus ∈ [2.4635, 2.46352]`), `nb17_two_hminus_lt_two_h0`
  (`2·hminus < 2·h0 = 2.52`: no `lmfun` kink inside the bank box).
-/
import Kepler.NliBanks7

set_option maxHeartbeats 2000000

namespace Kepler.NliBanks17
open Kepler.Text

/-! ## 1. The quartic certificate on the left piece `[1.23176, 1.26]` -/

/-- On the right of the Marchal root the quartic is strictly above the linear
cap: `lmfun h < marchalQuartic h` for `h ∈ [1.23176, 1.26]`.

Same normalisation as `Kepler.NliBanks7.marchalQuartic_lt_lmfun_123175`:
clear the positive denominator `(√2−1)·5·(hplus−1)` and bracket
`1.41421356 < √2 < 1.41421357`; after substituting `h = 1.23176 + t`,
`t ∈ [0, 0.02824]`, the cleared difference is
`1.9146e−6 + 0.3434 t + 1.4453 t² − 0.6986 t³ − 2.34 t⁴ > 0`. -/
private theorem marchal_gt_lmfun_123176 {h : ℝ} (h1 : (1.23176 : ℝ) ≤ h)
    (h2 : h ≤ 1.26) : lmfun h < marchalQuartic h := by
  -- rational enclosures of `√2`
  have hs_lo : (1.41421356 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs_hi : Real.sqrt 2 < 1.41421357 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  -- positivity / bracketing of the pieces
  have hD : (0:ℝ) < (Real.sqrt 2 - 1) * 5 * (hplus - 1) := by
    have a : (0:ℝ) < Real.sqrt 2 - 1 := by linarith
    have b : (0:ℝ) < hplus - 1 := by rw [hplus]; norm_num
    positivity
  have hDhi : (Real.sqrt 2 - 1) * 5 * (hplus - 1) ≤
      (1.41421357 - 1) * 5 * (hplus - 1) := by
    have b : (0:ℝ) < 5 * (hplus - 1) := by rw [hplus]; norm_num
    nlinarith [hs_hi]
  have hA : (0:ℝ) < Real.sqrt 2 - h := by linarith
  have hB : (0:ℝ) < hplus - h := by rw [hplus]; linarith
  have hC : (0:ℝ) < 17 * h - 9 * h ^ 2 - 3 := by
    have hfac : 17 * h - 9 * h ^ 2 - 3 - 4.1316 = (h - 1.26) * (5.66 - 9 * h) := by ring
    have hp : (0:ℝ) ≤ (h - 1.26) * (5.66 - 9 * h) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    nlinarith [hp]
  have hE : (0:ℝ) ≤ h0 - h := by rw [h0]; linarith
  have hE1 : (0:ℝ) < h0 - 1 := by rw [h0]; norm_num
  -- normal form with the quadratic factor expanded the useful way
  have hmq : marchalQuartic h =
      (Real.sqrt 2 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) /
        ((Real.sqrt 2 - 1) * 5 * (hplus - 1)) := by
    unfold marchalQuartic
    have e : (Real.sqrt 2 - h) * (h - hplus) * (9 * h ^ 2 - 17 * h + 3)
        = (Real.sqrt 2 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) := by ring
    rw [e]
  have hlm : lmfun h = (h0 - h) / (h0 - 1) := by
    unfold lmfun
    rw [if_pos (by rw [h0]; linarith)]
  -- the cleared certificate, positive on the whole `t`-interval
  have hkey : (0:ℝ) < (1.41421356 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) *
        (h0 - 1) - (h0 - h) * ((1.41421357 - 1) * 5 * (hplus - 1)) := by
    rw [show h0 = (1.26:ℝ) from rfl, show hplus = (1.3254:ℝ) from rfl]
    have ht0 : (0:ℝ) ≤ h - 1.23176 := by linarith
    have htT : h - 1.23176 ≤ 0.02824 := by linarith
    have h2t : (h - 1.23176) ^ 2 ≤ 0.02824 * (h - 1.23176) := by nlinarith
    have h3t : (h - 1.23176) ^ 3 ≤ 0.02824 ^ 2 * (h - 1.23176) := by nlinarith
    have h4t : (h - 1.23176) ^ 4 ≤ 0.02824 ^ 3 * (h - 1.23176) := by nlinarith
    nlinarith [ht0, htT, h2t, h3t, h4t]
  -- clear the denominators
  rw [hmq, hlm, div_lt_div_iff₀ hE1 hD]
  -- `(h0−h)·D < (√2−h)·(…)·(h0−1)`
  have hBCE : (0:ℝ) < (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1) :=
    mul_pos (mul_pos hB hC) hE1
  have hlo : (1.41421356 - h) * ((hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1))
      < (Real.sqrt 2 - h) * ((hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1)) :=
    mul_lt_mul_of_pos_right (by linarith) hBCE
  have hDhi' : (h0 - h) * ((Real.sqrt 2 - 1) * 5 * (hplus - 1))
      ≤ (h0 - h) * ((1.41421357 - 1) * 5 * (hplus - 1)) :=
    mul_le_mul_of_nonneg_left hDhi hE
  nlinarith [hlo, hDhi', hkey]

/-! ## 2. The right piece `[1.26, 1.3)` -/

/-- `9h² − 17h + 3 < 0` on `[1.26, 1.3]` (convex quadratic: the maximum sits at
an endpoint, and both endpoint values are negative). -/
private theorem nine_h_sq_sub {h : ℝ} (h1 : (1.26:ℝ) ≤ h) (h2 : h ≤ 1.3) :
    9 * h ^ 2 - 17 * h + 3 < 0 := by
  have hp : (h - 1.26) * (h - 1.3) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hfac : 9 * h ^ 2 - 17 * h + 3 =
      -4.1316 + 6.04 * (h - 1.26) + 9 * ((h - 1.26) * (h - 1.3)) := by ring
  nlinarith

/-- On `[1.26, 1.3)` the quartic is strictly positive (`lmfun` is already
zero there, since `h ≥ h0 = 1.26`). -/
private theorem marchal_gt_lmfun_h0 {h : ℝ} (h1 : (1.26:ℝ) ≤ h) (h2 : h < 1.3) :
    lmfun h < marchalQuartic h := by
  have hs_lo : (1.41421356 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hA : (0:ℝ) < Real.sqrt 2 - h := by linarith
  have hB : h - hplus < 0 := by rw [hplus]; linarith
  have hC : 9 * h ^ 2 - 17 * h + 3 < 0 := nine_h_sq_sub h1 (le_of_lt h2)
  have hD : (0:ℝ) < (Real.sqrt 2 - 1) * 5 * (hplus - 1) := by
    have a : (0:ℝ) < Real.sqrt 2 - 1 := by linarith
    have b : (0:ℝ) < hplus - 1 := by rw [hplus]; norm_num
    positivity
  have hprod : 0 < (Real.sqrt 2 - h) * (h - hplus) * (9 * h ^ 2 - 17 * h + 3) := by
    have hB' : (0:ℝ) < -(h - hplus) := by linarith
    have hC' : (0:ℝ) < -(9 * h ^ 2 - 17 * h + 3) := by linarith
    have h2 : (0:ℝ) < (-(h - hplus)) * (-(9 * h ^ 2 - 17 * h + 3)) := mul_pos hB' hC'
    nlinarith [hA, h2]
  have hlm : lmfun h = 0 := by
    unfold lmfun
    by_cases hh : h ≤ h0
    · rw [if_pos hh, show h = h0 by linarith [show h0 = (1.26:ℝ) from rfl],
        sub_self, zero_div]
    · rw [if_neg hh]
  rw [hlm, marchalQuartic]
  exact div_pos hprod hD

/-! ## 3. The pinning -/

/-- `marchalQuartic h > lmfun h` for every `h ∈ [1.23176, 1.3)`. -/
theorem nb17_marchal_gt_lmfun {h : ℝ} (h1 : (1.23176 : ℝ) ≤ h) (h2 : h < 1.3) :
    lmfun h < marchalQuartic h := by
  by_cases hle : h ≤ 1.26
  · exact marchal_gt_lmfun_123176 h1 hle
  · exact marchal_gt_lmfun_h0 (le_of_lt (not_le.mp hle)) h2

/-- **The missing pinning**: `hminus ≤ 1.23176`.

Together with `Kepler.NliBanks7.hminus_ge_123175` this closes the Marchal root
to `[1.23175, 1.23176]` (true value `1.231754422…`), i.e.
`2·hminus ∈ [2.4635, 2.46352]`. -/
theorem nb17_hminus_le_123176 : hminus ≤ 1.23176 := by
  obtain ⟨h1, h2, hspec⟩ := mi_hminus_prop
  by_contra hcon
  have hcon' : (1.23176 : ℝ) < hminus := not_le.mp hcon
  have hgt := nb17_marchal_gt_lmfun (le_of_lt hcon') h2
  rw [hspec] at hgt
  exact absurd hgt (lt_irrefl _)

/-- Two-sided five-digit envelope: `hminus ∈ [1.23175, 1.23176]`. -/
theorem nb17_hminus_bounds : (1.23175 : ℝ) ≤ hminus ∧ hminus ≤ 1.23176 :=
  ⟨Kepler.NliBanks7.hminus_ge_123175, nb17_hminus_le_123176⟩

/-- Consumable form for the `RIBCYXUsym` box edges:
`2·hminus ∈ [2.4635, 2.46352]`. -/
theorem nb17_two_hminus_bounds :
    (2.4635 : ℝ) ≤ 2 * hminus ∧ 2 * hminus ≤ 2.46352 := by
  have h := nb17_hminus_bounds
  constructor <;> linarith [h.1, h.2]

/-- The bank box edge `2·hminus` stays strictly below the `lmfun` kink
`2·h0 = 2.52`; no kink split is needed on `RIBCYXUsym`'s box. -/
theorem nb17_two_hminus_lt_two_h0 : 2 * hminus < 2 * h0 := by
  have h : (2 * hminus : ℝ) ≤ 2 * 1.23176 := by linarith [nb17_hminus_le_123176]
  have hh : 2 * h0 = 2.52 := by rw [show h0 = (1.26:ℝ) from rfl]; norm_num
  linarith

/-! ## Axiom audit (house style) -/

#print axioms nb17_marchal_gt_lmfun
#print axioms nb17_hminus_le_123176
#print axioms nb17_hminus_bounds
#print axioms nb17_two_hminus_bounds
#print axioms nb17_two_hminus_lt_two_h0

end Kepler.NliBanks17
