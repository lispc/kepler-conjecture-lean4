/-
Kepler.Text.TaylorSecond.HminusTight — lane `wt1-hminus-tight-w1`.

Sixteen-digit two-sided pinning of the Marchal root `hminus`
(`pack_defs.hl:153`), for the wt1 covering lane's root-box tiling:

  `1.2317544220900045 ≤ hminus ≤ 1.2317544220903218`,
  `2.463508844180009 ≤ 2·hminus ≤ 2.4635088441806436`.

True value `hminus = 1.23175442209030439013286771549980055524…` (60 dps), so the
two endpoints keep margins `3.0e−13` / `1.7e−13`.  This is the *same mechanism* as
HOL's `hminus_interval` (`reference/flyspeck/text_formalization/nonlinear/
formal_tests/hminus.hl:209` = `[1.2317544220903043901, 1.2317544220903047]`,
registered as a verifier constant at `:223`), only ~1000× coarser — the same
three-piece split `[1.2, r₋]`, `[r₊, 1.26]`, `[1.26, 1.3)` with endpoint sign
checks (HOL `verify_ineq default_params 12`).

Certificates: same cleared-quartic shape as
`Kepler.NliBanks7.marchalQuartic_lt_lmfun_123175` (lower) and
`Kepler.NliBanks17.marchal_gt_lmfun_123176` (upper), but with a **16-digit**
bracket `1.4142135623730950 < √2 < 1.4142135623730952` — the 8-digit bracket of
the five-digit templates cannot resolve the new endpoints.  After substituting
`t = r₋ − h` (resp. `t = h − r₊`), the cleared difference is
`c₀ + t·R(t)` with `c₀ > 0` an exact rational of size `1.0e−13` (resp. `6.0e−15`)
and `R` a cubic that is positive on `[0, T]` with margin `≈ 0.3`; the tiny
margin lives **only** in the rational constant `c₀`.
-/
import Kepler.NliBanks17

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

/-! ## 16-digit enclosures of `√2` -/

theorem sqrt2_gt_16 : (1.4142135623730950 : ℝ) < Real.sqrt 2 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

theorem sqrt2_lt_16 : Real.sqrt 2 < 1.4142135623730952 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-! ## 1. Lower piece `[1.2, 1.2317544220900045]` -/

/-- `marchalQuartic h < lmfun h` on `[1.2, 1.2317544220900045]`; with
`mi_hminus_prop` this gives `1.2317544220900045 ≤ hminus`. -/
theorem marchal_lt_lmfun_tight {h : ℝ} (h1 : (1.2 : ℝ) ≤ h)
    (h2 : h ≤ 1.2317544220900045) : marchalQuartic h < lmfun h := by
  have hs_lo : (1.4142135623730950 : ℝ) < Real.sqrt 2 := sqrt2_gt_16
  have hs_hi : Real.sqrt 2 < 1.4142135623730952 := sqrt2_lt_16
  have hD : (0:ℝ) < (Real.sqrt 2 - 1) * 5 * (hplus - 1) := by
    have a : (0:ℝ) < Real.sqrt 2 - 1 := by linarith
    have b : (0:ℝ) < hplus - 1 := by rw [hplus]; norm_num
    positivity
  have hDlo : (0:ℝ) < (1.4142135623730950 - 1) * 5 * (hplus - 1) := by
    have b : (0:ℝ) < hplus - 1 := by rw [hplus]; norm_num
    positivity
  have hDge : (1.4142135623730950 - 1) * 5 * (hplus - 1)
      ≤ (Real.sqrt 2 - 1) * 5 * (hplus - 1) := by
    have b : (0:ℝ) < 5 * (hplus - 1) := by rw [hplus]; norm_num
    nlinarith [hs_lo]
  have hA : (0:ℝ) < Real.sqrt 2 - h := by linarith
  have hB : (0:ℝ) < hplus - h := by rw [hplus]; linarith
  have hC : (0:ℝ) < 17 * h - 9 * h ^ 2 - 3 := by
    have hp1 : (0:ℝ) ≤ h - 1.2 := by linarith
    have hp2 : (0:ℝ) ≤ 1.2317544220900045 - h := by linarith
    have hprod : (0:ℝ) ≤ (h - 1.2) * (1.2317544220900045 - h) := mul_nonneg hp1 hp2
    nlinarith [hprod]
  have hE : (0:ℝ) < h0 - h := by rw [h0]; linarith
  have hE1 : (0:ℝ) < h0 - 1 := by rw [h0]; norm_num
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
  have hkey : (0:ℝ) < (h0 - h) * ((1.4142135623730950 - 1) * 5 * (hplus - 1)) -
      (1.4142135623730952 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1) := by
    rw [show h0 = (1.26:ℝ) from rfl, show hplus = (1.3254:ℝ) from rfl]
    have ht0 : (0:ℝ) ≤ 1.2317544220900045 - h := by linarith
    have htT : 1.2317544220900045 - h ≤ 0.0317544220900045 := by linarith
    have h2t : (1.2317544220900045 - h) ^ 2
        ≤ 0.0317544220900045 * (1.2317544220900045 - h) := by nlinarith
    have h3t : (1.2317544220900045 - h) ^ 3
        ≤ 0.0317544220900045 ^ 2 * (1.2317544220900045 - h) := by nlinarith
    have h4t : (0:ℝ) ≤ (1.2317544220900045 - h) ^ 4 := by positivity
    nlinarith [ht0, htT, h2t, h3t, h4t]
  rw [hmq, hlm, div_lt_div_iff₀ hD hE1]
  have hBCE : (0:ℝ) < (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1) :=
    mul_pos (mul_pos hB hC) hE1
  have hltA : Real.sqrt 2 - h < 1.4142135623730952 - h := by linarith
  have hp : (Real.sqrt 2 - h) * ((hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1))
      < (1.4142135623730952 - h) * ((hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1)) :=
    mul_lt_mul_of_pos_right hltA hBCE
  have step1 : (Real.sqrt 2 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1)
      < (1.4142135623730952 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1) := by
    linarith [hp]
  have hDge' : (h0 - h) * ((1.4142135623730950 - 1) * 5 * (hplus - 1))
      ≤ (h0 - h) * ((Real.sqrt 2 - 1) * 5 * (hplus - 1)) :=
    mul_le_mul_of_nonneg_left hDge hE.le
  linarith [step1, hDge', hkey]



/-! ## 2. Upper piece `[1.2317544220903218, 1.26]` -/

/-- On `[1.2317544220903218, 1.26]` the quartic is strictly above the linear cap.
Same cleared certificate as `Kepler.NliBanks17.marchal_gt_lmfun_123176`, with the
16-digit `√2` bracket; the leftover margin of the five-digit version
(`1.9e−6` at the endpoint) has shrunk to `6.0e−15`. -/
private theorem marchal_gt_lmfun_tight_low {h : ℝ} (h1 : (1.2317544220903218 : ℝ) ≤ h)
    (h2 : h ≤ 1.26) : lmfun h < marchalQuartic h := by
  have hs_lo : (1.4142135623730950 : ℝ) < Real.sqrt 2 := sqrt2_gt_16
  have hs_hi : Real.sqrt 2 < 1.4142135623730952 := sqrt2_lt_16
  have hD : (0:ℝ) < (Real.sqrt 2 - 1) * 5 * (hplus - 1) := by
    have a : (0:ℝ) < Real.sqrt 2 - 1 := by linarith
    have b : (0:ℝ) < hplus - 1 := by rw [hplus]; norm_num
    positivity
  have hDhi : (Real.sqrt 2 - 1) * 5 * (hplus - 1)
      ≤ (1.4142135623730952 - 1) * 5 * (hplus - 1) := by
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
  have hkey : (0:ℝ) < (1.4142135623730950 - h) * (hplus - h) * (17 * h - 9 * h ^ 2 - 3) *
        (h0 - 1) - (h0 - h) * ((1.4142135623730952 - 1) * 5 * (hplus - 1)) := by
    rw [show h0 = (1.26:ℝ) from rfl, show hplus = (1.3254:ℝ) from rfl]
    have ht0 : (0:ℝ) ≤ h - 1.2317544220903218 := by linarith
    have htT : h - 1.2317544220903218 ≤ 0.0282455779096782 := by linarith
    have h2t : (h - 1.2317544220903218) ^ 2
        ≤ 0.0282455779096782 * (h - 1.2317544220903218) := by nlinarith
    have h3t : (h - 1.2317544220903218) ^ 3
        ≤ 0.0282455779096782 ^ 2 * (h - 1.2317544220903218) := by nlinarith
    have h4t : (0:ℝ) ≤ (h - 1.2317544220903218) ^ 4 := by positivity
    nlinarith [ht0, htT, h2t, h3t, h4t]
  rw [hmq, hlm, div_lt_div_iff₀ hE1 hD]
  have hBCE : (0:ℝ) < (hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1) :=
    mul_pos (mul_pos hB hC) hE1
  have hlo : (1.4142135623730950 - h) * ((hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1))
      < (Real.sqrt 2 - h) * ((hplus - h) * (17 * h - 9 * h ^ 2 - 3) * (h0 - 1)) :=
    mul_lt_mul_of_pos_right (by linarith) hBCE
  have hDhi' : (h0 - h) * ((Real.sqrt 2 - 1) * 5 * (hplus - 1))
      ≤ (h0 - h) * ((1.4142135623730952 - 1) * 5 * (hplus - 1)) :=
    mul_le_mul_of_nonneg_left hDhi hE
  nlinarith [hlo, hDhi', hkey]

/-- `lmfun h < marchalQuartic h` on the whole right side
`[1.2317544220903218, 1.3)`: the tight piece `[·, 1.26]` above, then the landed
`Kepler.NliBanks17.nb17_marchal_gt_lmfun` on `[1.23176, 1.3)` (which covers
`[1.26, 1.3)`, the `lmfun = 0` branch, `hminus.hl:37` `bounds3`). -/
theorem marchal_gt_lmfun_tight {h : ℝ} (h1 : (1.2317544220903218 : ℝ) ≤ h)
    (h2 : h < 1.3) : lmfun h < marchalQuartic h := by
  by_cases hle : h ≤ 1.26
  · exact marchal_gt_lmfun_tight_low h1 hle
  · exact Kepler.NliBanks17.nb17_marchal_gt_lmfun (by linarith) h2

/-! ## 3. The sixteen-digit pinning -/

/-- **Sixteen-digit two-sided pinning** of the Marchal root
(`hminus.hl:209` shape, ~1000× coarser than HOL's
`[1.2317544220903043901, 1.2317544220903047]`). -/
theorem hminus_bounds_tight :
    (1.2317544220900045 : ℝ) ≤ hminus ∧ hminus ≤ 1.2317544220903218 := by
  obtain ⟨h1, h2, hspec⟩ := mi_hminus_prop
  constructor
  · by_contra hcon
    have hcon' : hminus < 1.2317544220900045 := not_le.mp hcon
    have hlt := marchal_lt_lmfun_tight (h := hminus) h1 (le_of_lt hcon')
    rw [hspec] at hlt
    exact absurd hlt (lt_irrefl _)
  · by_contra hcon
    have hcon' : (1.2317544220903218 : ℝ) < hminus := not_le.mp hcon
    have hgt := marchal_gt_lmfun_tight (le_of_lt hcon') h2
    rw [hspec] at hgt
    exact absurd hgt (lt_irrefl _)

/-- Consumable edge form for the wt1 root box:
`2·hminus ∈ [2.463508844180009, 2.4635088441806436]`. -/
theorem two_hminus_bounds_tight :
    (2.463508844180009 : ℝ) ≤ 2 * hminus ∧ 2 * hminus ≤ 2.4635088441806436 := by
  have h := hminus_bounds_tight
  constructor <;> linarith [h.1, h.2]

/-! ## Axiom audit (house style) -/

#print axioms sqrt2_gt_16
#print axioms sqrt2_lt_16
#print axioms marchal_gt_lmfun_tight_low
#print axioms marchal_lt_lmfun_tight
#print axioms marchal_gt_lmfun_tight
#print axioms hminus_bounds_tight
#print axioms two_hminus_bounds_tight

end Kepler.Text.TaylorSecond
