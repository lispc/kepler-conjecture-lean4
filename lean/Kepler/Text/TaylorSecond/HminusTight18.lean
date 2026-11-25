/-
Kepler.Text.TaylorSecond.HminusTight18 — lane `wt1-hminus-tight-w1`, round 2.

Incremental tightening for the wt1 root-box tiling (glue lane's exact review): the
root-box edges are `min y4lo = 246350884418000923/10^17` and
`max y5hi = 2463508844180643489/10^18`, i.e. half-edges

  `r₋ = 1.231754422090004615`, `r₊ = 1.2317544220903217445`,

so `hminus ∈ [r₋, r₊]` with margins `3.00e−13` / `1.74e−14` against the true root
`1.23175442209030439013286771549980055524…`.  This file re-runs only the two
cleared-quartic certificates of `Kepler.Text.TaylorSecond.HminusTight` at the new
endpoints; **nothing landed is modified** — `HminusTight.lean` is imported and its
public 16-digit `√2` brackets `sqrt2_gt_16` / `sqrt2_lt_16` are reused (not
reproved), so the arithmetic core here is byte-for-byte the round-1 certificate
with the endpoint literals swapped.

Endpoint margins of the cleared certificates (exact rational arithmetic, see
`REPORT.md`):

| piece | `√2` bracket | `hkey` at the new endpoint |
|---|---|---|
| lower `[1.2, r₋]` | 16-digit (reused) | `+1.0291066e−13` |
| upper `[r₊, 1.26]` | 16-digit (reused) | `+5.9466336e−15` |

Structure unchanged from round 1: three pieces (HOL `hminus.hl:36-37` split), with
`[1.26, 1.3)` still delegated to `Kepler.NliBanks17.nb17_marchal_gt_lmfun`.
-/
import Kepler.Text.TaylorSecond.HminusTight

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

/-! ## 1. Lower piece `[1.2, 1.231754422090004615]` -/

/-- `marchalQuartic h < lmfun h` on `[1.2, 1.231754422090004615]`; with
`mi_hminus_prop` this gives `1.231754422090004615 ≤ hminus`. -/
theorem marchal_lt_lmfun_tight18 {h : ℝ} (h1 : (1.2 : ℝ) ≤ h)
    (h2 : h ≤ 1.231754422090004615) : marchalQuartic h < lmfun h := by
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
    have hp2 : (0:ℝ) ≤ 1.231754422090004615 - h := by linarith
    have hprod : (0:ℝ) ≤ (h - 1.2) * (1.231754422090004615 - h) := mul_nonneg hp1 hp2
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
    have ht0 : (0:ℝ) ≤ 1.231754422090004615 - h := by linarith
    have htT : 1.231754422090004615 - h ≤ 0.031754422090004615 := by linarith
    have h2t : (1.231754422090004615 - h) ^ 2
        ≤ 0.031754422090004615 * (1.231754422090004615 - h) := by nlinarith
    have h3t : (1.231754422090004615 - h) ^ 3
        ≤ 0.031754422090004615 ^ 2 * (1.231754422090004615 - h) := by nlinarith
    have h4t : (0:ℝ) ≤ (1.231754422090004615 - h) ^ 4 := by positivity
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



/-! ## 2. Upper piece `[1.2317544220903217445, 1.26]` -/

/-- On `[1.2317544220903217445, 1.26]` the quartic is strictly above the linear cap.
Same cleared certificate as `Kepler.NliBanks17.marchal_gt_lmfun_123176`, with the
16-digit `√2` bracket (reused, not reproved); the leftover margin of the five-digit version
(`1.9e−6` at the endpoint) is now `5.95e−15`. -/
private theorem marchal_gt_lmfun_tight18_low {h : ℝ} (h1 : (1.2317544220903217445 : ℝ) ≤ h)
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
    have ht0 : (0:ℝ) ≤ h - 1.2317544220903217445 := by linarith
    have htT : h - 1.2317544220903217445 ≤ 0.0282455779096782555 := by linarith
    have h2t : (h - 1.2317544220903217445) ^ 2
        ≤ 0.0282455779096782555 * (h - 1.2317544220903217445) := by nlinarith
    have h3t : (h - 1.2317544220903217445) ^ 3
        ≤ 0.0282455779096782555 ^ 2 * (h - 1.2317544220903217445) := by nlinarith
    have h4t : (0:ℝ) ≤ (h - 1.2317544220903217445) ^ 4 := by positivity
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
`[1.2317544220903217445, 1.3)`: the tight piece `[·, 1.26]` above, then the landed
`Kepler.NliBanks17.nb17_marchal_gt_lmfun` on `[1.23176, 1.3)` (which covers
`[1.26, 1.3)`, the `lmfun = 0` branch, `hminus.hl:37` `bounds3`). -/
theorem marchal_gt_lmfun_tight18 {h : ℝ} (h1 : (1.2317544220903217445 : ℝ) ≤ h)
    (h2 : h < 1.3) : lmfun h < marchalQuartic h := by
  by_cases hle : h ≤ 1.26
  · exact marchal_gt_lmfun_tight18_low h1 hle
  · exact Kepler.NliBanks17.nb17_marchal_gt_lmfun (by linarith) h2

/-! ## 3. The round-2 pinning -/

/-- **Round-2 two-sided pinning**: exactly the wt1 root-box half-edges. -/
theorem hminus_bounds_tight18 :
    (1.231754422090004615 : ℝ) ≤ hminus ∧ hminus ≤ 1.2317544220903217445 := by
  obtain ⟨h1, h2, hspec⟩ := mi_hminus_prop
  constructor
  · by_contra hcon
    have hcon' : hminus < 1.231754422090004615 := not_le.mp hcon
    have hlt := marchal_lt_lmfun_tight18 (h := hminus) h1 (le_of_lt hcon')
    rw [hspec] at hlt
    exact absurd hlt (lt_irrefl _)
  · by_contra hcon
    have hcon' : (1.2317544220903217445 : ℝ) < hminus := not_le.mp hcon
    have hgt := marchal_gt_lmfun_tight18 (le_of_lt hcon') h2
    rw [hspec] at hgt
    exact absurd hgt (lt_irrefl _)

/-- Consumable edge form, exactly the root-box decimal strings:
`2·hminus ∈ [2.46350884418000923, 2.463508844180643489]`. -/
theorem two_hminus_bounds_tight18 :
    (2.46350884418000923 : ℝ) ≤ 2 * hminus ∧ 2 * hminus ≤ 2.463508844180643489 := by
  have h := hminus_bounds_tight18
  constructor <;> linarith [h.1, h.2]

/-! ## Axiom audit (house style) -/

#print axioms marchal_lt_lmfun_tight18
#print axioms marchal_gt_lmfun_tight18_low
#print axioms marchal_gt_lmfun_tight18
#print axioms hminus_bounds_tight18
#print axioms two_hminus_bounds_tight18

end Kepler.Text.TaylorSecond
