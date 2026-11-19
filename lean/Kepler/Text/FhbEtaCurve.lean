/-
Kepler.Text.FhbEtaCurve — lane `fhb-seam-curve-w1`, 2026-11-18.

FHBVYXZa η126 **seam-curve algebraic kit and reduction interfaces**.

`bank_FHBVYXZa` (PA21:629-640, Assembly `nliRestFHBVYXZa`) is the disjunction
`γ4 > 0 ∨ rad2 > 2 ∨ η126² < 1.34²` on the B0 box `[2hmin,2hplus]×[2,2hmin]⁵`.
The b0-joint-envelope-w1 numeric recon (B0_MASTER_PROPOSAL §4.3) showed the
two-branch reduction is the right route: split on `η126² < 1.7956` (the third
disjunct, since `1.7956 = 1.34² = 4489/2500`); on the guard `{η126² ≥ 4489/2500}`
prove `γ4 > 0` (the first disjunct). The rad2 disjunct is not used. The true
minimum of `γ4` on the guard is `+7.3623e-3`, attained at
`(2hplus, 2.05892…, 2, 2, 2, 2)` — five coordinates on box faces and `y2` at an
*interior* point of the algebraic curve `{η126² = 4489/2500}` — so no corner
table can see it (hence the seam-curve certificate).

This file proves, with no `sorry`/`axiom`/`native_decide` (axiom-audited at
the bottom):

1. `fhb_eta_sq` — `eta_y y1 y2 y6 ^ 2` is the rational quotient
   `y1²y2²y6² / upsX (y1²) (y2²) (y6²)` on B0 (where `upsX > 0`, junk-free);
2. `fhb_boundary_quad` — on B0, `η126² = 4489/2500` iff the rational quadratic
   `fhbQuad (y1²) (y6²) (y2²) = 0`: the η-boundary is an algebraic curve;
3. `fhb_disc` — the factorised discriminant
   `x1·x6·(625x1−4489)·(625x6−4489)/390625`, and `fhb_quad_root` /
   `fhbX2Root_is_root` — the explicit radical root of the boundary quadratic
   (the `y6 = 2` slice used by the seam curve);
4. the reduction interfaces (each fully proven, hard analysis isolated as
   hypotheses, in the style of `Gamma4WideBanks` / `NliBanks9`):
   * `nliRestFHBVYXZa_of_eta_disj` — bank ← `∀ y ∈ B0, η² < 1.7956 ∨ γ4 > 0`;
   * `fhb_eta_disj_of_hba` — disjunction ← `hba` (the η-guard certificate);
   * `fhb_hba_of_floor3` — `hba` ← y3/y4/y5 floor monotonicity `m3 m4 m5`
     (each `∂γ4/∂yi ≥ +1.9e-2` on B0 numerically) + 3-D guard positivity
     `g3pos` (the seam-analysis residual, see below).

Remaining hard obligations (exact statements + margins in the lane
`Evidence.md`): the three floor-monotonicity signs `m3 m4 m5`; the 3-D guard
positivity `g3pos` (no-interior-critical-point + seven boundary-piece
certificates: seam surface `S`, faces `y1=2hplus/2hmin`, `y6=2`, `y2=2`,
tops `y2=2hmin`, `y6=2hmin`; the binding leaf is the **1-D seam-curve
certificate** `γ4(y1, y2*(y1), 2⁴) ≥ 7e-3` on `y1 ∈ [2hmin, 2hplus]`, with
`y2*(y1) = √fhbX2Root(y1²) ∈ [2.0579, 2.4290] ⊆ [2, 2hmin]`); and the curve
box-containment / root-two-sided bounds.
-/

import Kepler.Text.PackingAuto21
import Kepler.Text.Gamma4WideBanks
import Kepler.NliBanks17

set_option maxHeartbeats 4000000

namespace Kepler.Text

/-! ## 1. The η126 squared quotient -/

/-- On the B0 box `eta_y y1 y2 y6 ^ 2` is the rational quotient
`y1²y2²y6² / upsX (y1²) (y2²) (y6²)` (the `sqrt` squares back; `upsX > 0`
on B0 makes the quotient junk-free). -/
theorem fhb_eta_sq (y1 y2 y6 : ℝ) (h1 : (2:ℝ) ≤ y1) (h1' : y1 < 4)
    (h2 : (2:ℝ) ≤ y2) (h2' : y2 < 4) (h6 : (2:ℝ) ≤ y6) (h6' : y6 < 4) :
    eta_y y1 y2 y6 ^ 2
      = y1 * y1 * (y2 * y2) * (y6 * y6)
        / upsX (y1 * y1) (y2 * y2) (y6 * y6) := by
  have hups := mi_UPS_X_POS y1 y2 y6 h1 h1' h2 h2' h6 h6'
  have hy1 : (0:ℝ) ≤ y1 := by linarith
  have hy2 : (0:ℝ) ≤ y2 := by linarith
  have hy6 : (0:ℝ) ≤ y6 := by linarith
  have hP : (0:ℝ) ≤ y1 * y1 * (y2 * y2) * (y6 * y6) := by positivity
  have hquo : (0:ℝ) ≤ y1 * y1 * (y2 * y2) * (y6 * y6)
      / upsX (y1 * y1) (y2 * y2) (y6 * y6) := div_nonneg hP hups.le
  simp only [eta_y, etaY, etaX, pow_two, Real.mul_self_sqrt hquo]

/-- `upsX` positivity packed for the B0 box. -/
theorem fhb_upsX_pos {y1 y2 y6 : ℝ} (h1 : (2:ℝ) ≤ y1) (h1' : y1 ≤ 2 * hplus)
    (h2 : (2:ℝ) ≤ y2) (h2' : y2 ≤ 2 * hminus) (h6 : (2:ℝ) ≤ y6)
    (h6' : y6 ≤ 2 * hminus) :
    0 < upsX (y1 * y1) (y2 * y2) (y6 * y6) := by
  have h1lt4 : y1 < 4 := by
    have hhp : 2 * hplus < 4 := by
      have hhp2 : hplus = 1.3254 := rfl
      linarith
    linarith
  have h2lt4 : y2 < 4 := by linarith [mi_hminus_prop.2.1]
  have h6lt4 : y6 < 4 := by linarith [mi_hminus_prop.2.1]
  exact mi_UPS_X_POS y1 y2 y6 h1 h1lt4 h2 h2lt4 h6 h6lt4

/-! ## 2. The boundary quadratic (η126² = 4489/2500)

In x-coordinates `xi = yi²` the boundary `η126² = 4489/2500` is
`x1·x2·x6 = (4489/2500)·upsX x1 x2 x6`, a quadratic in `x2 = y2²` with
rational coefficients (B0_MASTER_PROPOSAL §4.3). -/

/-- Leading coefficient `A = 4489/2500`. -/
noncomputable def fhbQA : ℝ := 4489 / 2500

/-- Linear coefficient `B = ab − (4489/1250)(a+b)` (parameters `a = x1`,
`b = x6`). -/
noncomputable def fhbQB (a b : ℝ) : ℝ := a * b - 4489 / 1250 * (a + b)

/-- Constant coefficient `C = (4489/2500)(a−b)²`. -/
noncomputable def fhbQC (a b : ℝ) : ℝ := 4489 / 2500 * (a - b) * (a - b)

/-- The boundary quadratic `A·c² + B·c + C` in `c = x2`. -/
noncomputable def fhbQuad (a b c : ℝ) : ℝ := fhbQA * (c * c) + fhbQB a b * c + fhbQC a b

/-- Definitional unfolding of `fhbQuad`. -/
theorem fhbQuad_eq (a b c : ℝ) :
    fhbQuad a b c = 4489 / 2500 * (c * c)
      + (a * b - 4489 / 1250 * (a + b)) * c + 4489 / 2500 * (a - b) * (a - b) :=
  rfl

/-- The η-boundary identity:
`x1·x2·x6 − (4489/2500)·upsX x1 x2 x6 = fhbQuad x1 x6 x2`. -/
theorem fhb_quad_ident (x1 x2 x6 : ℝ) :
    x1 * x2 * x6 - 4489 / 2500 * upsX x1 x2 x6 = fhbQuad x1 x6 x2 := by
  simp only [upsX, fhbQuad, fhbQA, fhbQB, fhbQC]; ring

/-- On B0, `η126² = 4489/2500` iff `fhbQuad (y1²) (y6²) (y2²) = 0`. -/
theorem fhb_boundary_quad {y1 y2 y6 : ℝ} (h1 : (2:ℝ) ≤ y1) (h1' : y1 ≤ 2 * hplus)
    (h2 : (2:ℝ) ≤ y2) (h2' : y2 ≤ 2 * hminus) (h6 : (2:ℝ) ≤ y6)
    (h6' : y6 ≤ 2 * hminus) :
    eta_y y1 y2 y6 ^ 2 = 4489 / 2500 ↔ fhbQuad (y1 * y1) (y6 * y6) (y2 * y2) = 0 := by
  have hups := fhb_upsX_pos h1 h1' h2 h2' h6 h6'
  have h1lt4 : y1 < 4 := by
    have hhp : 2 * hplus < 4 := by
      have hhp2 : hplus = 1.3254 := rfl
      linarith
    linarith
  have h2lt4 : y2 < 4 := by linarith [mi_hminus_prop.2.1]
  have h6lt4 : y6 < 4 := by linarith [mi_hminus_prop.2.1]
  rw [fhb_eta_sq y1 y2 y6 h1 h1lt4 h2 h2lt4 h6 h6lt4]
  have hkey : y1 * y1 * (y2 * y2) * (y6 * y6)
      - 4489 / 2500 * upsX (y1 * y1) (y2 * y2) (y6 * y6)
      = fhbQuad (y1 * y1) (y6 * y6) (y2 * y2) := by
    rw [fhb_quad_ident]
  constructor
  · intro he
    have heq : y1 * y1 * (y2 * y2) * (y6 * y6)
        = 4489 / 2500 * upsX (y1 * y1) (y2 * y2) (y6 * y6) := by
      rw [div_eq_iff hups.ne'] at he
      exact he
    have hz : fhbQuad (y1 * y1) (y6 * y6) (y2 * y2) = 0 := by
      rw [← hkey]
      linarith
    exact hz
  · intro hq
    have hz : y1 * y1 * (y2 * y2) * (y6 * y6)
        - 4489 / 2500 * upsX (y1 * y1) (y2 * y2) (y6 * y6) = 0 := by
      rw [hkey]
      exact hq
    have heq : y1 * y1 * (y2 * y2) * (y6 * y6)
        = 4489 / 2500 * upsX (y1 * y1) (y2 * y2) (y6 * y6) := by linarith
    rw [div_eq_iff hups.ne']
    exact heq

/-- Factorised discriminant of `fhbQuad a b ·`:
`B² − 4AC = a·b·(625a−4489)·(625b−4489)/390625`. -/
theorem fhb_disc (a b : ℝ) :
    fhbQB a b * fhbQB a b - 4 * fhbQA * fhbQC a b
      = a * b * (625 * a - 4489) * (625 * b - 4489) / 390625 := by
  simp only [fhbQB, fhbQA, fhbQC]; ring

/-! ## 3. The explicit seam-curve root (y6 = 2 slice)

With `y6 = 2` (`x6 = 4`), for `y1 ∈ [2hmin, 2hplus]` the boundary value
`x2 = y2*²` is the larger root of `fhbQuad x1 4 · = 0`; numerically
`y2* ∈ [2.0579, 2.4290] ⊆ [2, 2hmin]` (lane recon). The root needs the
discriminant nonnegative — on the slice `x1 ∈ [2.4635², 2.6508²]` and
`x6 = 4` both factors `625x1−4489 < 0`, `625x6−4489 = −1989 < 0` make
`D > 0`. -/

/-- The explicit `x2`-root of the boundary quadratic at `x6 = 4`:
`c = (1250/4489)·(−B + √D)` with `D` the factorised discriminant. -/
noncomputable def fhbX2Root (x1 : ℝ) : ℝ :=
  (1250 / 4489) * (-(x1 * 4 - 4489 / 1250 * (x1 + 4))
    + Real.sqrt (x1 * 4 * (625 * x1 - 4489) * (625 * 4 - 4489) / 390625))

/-- The discriminant of the `x6 = 4` slice. -/
noncomputable def fhbD4 (x1 : ℝ) : ℝ :=
  x1 * 4 * (625 * x1 - 4489) * (625 * 4 - 4489) / 390625

/-- Nonnegativity hypothesis packaged: `0 ≤ fhbD4 x1` (on the slice this is
strict, witness `fhbX2Root_is_root`). -/
theorem fhbX2Root_is_root {x1 : ℝ} (hD : 0 ≤ fhbD4 x1) :
    fhbQuad x1 4 (fhbX2Root x1) = 0 := by
  have hsq : Real.sqrt (x1 * 4 * (625 * x1 - 4489) * (625 * 4 - 4489) / 390625)
      * Real.sqrt (x1 * 4 * (625 * x1 - 4489) * (625 * 4 - 4489) / 390625)
      = x1 * 4 * (625 * x1 - 4489) * (625 * 4 - 4489) / 390625 := by
    have h := Real.mul_self_sqrt hD
    simpa [fhbD4] using h
  simp only [fhbX2Root, fhbQuad, fhbQA, fhbQB, fhbQC]
  linear_combination (625 / 4489 : ℝ) * hsq

/-- The discriminant is strictly positive on the `y6 = 2` slice over the
whole `y1`-range (`x1 = y1² ∈ [2.4635², 2.6508²]`, both factors
`625x1−4489 < 0`, `625·4−4489 = −1989 < 0`). -/
theorem fhbD4_pos {y1 : ℝ} (h1 : 2 * hminus ≤ y1) (h1' : y1 ≤ 2 * hplus) :
    0 < fhbD4 (y1 * y1) := by
  have hm := Kepler.NliBanks17.nb17_two_hminus_bounds
  have hy1lo : (2.4635:ℝ) ≤ y1 := le_trans hm.1 h1
  have hy1hi : y1 ≤ 2.6508 := by
    have e : (2:ℝ) * hplus = 2.6508 := by norm_num [hplus]
    linarith
  have hx1 : (6.06883225:ℝ) ≤ y1 * y1 ∧ y1 * y1 ≤ 7.02674064 := by
    constructor <;> nlinarith
  have hna : (0:ℝ) < -(625 * (y1 * y1) - 4489) := by nlinarith [hx1.2]
  have hnb : (0:ℝ) < -(625 * 4 - 4489) := by norm_num
  have hy1sq : (0:ℝ) < y1 * y1 := by nlinarith [hy1lo]
  have hprod : (0:ℝ)
      < y1 * y1 * 4 * (625 * (y1 * y1) - 4489) * (625 * 4 - 4489) := by
    have e : y1 * y1 * 4 * (625 * (y1 * y1) - 4489) * (625 * 4 - 4489)
        = y1 * y1 * 4 * (-(625 * (y1 * y1) - 4489)) * (-(625 * 4 - 4489)) := by
      ring
    rw [e]
    positivity
  unfold fhbD4
  exact div_pos hprod (by norm_num : (0:ℝ) < 390625)

/-- Two-sided bounds for the explicit root on the slice:
`4.23 < fhbX2Root (y1²) < 5.90` (numerically `[4.2392, 5.8919]`). -/
theorem fhbX2Root_bounds {y1 : ℝ} (h1 : 2 * hminus ≤ y1) (h1' : y1 ≤ 2 * hplus) :
    (4.23:ℝ) < fhbX2Root (y1 * y1) ∧ fhbX2Root (y1 * y1) < 5.90 := by
  have hm := Kepler.NliBanks17.nb17_two_hminus_bounds
  have hy1lo : (2.4635:ℝ) ≤ y1 := le_trans hm.1 h1
  have hy1hi : y1 ≤ 2.6508 := by
    have e : (2:ℝ) * hplus = 2.6508 := by norm_num [hplus]
    linarith
  have hx1 : (6.06883225:ℝ) ≤ y1 * y1 ∧ y1 * y1 ≤ 7.02674064 := by
    constructor <;> nlinarith
  -- work with the atom `x = y1²` to keep `nlinarith` degrees low
  set x := y1 * y1 with hx_def
  have hxlo : (6.06883225:ℝ) ≤ x := by rw [hx_def]; exact hx1.1
  have hxhi : x ≤ 7.02674064 := by rw [hx_def]; exact hx1.2
  have hprod : (0:ℝ) ≤ (7.02674064 - x) * (x - 6.06883225) :=
    mul_nonneg (sub_nonneg.mpr hxhi) (sub_nonneg.mpr hxlo)
  -- discriminant bounds: D decreasing in x, D ∈ (13.91, 86.03)
  have hDlo : (13.91:ℝ) < fhbD4 x := by
    rw [show fhbD4 x = x * 4 * (625 * x - 4489) * (625 * 4 - 4489) / 390625 from rfl,
      lt_div_iff₀ (by norm_num : (0:ℝ) < 390625),
      show (625:ℝ) * 4 - 4489 = -1989 from by norm_num]
    nlinarith [hxlo, hxhi, hprod]
  have hDhi : fhbD4 x < 86.03 := by
    rw [show fhbD4 x = x * 4 * (625 * x - 4489) * (625 * 4 - 4489) / 390625 from rfl,
      div_lt_iff₀ (by norm_num : (0:ℝ) < 390625),
      show (625:ℝ) * 4 - 4489 = -1989 from by norm_num]
    nlinarith [hxlo, hxhi, hprod]
  -- sqrt bounds: s ∈ (3.71, 9.28)
  have hslo : (3.71:ℝ) < Real.sqrt (fhbD4 x) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [hDlo]
  have hshi : Real.sqrt (fhbD4 x) < 9.28 := by
    have h1 : fhbD4 x < (9.28:ℝ) ^ 2 := by nlinarith [hDhi]
    have h2 : Real.sqrt (fhbD4 x) < Real.sqrt ((9.28:ℝ) ^ 2) :=
      Real.sqrt_lt_sqrt (by positivity) h1
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 9.28)] at h2
    exact h2
  -- linear coefficient bounds: Bx = fhbQB x 4 ∈ (−11.89, −11.492)
  have hB1 : (-11.89:ℝ) < x * 4 - 4489 / 1250 * (x + 4) := by
    nlinarith [hxlo, hxhi]
  have hB2 : x * 4 - 4489 / 1250 * (x + 4) < (-11.492:ℝ) := by
    nlinarith [hxlo, hxhi]
  constructor
  · rw [show fhbX2Root x = (1250 / 4489) * (-(x * 4 - 4489 / 1250 * (x + 4))
        + Real.sqrt (fhbD4 x)) from rfl]
    nlinarith
  · rw [show fhbX2Root x = (1250 / 4489) * (-(x * 4 - 4489 / 1250 * (x + 4))
        + Real.sqrt (fhbD4 x)) from rfl]
    nlinarith

/-- The seam-curve boundary point `y2*(y1) = √(fhbX2Root (y1²))`. -/
noncomputable def fhbY2Star (y1 : ℝ) : ℝ := Real.sqrt (fhbX2Root (y1 * y1))

/-- The seam curve lies strictly inside the box on the whole slice:
`2 < y2*(y1) < 2hminus` (numerically `[2.0579, 2.4290]`). -/
theorem fhbY2Star_mem_box {y1 : ℝ} (h1 : 2 * hminus ≤ y1)
    (h1' : y1 ≤ 2 * hplus) :
    (2:ℝ) < fhbY2Star y1 ∧ fhbY2Star y1 < 2 * hminus := by
  have hm := Kepler.NliBanks17.nb17_two_hminus_bounds
  have hb := fhbX2Root_bounds h1 h1'
  have hroot_nn : (0:ℝ) ≤ fhbX2Root (y1 * y1) := by linarith [hb.1]
  have hsq : fhbY2Star y1 * fhbY2Star y1 = fhbX2Root (y1 * y1) := by
    unfold fhbY2Star
    exact Real.mul_self_sqrt hroot_nn
  have hlo : (2.05:ℝ) < fhbY2Star y1 := by
    unfold fhbY2Star
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [hb.1]
  have hhi : fhbY2Star y1 < 2.43 := by
    have h1 : fhbX2Root (y1 * y1) < (2.43:ℝ) ^ 2 := by nlinarith [hb.2]
    have h2 : fhbY2Star y1 < Real.sqrt ((2.43:ℝ) ^ 2) :=
      Real.sqrt_lt_sqrt hroot_nn h1
    rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.43)] at h2
    exact h2
  exact ⟨by linarith, lt_of_lt_of_le hhi (by linarith [hm.2])⟩

/-- The seam curve is on the boundary: `η126(y1, y2*(y1), 2)² = 4489/2500`
for every `y1 ∈ [2hmin, 2hplus]`. -/
theorem fhbY2Star_boundary {y1 : ℝ} (h1 : 2 * hminus ≤ y1)
    (h1' : y1 ≤ 2 * hplus) :
    eta_y y1 (fhbY2Star y1) 2 ^ 2 = 4489 / 2500 := by
  have hm := Kepler.NliBanks17.nb17_two_hminus_bounds
  have hy1lo : (2:ℝ) ≤ y1 := by linarith [le_trans hm.1 h1]
  have hm2 := fhbY2Star_mem_box h1 h1'
  have hr := fhbX2Root_is_root (fhbD4_pos h1 h1').le
  have hb := fhb_boundary_quad hy1lo h1' hm2.1.le hm2.2.le
    (by norm_num : (2:ℝ) ≤ 2) (by linarith [hm.2] : (2:ℝ) ≤ 2 * hminus)
  rw [hb]
  have hsq : (fhbY2Star y1) * (fhbY2Star y1) = fhbX2Root (y1 * y1) := by
    have hroot_nn : (0:ℝ) ≤ fhbX2Root (y1 * y1) := by
      linarith [fhbX2Root_bounds h1 h1']
    unfold fhbY2Star
    exact Real.mul_self_sqrt hroot_nn
  rw [hsq]
  have e42 : (4:ℝ) = 2 * 2 := by norm_num
  rw [e42] at hr
  exact hr

/-! ## 4. Reduction interfaces -/

/-- **Bank ← η-disjunction.** If on B0 either `η126² < 1.7956` (third
disjunct, as `1.7956 = 1.34²`) or `γ4 > 0` (first disjunct), the bank holds.
The rad2 disjunct is not used. -/
theorem nliRestFHBVYXZa_of_eta_disj
    (h : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      eta_y y1 y2 y6 ^ 2 < 1.7956 ∨
        0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun) :
    bank_FHBVYXZa := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  rcases h y1 y2 y3 y4 y5 y6
      ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩ with heta | hg
  · refine Or.inr (Or.inr ?_)
    have h17956 : (1.7956:ℝ) ≤ 1.34 ^ 2 := by norm_num
    exact lt_of_lt_of_le heta h17956
  · exact Or.inl hg

/-- **Disjunction ← hba.** Splitting on `η126² < 1.7956` vs `≥ 4489/2500`
(the same cut, since `4489/2500 = 1.7956`). -/
theorem fhb_eta_disj_of_hba
    (hba : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      4489 / 2500 ≤ eta_y y1 y2 y6 ^ 2 →
        0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun) :
    ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      eta_y y1 y2 y6 ^ 2 < 1.7956 ∨
        0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  intro y1 y2 y3 y4 y5 y6 hb
  by_cases hcut : eta_y y1 y2 y6 ^ 2 < 1.7956
  · exact Or.inl hcut
  · refine Or.inr (hba y1 y2 y3 y4 y5 y6 hb ?_)
    have e : (4489 / 2500 : ℝ) = 1.7956 := by norm_num
    rw [e]
    exact not_lt.mp hcut

/-- **hba ← floor monotonicity + 3-D guard positivity.**
The floor monotonicity hypotheses `m3 m4 m5` say `γ4` is nondecreasing in
each of `y3, y4, y5` over `[2, 2hmin]` (other coordinates fixed in the box).
Numerically `∂γ4/∂y3 ≥ +1.9e-2`, `∂γ4/∂y4 ≥ +3.4e-2`, `∂γ4/∂y5 ≥ +2.9e-2`
on the whole B0 box (50-point random recon, lane Evidence.md), so `m3 m4 m5`
hold; the formal derivative-sign proofs are the outstanding obligation.
`g3pos` is positivity on the floor 3-D guard
`{y3=y4=y5=2, η126² ≥ 4489/2500} ⊆ [2hmin,2hplus]×[2,2hmin]²` — the
seam-analysis residual whose leaf is the 1-D curve certificate of §3. -/
theorem fhb_hba_of_floor3
    (m3 : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      gamma4fgcy y1 y2 2 y4 y5 y6 lmfun ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun)
    (m4 : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      gamma4fgcy y1 y2 y3 2 y5 y6 lmfun ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun)
    (m5 : ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      gamma4fgcy y1 y2 y3 y4 2 y6 lmfun ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun)
    (g3pos : ∀ y1 y2 y6, (2 * hminus ≤ y1 ∧ y1 ≤ 2 * hplus ∧
      2 ≤ y2 ∧ y2 ≤ 2 * hminus ∧ 2 ≤ y6 ∧ y6 ≤ 2 * hminus) →
      4489 / 2500 ≤ eta_y y1 y2 y6 ^ 2 →
        0 < gamma4fgcy y1 y2 2 2 2 y6 lmfun) :
    ∀ y1 y2 y3 y4 y5 y6, g4wB5 y1 y2 y3 y4 y5 y6 →
      4489 / 2500 ≤ eta_y y1 y2 y6 ^ 2 →
        0 < gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  intro y1 y2 y3 y4 y5 y6 hb hguard
  have hbS := hb
  obtain ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩ := hb
  have hb3 : g4wB5 y1 y2 2 y4 y5 y6 :=
    ⟨h1l, h1h, h2l, h2h, le_refl (2:ℝ), mi_two_le_two_hminus, h4l, h4h,
      h5l, h5h, h6l, h6h⟩
  have hstep3 := m3 y1 y2 y3 y4 y5 y6 hbS
  have hstep4 := m4 y1 y2 2 y4 y5 y6 hb3
  have hstep5 := m5 y1 y2 2 2 y5 y6
    ⟨h1l, h1h, h2l, h2h, le_refl (2:ℝ), mi_two_le_two_hminus,
      le_refl (2:ℝ), mi_two_le_two_hminus, h5l, h5h, h6l, h6h⟩
  have hg3 : 0 < gamma4fgcy y1 y2 2 2 2 y6 lmfun :=
    g3pos y1 y2 y6 ⟨h1l, h1h, h2l, h2h, h6l, h6h⟩ hguard
  exact lt_of_lt_of_le hg3 (le_trans hstep5 (le_trans hstep4 hstep3))

/-! ## 5. Axiom audit -/

#print axioms fhb_eta_sq
#print axioms fhb_boundary_quad
#print axioms fhb_disc
#print axioms fhbX2Root_is_root
#print axioms fhbD4_pos
#print axioms fhbX2Root_bounds
#print axioms fhbY2Star_mem_box
#print axioms fhbY2Star_boundary
#print axioms nliRestFHBVYXZa_of_eta_disj
#print axioms fhb_eta_disj_of_hba
#print axioms fhb_hba_of_floor3

end Kepler.Text
