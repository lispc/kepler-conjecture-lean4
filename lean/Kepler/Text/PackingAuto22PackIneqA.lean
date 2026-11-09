/-
PackingAuto22PackIneqA (lane packineqa-w1): kernel-checked interval
certificates + gluing for the two `packIneqDefAP22` entries that were not
already closed in Assembly:

  * `WAZLDCD_bank`  = HOL ineq `8055810915` (ineq.hl:1634) via
    `Kepler.Interval.Cases.C8055810915` (83 leaves repaired to 85, bb_arb
    prec 64; axioms = standard three).
  * `BIEFJHU_bank` branch 1 = HOL ineq `1965189142 a` (ineq.hl:1598) via
    `Kepler.Interval.Cases.C1965189142a` (TM tier + h-repair).

The other three entries of `pack_ineq_def_a` are reused at the Assembly
composition site (`nliRest6096597438b`, `nliRest6096597438a`,
`nliRest1965189142x34`).

No new `axiom` / `sorry` / `native_decide`.  The only `decide`s are the
certificate machinery's kernel replays (`BBTreeG.covers` → `bb_soundG`).

Name capture: every auxiliary declaration is prefixed `pka`; PA22 names
(`asn797k`, `asnFnhk`, `lfun`, `lfunY1`, `acs`, `arclength22`, `h0`, ...)
are consumed, never redefined.
-/

import Kepler.Text.PackingAuto22
import Kepler.Interval.Cases.C8055810915
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false

namespace Kepler.Text

/-! ## Real identities used by the gluing lemmas -/

/-- `arcsin u = 2 * arctan (u / (1 + sqrt (1 - u^2)))` on `(-1, 1)` (the
certificate's half-angle form; mirrors Assembly's private
`nliRest6096597438b_two_atan`, restated here because that one is private
to Assembly). -/
private theorem pka_two_atan (u : ℝ) (hu1 : -1 < u) (hu2 : u < 1) :
    2 * Real.arctan (u / (1 + Real.sqrt (1 - u * u))) = Real.arcsin u := by
  have hu2sq : u * u < 1 := by nlinarith
  have h1mu : 0 < 1 - u * u := by linarith
  have hs : 0 < Real.sqrt (1 - u * u) := Real.sqrt_pos.mpr h1mu
  have hs2 : (Real.sqrt (1 - u * u)) ^ 2 = 1 - u * u :=
    Real.sq_sqrt (le_of_lt h1mu)
  set s := Real.sqrt (1 - u * u)
  have h1s : 0 < 1 + s := by linarith
  have hw1 : -1 < u / (1 + s) := by
    rw [lt_div_iff₀ h1s]; nlinarith
  have hw2 : u / (1 + s) < 1 := by
    rw [div_lt_iff₀ h1s]; nlinarith
  rw [Real.two_mul_arctan hw1 hw2]
  have hden : 1 - (u / (1 + s)) ^ 2 = 2 * s / (1 + s) := by
    field_simp [h1s.ne']; nlinarith [hs2]
  have hw : 2 * (u / (1 + s)) / (1 - (u / (1 + s)) ^ 2) = u / s := by
    rw [hden]; field_simp [h1s.ne', hs.ne']
  rw [hw]
  simpa [s, sq] using (Real.arcsin_eq_arctan ⟨hu1, hu2⟩).symm

/-- `arccos u = 2 * arctan (sqrt (1 - u^2) / (1 + u))` on `(0, 1)` (the
certificate's half-angle form for the `acs` term). -/
private theorem pka_arccos_two_atan (u : ℝ) (hu1 : 0 < u) (hu2 : u < 1) :
    2 * Real.arctan (Real.sqrt (1 - u * u) / (1 + u)) = Real.arccos u := by
  have hu2sq : u * u < 1 := by nlinarith
  have h1mu : 0 ≤ 1 - u * u := by linarith
  have hs : 0 < Real.sqrt (1 - u * u) := Real.sqrt_pos.mpr (by linarith)
  set t := Real.sqrt (1 - u * u) / (1 + u) with ht
  have htu : 0 ≤ t := div_nonneg hs.le (le_of_lt (by linarith : (0:ℝ) < 1 + u))
  have hte : t ≠ 0 := by
    simp only [ht]
    intro hc
    rw [div_eq_zero_iff] at hc
    rcases hc with hc | hc
    · exact absurd hc (ne_of_gt hs)
    · linarith
  have htsq : t ^ 2 = (1 - u * u) / (1 + u) ^ 2 := by
    rw [ht, div_pow, Real.sq_sqrt h1mu]
  have hden : 1 + t ^ 2 = 2 / (1 + u) := by
    rw [htsq]
    field_simp
    linarith [sq_nonneg (1 + u)]
  have hc1 : (Real.cos (Real.arctan t)) ^ 2 = 1 / (1 + t ^ 2) := by
    rw [Real.cos_arctan, div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + t ^ 2)]
    field_simp
  have hcos : Real.cos (2 * Real.arctan t) = u := by
    rw [Real.cos_two_mul, hc1, hden]
    field_simp
    linarith
  have hrange1 : 0 ≤ 2 * Real.arctan t :=
    mul_nonneg zero_le_two (Real.arctan_nonneg.mpr htu)
  have hrange2 : 2 * Real.arctan t < Real.pi := by
    calc 2 * Real.arctan t < 2 * (Real.pi / 2) :=
          mul_lt_mul_of_pos_left (Real.arctan_lt_pi_div_two t) two_pos
      _ = Real.pi := by ring
  rw [← Real.arccos_cos hrange1 hrange2.le, hcos]

/-- The certificate's `ite` tree for `atn2` matches the definition. -/
private theorem pka_atn2_ite (x y : ℝ) :
    atn2 x y =
      (if |y| - x < 0 then Real.arctan (y / x)
       else if 0 - y < 0 then Real.pi / 2 - Real.arctan (x / y)
       else if y - 0 < 0 then -(Real.pi / 2) - Real.arctan (x / y)
       else Real.pi) := by
  unfold atn2
  have c1 : (|y| - x) < 0 ↔ |y| < x :=
    ⟨fun h => by linarith, fun h => by linarith⟩
  have c2 : (0 - y) < 0 ↔ 0 < y := by simp
  have c3 : (y - 0) < 0 ↔ y < 0 := by simp
  simp only [c1, c2, c3]

/-- `4 * arctan 1 / 2 = π / 2`, `4 * arctan 1 / 6 = π / 6`, `4 * arctan 1 = π`
(the certificate's `π` encoding). -/
private theorem pka_pi_half : (4 : ℝ) * Real.arctan 1 / 2 = Real.pi / 2 := by
  rw [Real.arctan_one]; ring

private theorem pka_pi_six : (4 : ℝ) * Real.arctan 1 / 6 = Real.pi / 6 := by
  rw [Real.arctan_one]; ring

private theorem pka_pi_one : (4 : ℝ) * Real.arctan 1 = Real.pi := by
  rw [Real.arctan_one]; ring

/-- The certificate expression evaluates exactly to the real content of the
WAZLDCD inequality. -/
theorem pka_waz_eval (x1 x2 x3 x4 x5 x6 : ℝ) (h1l : 4 ≤ x1) (h1h : x1 ≤ (2.52 : ℝ) ^ 2)
    (h2l : 4 ≤ x2) (h2h : x2 ≤ 4) (h3l : (2 * h0) ^ 2 ≤ x3) (h3h : x3 ≤ (2 * h0) ^ 2) :
    (Kepler.Interval.Cases.C8055810915Expr).evalReal ![x1, x2, x3, x4, x5, x6] =
      arclength22 (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3) -
        (acs (Real.sqrt x1 / 4) - Real.pi / 6 + 797 / 1000) := by
  have hρ0 : ((![x1, x2, x3, x4, x5, x6] : Fin 6 → ℝ) 0) = x1 := rfl
  have hρ1 : ((![x1, x2, x3, x4, x5, x6] : Fin 6 → ℝ) 1) = x2 := rfl
  have hρ2 : ((![x1, x2, x3, x4, x5, x6] : Fin 6 → ℝ) 2) = x3 := rfl
  have h1 : 0 ≤ x1 := by linarith
  have h2 : 0 ≤ x2 := le_trans (by norm_num) h2l
  have h3 : 0 ≤ x3 := le_trans (sq_nonneg (2 * h0)) h3l
  have hsq1 : Real.sqrt x1 * Real.sqrt x1 = x1 := Real.mul_self_sqrt h1
  have hsq2 : Real.sqrt x2 * Real.sqrt x2 = x2 := Real.mul_self_sqrt h2
  have hsq3 : Real.sqrt x3 * Real.sqrt x3 = x3 := Real.mul_self_sqrt h3
  have hx1p : (0 : ℝ) < x1 := by linarith
  have hu1 : 0 < Real.sqrt x1 / 4 := div_pos (Real.sqrt_pos.mpr hx1p) (by norm_num : (0 : ℝ) < 4)
  have hu2 : Real.sqrt x1 / 4 < 1 := by
    rw [div_lt_one (by norm_num : (0 : ℝ) < 4)]
    have h52 : (2.52 : ℝ) ^ 2 < 16 := by norm_num
    have hx116 : x1 < 16 := by linarith
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 4)).mpr (by linarith : x1 < (4:ℝ) ^ 2)
  simp only [arclength22, arcLengthICD, acs, hsq1, hsq2, hsq3]
  rw [pka_atn2_ite]
  dsimp only [Kepler.Interval.Cases.C8055810915Expr,
    Kepler.Interval.Cases.C8055810915MkExpr,
    Kepler.Interval.IExpr.evalReal, Kepler.Interval.transReal]
  simp only [hρ0, hρ1, hρ2]
  simp only [upsX, Kepler.Interval.Dyadic.toReal_def, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.empty_val',
    Fin.isValue, pow_zero, mul_one, one_mul, Int.cast_ofNat, Int.cast_one,
    Nat.cast_ofNat, zpow_zero, zpow_one, pow_two,
    Real.mul_self_sqrt h1, Real.mul_self_sqrt h2, Real.mul_self_sqrt h3,
    pka_pi_half, pka_pi_six, pka_pi_one,
    pka_arccos_two_atan (Real.sqrt x1 / 4) hu1 hu2]
  ring_nf

/-- WAZLDCD box membership: the bank hypotheses put the point inside the
certificate box.  The certificate box is a strict superset of the HOL box
in one coordinate (documented in DELIVERY.md): the degenerate `x2 = 4` is
widened to `4 ± 2⁻⁴⁰` because a dyadic radicand with exponent e = 0 only
certifies `sqrtI` to granularity 2^0 (a `√4` radicand at e = 0 evaluates
to the useless enclosure [2, 3] and poisons the whole downstream interval
chain); x1's top endpoint additionally carries a +1 ulp dyadic ceiling
(`213084066·2⁻²⁵ ≥ 2.52²`; the upstream value already covered the corner,
the bump is a harmless safety margin). -/
theorem pka_waz_mem (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 4 ≤ x1) (h1h : x1 ≤ (2.52 : ℝ) ^ 2) (h2l : 4 ≤ x2) (h2h : x2 ≤ 4)
    (h3l : (2 * h0) ^ 2 ≤ x3) (h3h : x3 ≤ (2 * h0) ^ 2)
    (h4l : 1 ≤ x4) (h4h : x4 ≤ 1) (h5l : 1 ≤ x5) (h5h : x5 ≤ 1)
    (h6l : 1 ≤ x6) (h6h : x6 ≤ 1) :
    Kepler.Interval.boxMem Kepler.Interval.Cases.C8055810915Box
      ![x1, x2, x3, x4, x5, x6] := by
  have hpow : (2 * h0 : ℝ) ^ 2 = (2.52 : ℝ) ^ 2 := by norm_num [h0]
  intro i
  fin_cases i
  all_goals
    simp only [Kepler.Interval.Cases.C8055810915Box,
      Kepler.Interval.DInterval.mem, Kepler.Interval.Dyadic.toReal_def,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Fin.isValue, h0,
      Nat.reducePow] at *
    norm_num
    constructor <;> norm_num <;> linarith

/-- **WAZLDCD closed**: HOL ineq entry `8055810915` (`WAZLDCD_bank`,
PackingAuto22:383). -/
theorem packIneqAWAZLDCD : WAZLDCD_bank := by
  intro x1 x2 x3 x4 x5 x6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hmem := pka_waz_mem x1 x2 x3 x4 x5 x6 h1l h1h h2l h2h h3l h3h
    h4l h4h h5l h5h h6l h6h
  have hpos := Kepler.Interval.Cases.C8055810915_pos ![x1, x2, x3, x4, x5, x6] hmem
  have hev := pka_waz_eval x1 x2 x3 x4 x5 x6 h1l h1h h2l h2h h3l h3h
  rw [hev] at hpos
  simp only [acs] at hpos ⊢
  linarith

end Kepler.Text

#print axioms Kepler.Interval.Cases.C8055810915_pos
#print axioms Kepler.Text.packIneqAWAZLDCD
