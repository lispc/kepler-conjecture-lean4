/-
  BIEFJHU-a (HOL ineq entry `1965189142 a`, ineq.hl:1598) — G4 glue
  (schema-v3 hull / Taylor-model certificate route).

  Certificate: `Kepler.Interval.Cases.C1965189142aHull` — 184 leaves
  (175 `tm` + 9 `main`), `bb_arb --tm --ite-hull2 --tm-div2` on the widened
  box `[1, 1352914700/2^30] × [3,34] × [1,1]^4`; every leaf is a kernel
  `decide +kernel` on `checkPosTMHull`, and `C1965189142aHull_pos` glues them
  through `HullTree` (`splitOKB` cover, the `checkPosTMHull` analogue of
  `BBTreeG`/`bb_soundG`).
  Target: `Kepler.Text.bank_1965189142a` (PackingAuto21:437).

  `1352914700/2^30 = 1.2600000009…` is the dyadic *ceiling* of the HOL bound
  `1.26`, so the certificate box is a strict superset of the bank box (the
  original `1352914699/2^30 = 1.26 − 5.6e-10` did not reach `1.26`).

  No new `axiom` / `sorry` / `native_decide` — this module contains no
  `decide` at all: its inputs are the real identities, the box membership and
  the certificate's positivity lemma (hypothesis `hpos` of `pka_bief_close`).
-/
import Kepler.Text.PackingAuto21
import Kepler.Interval.Cases.C1965189142aHullBase
import Mathlib

set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Kepler.Text

/-! ## The certificate box -/

/-- The TM-certificate root box: `[1, 1352914700/2^30] × [3,34] × [1,1]^4`.
`1352914700/2^30 = 1.2600000009…` is the dyadic *ceiling* of the HOL bound
`1.26` (the P0' box-top fix: the original `1352914699/2^30 = 1.26 − 5.6e-10`
does not reach `1.26`).  The literal is the **normalised** dyadic form
(`338228675·2⁻²⁸`, odd mantissa) — an unnormalised literal for the same value
(`1352914700·2⁻³⁰`) changes `boxCenter`/`DInterval.mid`'s exponent scale and
makes `checkPosTMHull` return `false` (lane measurement, DELIVERY §4.4). -/
def pkaCertBox : Fin 6 → Kepler.Interval.DInterval :=
  ![⟨⟨1, 0⟩, ⟨338228675, -28⟩⟩, ⟨⟨3, 0⟩, ⟨34, 0⟩⟩, ⟨⟨1, 0⟩, ⟨1, 0⟩⟩,
    ⟨⟨1, 0⟩, ⟨1, 0⟩⟩, ⟨⟨1, 0⟩, ⟨1, 0⟩⟩, ⟨⟨1, 0⟩, ⟨1, 0⟩⟩]

/-! ## Real identities used by the gluing -/

/-- `arcsin u = 2 * arctan (u / (1 + sqrt (1 - u^2)))` on `(-1, 1)`
(the certificate's half-angle form). -/
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

/-- The certificate's `sqrt 3` replacement: `cos (π/6) * 2 = sqrt 3`. -/
private theorem pka_cos6 : Real.cos (Real.pi / 6) * 2 = Real.sqrt 3 := by
  rw [Real.cos_pi_div_six]; ring

/-- `sin (π/x2) ≤ sin (π/3) = √3/2` for `x2 ≥ 3`. -/
private theorem pka_sin_le {x2 : ℝ} (h2l : 3 ≤ x2) :
    Real.sin (Real.pi / x2) ≤ Real.sqrt 3 / 2 := by
  have hx2 : 0 < x2 := by linarith
  have h0 : -(Real.pi / 2) ≤ Real.pi / x2 := by
    have : 0 ≤ Real.pi / x2 := div_nonneg (le_of_lt Real.pi_pos) (by linarith)
    linarith [Real.pi_pos]
  have h1 : Real.pi / x2 ≤ Real.pi / 3 := by
    rw [div_le_div_iff₀ hx2 (by norm_num)]
    nlinarith [Real.pi_pos]
  have h2 : Real.pi / 3 ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two h0 h2 h1
  rwa [Real.sin_pi_div_three] at hsin

/-- The hybrid `sinH` ite equals `sin (π/x2)` on `[3, 34]`. -/
private theorem pka_sinh_ite (x2 : ℝ) (h2l : 3 ≤ x2) (h2h : x2 ≤ 34) :
    (if Real.pi / x2 - 3 / 4 < 0 then Real.sin (Real.pi / x2)
     else Real.cos |Real.pi / 2 - Real.pi / x2|) = Real.sin (Real.pi / x2) := by
  have hx2 : 0 < x2 := by linarith
  have hle : Real.pi / x2 ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hx2 (by norm_num)]
    nlinarith [Real.pi_pos]
  by_cases h : Real.pi / x2 - 3 / 4 < 0
  · simp only [h, if_true]
  · simp only [h, if_false]
    have hnn : 0 ≤ Real.pi / 2 - Real.pi / x2 := by linarith
    rw [abs_of_nonneg hnn, Real.cos_pi_div_two_sub]

/-- `q ≤ (1 + 1352914700/2^30) * (√3/4)` (crude but enough). -/
private theorem pka_q_le {x1 : ℝ} (h1l : 1 ≤ x1)
    (h1h : x1 ≤ 1352914700 / 1073741824) :
    x1 * Real.sqrt 3 / 4 + Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2 ≤
      (1352914700 / 1073741824 + 1) * (Real.sqrt 3 / 4) := by
  have hx1 : 0 < x1 := by linarith
  have hsq : (1 : ℝ) / 4 ≤ (x1 / 2) * (x1 / 2) := by nlinarith
  have hrad : 1 - (x1 / 2) * (x1 / 2) ≤ 3 / 4 := by nlinarith
  have h1 : Real.sqrt (1 - (x1 / 2) * (x1 / 2)) ≤ Real.sqrt (3 / 4) := by
    apply Real.sqrt_le_sqrt; linarith
  have h2 : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by
    rw [show (3 / 4 : ℝ) = 3 / 4 by norm_num,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3) (4 : ℝ)]
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h4]
  have h4 : x1 * Real.sqrt 3 / 4 ≤
      (1352914700 / 1073741824 : ℝ) * (Real.sqrt 3 / 4) := by
    have hpos : (0 : ℝ) < Real.sqrt 3 / 4 := by positivity
    calc x1 * Real.sqrt 3 / 4 = x1 * (Real.sqrt 3 / 4) := by ring
      _ ≤ (1352914700 / 1073741824) * (Real.sqrt 3 / 4) :=
          mul_le_mul_of_nonneg_right h1h (le_of_lt hpos)
  have h5 : Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2 ≤ Real.sqrt 3 / 4 := by
    calc Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2 ≤ (Real.sqrt 3 / 2) / 2 := by
          rw [h2] at h1; exact div_le_div_of_nonneg_right h1 (by norm_num)
      _ = Real.sqrt 3 / 4 := by ring
  calc x1 * Real.sqrt 3 / 4 + Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2
      ≤ (1352914700 / 1073741824) * (Real.sqrt 3 / 4) + Real.sqrt 3 / 4 := by
        linarith
    _ = (1352914700 / 1073741824 + 1) * (Real.sqrt 3 / 4) := by ring

/-- The certificate expression evaluates exactly to the real content of the
bank inequality: `2π − 2·asnFnhk − (0.591 − 0.0331·x2 + 0.506·lfunY1)`. -/
theorem pka_bief_eval (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 1 ≤ x1) (h1h : x1 ≤ 1352914700 / 1073741824) (h2l : 3 ≤ x2)
    (h2h : x2 ≤ 34)
    (h3l : 1 ≤ x3) (h3h : x3 ≤ 1) (h4l : 1 ≤ x4) (h4h : x4 ≤ 1)
    (h5l : 1 ≤ x5) (h5h : x5 ≤ 1) (h6l : 1 ≤ x6) (h6h : x6 ≤ 1) :
    (Kepler.Interval.Cases.C1965189142aHullExpr).evalReal ![x1, x2, x3, x4, x5, x6] =
      2 * Real.pi - 2 * asnFnhk x1 x2 x3 x4 x5 x6
        - (0.591 - 0.0331 * x2 + 0.506 * lfunY1 x1 x2 x3 x4 x5 x6) := by
  have hx2 : 0 < x2 := by linarith
  -- side condition: the arcsin argument stays in (-1, 1)
  have hu1 : -1 < (x1 * Real.sqrt 3 / 4 + Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2) *
      Real.sin (Real.pi / x2) := by
    have h0 : 0 ≤ x1 * Real.sqrt 3 / 4 + Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2 := by
      positivity
    have h1 : 0 ≤ Real.sin (Real.pi / x2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        (div_nonneg (le_of_lt Real.pi_pos) (by linarith))
        (by rw [div_le_iff₀ hx2]; nlinarith [Real.pi_pos])
    nlinarith
  have hu2 : (x1 * Real.sqrt 3 / 4 + Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2) *
      Real.sin (Real.pi / x2) < 1 := by
    have hsin := pka_sin_le (x2 := x2) h2l
    have hsin0 : 0 ≤ Real.sin (Real.pi / x2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        (div_nonneg (le_of_lt Real.pi_pos) (by linarith))
        (by rw [div_le_iff₀ hx2]; nlinarith [Real.pi_pos])
    have hq := pka_q_le (x1 := x1) h1l h1h
    have hq0 : 0 ≤ x1 * Real.sqrt 3 / 4 + Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2 := by
      positivity
    have hprod : (x1 * Real.sqrt 3 / 4 + Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2) *
        Real.sin (Real.pi / x2) ≤
          ((1352914700 / 1073741824 + 1) * (Real.sqrt 3 / 4)) *
            (Real.sqrt 3 / 2) := by
      apply mul_le_mul hq hsin hsin0 (by positivity)
    have hnum : ((1352914700 / 1073741824 + 1) * (Real.sqrt 3 / 4)) *
        (Real.sqrt 3 / 2) < 1 := by
      have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
      have he : ((1352914700 / 1073741824 + 1) * (Real.sqrt 3 / 4)) *
          (Real.sqrt 3 / 2)
          = (1352914700 / 1073741824 + 1) * (Real.sqrt 3 * Real.sqrt 3) / 8 := by
        ring
      rw [he, hsq]; norm_num
    linarith
  unfold asnFnhk lfunY1 lfun h0 sqrt3
  dsimp only [Kepler.Interval.Cases.C1965189142aHullExpr,
    Kepler.Interval.IExpr.evalReal, Kepler.Interval.transReal]
  simp only [Kepler.Interval.Dyadic.toReal_def, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.isValue, pow_zero, mul_one, one_mul,
    Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, zpow_zero, zpow_one,
    pow_two, Nat.reducePow]
  have hpi4 : (4 : ℝ) * Real.arctan 1 = Real.pi := by
    rw [Real.arctan_one]; ring
  have h34 : (3 : ℝ) * 2 ^ (-2 : ℤ) = 3 / 4 := by
    rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg]
    norm_num
  simp only [h34, hpi4, pka_cos6, pka_sinh_ite x2 h2l h2h]
  -- fold the arcsin argument (both sides now share the `*`-form radicand)
  set u : ℝ := (x1 * Real.sqrt 3 / 4 + Real.sqrt (1 - (x1 / 2) * (x1 / 2)) / 2) *
      Real.sin (Real.pi / x2) with hu
  have harc : 2 * Real.arctan (u / (1 + Real.sqrt (1 - u * u))) = Real.arcsin u :=
    pka_two_atan u hu1 hu2
  simp only [harc]
  rw [hu]
  norm_num

/-- BIEFJHU-a box membership: the bank hypotheses put the point inside the
certificate box (whose top `1352914700/2^30 = 1.2600000009…` covers the HOL
bound `1.26`). -/
theorem pka_bief_mem (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : 1 ≤ x1) (h1h : x1 ≤ 1.26) (h2l : 3 ≤ x2) (h2h : x2 ≤ 34)
    (h3l : 1 ≤ x3) (h3h : x3 ≤ 1) (h4l : 1 ≤ x4) (h4h : x4 ≤ 1)
    (h5l : 1 ≤ x5) (h5h : x5 ≤ 1) (h6l : 1 ≤ x6) (h6h : x6 ≤ 1) :
    Kepler.Interval.boxMem pkaCertBox ![x1, x2, x3, x4, x5, x6] := by
  intro i
  fin_cases i <;>
    simp only [pkaCertBox,
      Kepler.Interval.DInterval.mem,
      Kepler.Interval.Dyadic.toReal_def, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Fin.isValue, Int.cast_ofNat, Nat.cast_ofNat,
      zpow_zero, pow_two, Nat.reducePow] <;>
    norm_num <;>
    constructor <;> norm_num <;> linarith

/-- **BIEFJHU-a closed, modulo the TM certificate's positivity lemma.**

`hpos` is exactly what the schema-v3 hull certificate module proves —
`∀ ρ, boxMem C1965189142aHullBox ρ → 0 < C1965189142aHullExpr.evalReal ρ`
(the `HullTree.sound` corollary of its 184-leaf `checkPosTMHull` tree) — see
`Kepler.Interval.Cases.C1965189142aHull._pos`.  Given it, the bank inequality
follows from the real identity `pka_bief_eval` and `linarith`. -/
theorem pka_bief_close
    (hpos : ∀ ρ : Fin 6 → ℝ, Kepler.Interval.boxMem pkaCertBox ρ →
      0 < Kepler.Interval.Cases.C1965189142aHullExpr.evalReal ρ) :
    bank_1965189142a := by
  intro x1 x2 x3 x4 x5 x6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hb1h : x1 ≤ 1352914700 / 1073741824 := by
    have h : (1.26 : ℝ) ≤ 1352914700 / 1073741824 := by norm_num
    linarith
  have hmem := pka_bief_mem x1 x2 x3 x4 x5 x6 h1l h1h h2l h2h h3l h3h
    h4l h4h h5l h5h h6l h6h
  have hp := hpos ![x1, x2, x3, x4, x5, x6] hmem
  have hev := pka_bief_eval x1 x2 x3 x4 x5 x6 h1l hb1h h2l h2h h3l h3h
    h4l h4h h5l h5h h6l h6h
  rw [hev] at hp
  linarith

#print axioms pka_bief_close

end Kepler.Text
