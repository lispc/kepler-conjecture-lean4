/-
Kepler.Text.NliQitnpea12ArctanSeries — lane `fat1-g3-exact-w1` (2026-11-19).

Robust replacement for the Hermite envelopes of the QITNPEA1_1_2 algebraization
(scout `nli-algebraize-fat1-scout-w1`, repaired ledger `nli-algebraize-fat1-w2`).

Math.  The exact identity on `[0,∞)`
    1/(1+u²) = Σ_{i=0}^{N} (-u²)ⁱ + (-u²)^{N+1}/(1+u²)
integrates (FTC) to
    arctan x = S_N(x) + (-1)^{N+1} · R_N(x),
    S_N(x) = Σ_{i=0}^{N} (-1)ⁱ x^{2i+1}/(2i+1),  R_N(x) = ∫₀ˣ u^{2N+2}/(1+u²) ≥ 0.
For N = 2m+1 odd and `t ≤ 0` (x = -t ≥ 0):
    arctan t = -arctan x ≤ -S_{2m+1}(x) = S_{2m+1}(t),
an EXACT upper bound with rational coefficients — no anchors, no endpoint
arctan enclosures, no error budget: the w2 Hermite layer (and its 1e-15
"minA" G3 criticality, an artifact of tangent contact plus a 60-dps rounding
misselection in `g3_compare.py`) disappears entirely.  This is the same
alternating bound as Flyspeck `formal_ineqs/trig/atn.hl` (`atn_poly_bound`,
`atn_poly_pos_upper_bound`), proved there via Leibniz series; here the
integral remainder makes it a one-page FTC lemma.  Instantiations: m = 0 is
`arctan t ≤ t - t³/3` on `(-∞,0]`; m = 1 is exactly w2's
`nliq12_arctan_le_t7_neg`; m = 9 (degree 39) is the certificate used for the
negative atan groups of `bank_QITNPEA1_1_2`.

Use.  With cs_g < 0 and `t_g ≤ t̂_g ≤ 0` (s_hi ≥ √Δ side, in-tree direction
lemmas `g4v_div_sqrt_pos_mem/neg_mem`), `cs_g · arctan t_g ≥ cs_g · S_{2m+1}(t̂_g)`,
so γ4 ≥ G(y) = s_lo(Δ)/12 + 8·mm1 + (π/2)·Σ cs_g + Σ cs_g·S_{2m+1}(t̂_g) — a
single-√ exact lower bound.  Grid spot-check (mpmath 60 dps, n=4, ESTIMATE):
min G ≈ 0.0798 over both y1 half-boxes vs the 0.0114 threshold; slack
γ4 - G ≥ +7e-4 pointwise.  Machine numbers are navigation, not certificates.

No `sorry`/`axiom`/`native_decide`.
-/
import Mathlib

set_option maxHeartbeats 4000000

namespace Kepler.Text

open intervalIntegral
open Set

/-- Alternating-Taylor UPPER bound of `arctan` on `(-∞,0]`, general degree:
for `t ≤ 0`,
`arctan t ≤ S_{2m+1}(t) = ∑_{i=0}^{2m+1} (-1)ⁱ t^{2i+1}/(2i+1)`.
Proof: `d/dt [arctan - S_{2m+1}] = t^{4m+4}/(1+t²) ≥ 0` on `(-∞,0]`
(geometric sum for `S'`), vanishes at `0`, hence `arctan - S ≤ 0` left of `0`. -/
theorem nliq12_arctan_le_alt_series_neg (m : ℕ) (t : ℝ) (ht : t ≤ 0) :
    Real.arctan t ≤ ∑ i ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ i * t ^ (2 * i + 1)
      / (2 * i + 1) := by
  -- geometric sum: (1+u²) · Σ_{i=0}^{2m+1} (-u²)ⁱ = 1 - u^{4m+4}
  have hg : ∀ u : ℝ, (∑ i ∈ Finset.range (2 * m + 2), ((-u ^ 2) : ℝ) ^ i) * (1 + u ^ 2)
      = 1 - u ^ (4 * m + 4) := by
    intro u
    induction m with
    | zero =>
      have hr : 2 * (0 : ℕ) + 2 = 1 + 1 := rfl
      rw [hr, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        pow_zero, pow_one]
      ring
    | succ k ih =>
      have hs : (∑ i ∈ Finset.range (2 * (k + 1) + 2), ((-u ^ 2) : ℝ) ^ i)
          = (∑ i ∈ Finset.range (2 * k + 2), ((-u ^ 2) : ℝ) ^ i)
            + ((-u ^ 2) : ℝ) ^ (2 * k + 2) + ((-u ^ 2) : ℝ) ^ (2 * k + 3) := by
        have h2 : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by ring
        rw [h2, Finset.sum_range_succ, Finset.sum_range_succ]
      have e2 : ((-u ^ 2) : ℝ) ^ (2 * k + 2) = u ^ (4 * k + 4) := by
        rw [Even.neg_pow (show Even (2 * k + 2) from ⟨k + 1, by ring⟩), ← pow_mul,
          show 2 * (2 * k + 2) = 4 * k + 4 from by ring]
      have e3 : ((-u ^ 2) : ℝ) ^ (2 * k + 3) = -(u ^ (4 * k + 6)) := by
        rw [Odd.neg_pow (show Odd (2 * k + 3) from ⟨k + 1, by ring⟩), ← pow_mul,
          show 2 * (2 * k + 3) = 4 * k + 6 from by ring]
      rw [hs, e2, e3, add_mul, add_mul, ih]
      ring
  -- deriv of the truncation sum, termwise + total
  have hPderiv : ∀ u : ℝ, deriv (fun v : ℝ => ∑ i ∈ Finset.range (2 * m + 2),
      (-1 : ℝ) ^ i * v ^ (2 * i + 1) / (2 * i + 1)) u
      = ∑ i ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ i * u ^ (2 * i) := by
    intro u
    have hdif : ∀ i ∈ Finset.range (2 * m + 2),
        DifferentiableAt ℝ (fun v : ℝ => (-1 : ℝ) ^ i * v ^ (2 * i + 1) / (2 * i + 1)) u := by
      intro i _
      fun_prop
    rw [deriv_fun_sum hdif]
    apply Finset.sum_congr rfl
    intro i _
    have h2i : (2 : ℝ) * i + 1 ≠ 0 := by positivity
    have e1 : (fun v : ℝ => (-1 : ℝ) ^ i * v ^ (2 * i + 1) / (2 * i + 1))
        = fun v : ℝ => (-1 : ℝ) ^ i / (2 * i + 1) * v ^ (2 * i + 1) := by
      funext v
      ring
    rw [e1, deriv_const_mul ((-1 : ℝ) ^ i / (2 * i + 1)) (differentiableAt_id.pow (2 * i + 1)),
      deriv_pow_field]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    field_simp
  have hP : ∀ u : ℝ, HasDerivAt (fun v : ℝ => ∑ i ∈ Finset.range (2 * m + 2),
      (-1 : ℝ) ^ i * v ^ (2 * i + 1) / (2 * i + 1))
      (∑ i ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ i * u ^ (2 * i)) u := by
    intro u
    have hdif : ∀ i ∈ Finset.range (2 * m + 2),
        DifferentiableAt ℝ (fun v : ℝ => (-1 : ℝ) ^ i * v ^ (2 * i + 1) / (2 * i + 1)) u := by
      intro i _
      fun_prop
    rw [← hPderiv u]
    exact (DifferentiableAt.fun_sum (u := Finset.range (2 * m + 2)) hdif).hasDerivAt
  -- (arctan - S)' = t^{4m+4}/(1+t²) ≥ 0
  have hF : deriv (fun u : ℝ => Real.arctan u - (∑ i ∈ Finset.range (2 * m + 2),
      (-1 : ℝ) ^ i * u ^ (2 * i + 1) / (2 * i + 1)))
      = fun u => u ^ (4 * m + 4) / (1 + u ^ 2) := by
    funext u
    have hd : HasDerivAt (fun v : ℝ => Real.arctan v - (∑ i ∈ Finset.range (2 * m + 2),
        (-1 : ℝ) ^ i * v ^ (2 * i + 1) / (2 * i + 1)))
        (1 / (1 + u ^ 2) - (∑ i ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ i * u ^ (2 * i))) u :=
      (Real.hasDerivAt_arctan u).sub (hP u)
    rw [hd.deriv]
    have hb : (∑ i ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ i * u ^ (2 * i))
        = ∑ i ∈ Finset.range (2 * m + 2), ((-u ^ 2) : ℝ) ^ i := by
      apply Finset.sum_congr rfl
      intro i _
      conv_rhs => rw [neg_pow, ← pow_mul]
    have h1 : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
    have hS : (∑ i ∈ Finset.range (2 * m + 2), ((-u ^ 2) : ℝ) ^ i)
        = (1 - u ^ (4 * m + 4)) / (1 + u ^ 2) := by
      rw [eq_div_iff h1]
      exact hg u
    rw [hb, hS]
    field_simp
    ring
  have hdiff : ∀ x ∈ uIcc t (0 : ℝ), DifferentiableAt ℝ (fun u : ℝ => Real.arctan u -
      (∑ i ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ i * u ^ (2 * i + 1) / (2 * i + 1))) x := by
    intro x _
    exact ((Real.hasDerivAt_arctan x).sub (hP x)).differentiableAt
  have hcont : Continuous (fun u : ℝ => u ^ (4 * m + 4) / (1 + u ^ 2)) :=
    Continuous.div (by fun_prop) (by fun_prop)
      (fun u => ne_of_gt (by positivity : (0:ℝ) < 1 + u ^ 2))
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (fun u : ℝ => Real.arctan u - (∑ i ∈ Finset.range (2 * m + 2),
      (-1 : ℝ) ^ i * u ^ (2 * i + 1) / (2 * i + 1))) hF hdiff hcont.continuousOn
  have hzero : (Real.arctan 0 - (∑ i ∈ Finset.range (2 * m + 2),
      (-1 : ℝ) ^ i * (0 : ℝ) ^ (2 * i + 1) / (2 * i + 1))) = 0 := by
    have hsum : (∑ i ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ i * (0 : ℝ) ^ (2 * i + 1)
        / (2 * i + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [zero_pow (by omega : 2 * i + 1 ≠ 0)]
      ring
    rw [hsum]
    simp [Real.arctan_zero]
  have hnonneg : (0:ℝ) ≤ ∫ y in t..(0:ℝ), y ^ (4 * m + 4) / (1 + y ^ 2) :=
    intervalIntegral.integral_nonneg ht (fun y _ => by
      have h2 : y ^ (4 * m + 4) = (y ^ 2) ^ (2 * m + 2) := by
        rw [← pow_mul]
        congr 1
        ring
      rw [h2]
      positivity)
  have hftc' : ∫ y in t..(0:ℝ), y ^ (4 * m + 4) / (1 + y ^ 2)
      = -(Real.arctan t - (∑ i ∈ Finset.range (2 * m + 2), (-1 : ℝ) ^ i * t ^ (2 * i + 1)
        / (2 * i + 1))) := by
    simpa [hzero] using hftc
  linarith

/-- G3 certificate: degree-39 alternating upper bound (m = 9), explicit form for
the `bank_QITNPEA1_1_2` negative atan group G3 (bB+ and bB- alike: the bound is
uniform on `(-∞,0]`, no anchor hypothesis is needed). -/
theorem nliq12_g3_arctan_le_S39 (t : ℝ) (ht : t ≤ 0) :
    Real.arctan t ≤ t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 - t ^ 11 / 11
      + t ^ 13 / 13 - t ^ 15 / 15 + t ^ 17 / 17 - t ^ 19 / 19 + t ^ 21 / 21
      - t ^ 23 / 23 + t ^ 25 / 25 - t ^ 27 / 27 + t ^ 29 / 29 - t ^ 31 / 31
      + t ^ 33 / 33 - t ^ 35 / 35 + t ^ 37 / 37 - t ^ 39 / 39 := by
  have h := nliq12_arctan_le_alt_series_neg 9 t ht
  rw [show (t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 - t ^ 11 / 11
      + t ^ 13 / 13 - t ^ 15 / 15 + t ^ 17 / 17 - t ^ 19 / 19 + t ^ 21 / 21
      - t ^ 23 / 23 + t ^ 25 / 25 - t ^ 27 / 27 + t ^ 29 / 29 - t ^ 31 / 31
      + t ^ 33 / 33 - t ^ 35 / 35 + t ^ 37 / 37 - t ^ 39 / 39)
      = ∑ i ∈ Finset.range (2 * 9 + 2), (-1 : ℝ) ^ i * t ^ (2 * i + 1) / (2 * i + 1) by
    norm_num [Finset.sum_range_succ]
    ring]
  exact h

/-- Consumer shape for the assembly: on the rational t̂-enclosure bracket of
G3 (w2's 1e-6 rounded anchors, still to be certified by the interval enclosure
machinery), the arctan term is bounded by the explicit degree-39 polynomial. -/
theorem nliq12_g3_arctan_le_S39_of_mem (t : ℝ) (ht : (-811112 : ℝ) / 1000000 ≤ t ∧
    t ≤ (-613842 : ℝ) / 1000000) :
    Real.arctan t ≤ t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 - t ^ 11 / 11
      + t ^ 13 / 13 - t ^ 15 / 15 + t ^ 17 / 17 - t ^ 19 / 19 + t ^ 21 / 21
      - t ^ 23 / 23 + t ^ 25 / 25 - t ^ 27 / 27 + t ^ 29 / 29 - t ^ 31 / 31
      + t ^ 33 / 33 - t ^ 35 / 35 + t ^ 37 / 37 - t ^ 39 / 39 :=
  nliq12_g3_arctan_le_S39 t (by linarith [ht.1, ht.2])

/-- Consumption probe: exactly the way the QITNPEA1_1_2 assembly instantiates
the certificate once the t̂ enclosure `t̂ ∈ [A,B]` is available. -/
example (t : ℝ) (ht1 : (-811112 : ℝ) / 1000000 ≤ t) (ht2 : t ≤ (-613842 : ℝ) / 1000000) :
    Real.arctan t ≤ t - t ^ 3 / 3 + t ^ 5 / 5 - t ^ 7 / 7 + t ^ 9 / 9 - t ^ 11 / 11
      + t ^ 13 / 13 - t ^ 15 / 15 + t ^ 17 / 17 - t ^ 19 / 19 + t ^ 21 / 21
      - t ^ 23 / 23 + t ^ 25 / 25 - t ^ 27 / 27 + t ^ 29 / 29 - t ^ 31 / 31
      + t ^ 33 / 33 - t ^ 35 / 35 + t ^ 37 / 37 - t ^ 39 / 39 :=
  nliq12_g3_arctan_le_S39_of_mem t ⟨ht1, ht2⟩

#print axioms nliq12_arctan_le_alt_series_neg
#print axioms nliq12_g3_arctan_le_S39
#print axioms nliq12_g3_arctan_le_S39_of_mem

end Kepler.Text
