/-
Kepler.Text.Gamma4ValArctan — lane `gamma4-val1e6`, V4.

`arctan` / `atn2` two-sided bounds at the finite parameter set actually
consumed by the B2 bank corners (and at the classical points the work order
lists).  The generic engine is Mathlib/`Kepler.Interval.Trans`'s verified
alternating Taylor remainder `arctan_abs_sub_partial_le` (order 32, tail
`≤ 1e-11`); every concrete instance closes with `norm_num`.

Parameter set found by grepping the B2 refined-corner table (the exact
corners of the 14 narrow gamma4 banks, `y_i ∈ {2, 2h0, 2hplus, √8}`):
* `(2hplus, 2,2,2,2,2)`: `atn2` arguments `-0.109105851…`, `-0.594328302…`
  (four times), `+0.173685369…` — the three values below (`A1`,`A2`,`A3`);
* `(√8, 2,2,2,2,2)`: `0`, `±1/√2`, `1/(2√2)` — the exact values below.
The full 14-bank exact-corner alphabet has 52 distinct algebraic arguments
(enumerated in `Evidence.md`); the generic ratio lemma here instantiates any
of them mechanically.
-/
import Kepler.Text.Gamma4Val

set_option maxHeartbeats 4000000

namespace Kepler.Text

/-! ## The generic rational Taylor bracket -/

/-- `arctan x` on `0 ≤ x < 1` from the order-32 alternating Taylor partial
sum: if the sum lies in `[lo + 1e-11, hi - 1e-11]` and the tail is
`≤ 1e-11`, then `arctan x ∈ [lo, hi]`. -/
theorem g4v_atan_pos_bounds {x lo hi : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hSlo : lo + 1 / 100000000000 ≤
      ∑ i ∈ Finset.range 32, ((-1:ℝ)^i * x^(2*i+1))/((2*i+1 : ℕ):ℝ))
    (hShi : (∑ i ∈ Finset.range 32, ((-1:ℝ)^i * x^(2*i+1))/((2*i+1 : ℕ):ℝ)) ≤
      hi - 1 / 100000000000)
    (hrem : x^(2*32+1)/((2*32+1 : ℕ):ℝ) ≤ 1 / 100000000000) :
    lo ≤ Real.arctan x ∧ Real.arctan x ≤ hi := by
  have h := Kepler.Interval.arctan_abs_sub_partial_le hx0 hx1 32
  have hr := le_trans h hrem
  have hb := abs_le.mp hr
  constructor <;> linarith [hb.1, hb.2]

/-- Odd mirror of `g4v_atan_pos_bounds`. -/
theorem g4v_atan_neg_bounds {x lo hi : ℝ}
    (h : lo ≤ Real.arctan x ∧ Real.arctan x ≤ hi) :
    -hi ≤ Real.arctan (-x) ∧ Real.arctan (-x) ≤ -lo := by
  rw [Real.arctan_neg]
  constructor
  · exact neg_le_neg_iff.mpr h.2
  · exact neg_le_neg_iff.mpr h.1

/-! ## Exact special values -/

theorem g4v_atan_zero : Real.arctan 0 = 0 := Real.arctan_zero

theorem g4v_atan_one : Real.arctan 1 = Real.pi / 4 := Real.arctan_one

/-- `arctan(1/√2) = arccos(1/3)/2` (V3 bridge). -/
theorem g4v_atan_inv_sqrt2 :
    Real.arctan (1 / Real.sqrt 2) = Real.arccos (1 / 3) / 2 := by
  have h := g4v_arccos_eq_two_arctan
  linarith

/-- `arctan(1/(2√2)) = arcsin(1/3)` (PA38 kernel re-derived locally). -/
theorem g4v_atan_inv_two_sqrt2 :
    Real.arctan (1 / (2 * Real.sqrt 2)) = Real.arcsin (1 / 3) := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : Real.sin (Real.arctan (1 / (2 * Real.sqrt 2))) = 1 / 3 := by
    rw [Real.sin_arctan]
    have hden : (1 : ℝ) + (1 / (2 * Real.sqrt 2)) ^ 2 = 9 / 8 := by
      have e1 : (1 / (2 * Real.sqrt 2)) ^ 2 = 1 / (2 * Real.sqrt 2) ^ 2 := by
        rw [one_div_pow]
      have e2 : (2 * Real.sqrt 2) ^ 2 = 8 := by rw [mul_pow, hsq2]; norm_num
      rw [e1, e2]
      norm_num
    have hr8 : Real.sqrt (9 / 8) = 3 / (2 * Real.sqrt 2) := by
      have hval : (9 / 8 : ℝ) = (3 / (2 * Real.sqrt 2)) ^ 2 := by
        rw [div_pow, mul_pow, hsq2]
        norm_num
      rw [hval, Real.sqrt_sq (by positivity)]
    rw [hden, hr8]
    field_simp
  rw [← hs]
  obtain ⟨hm1, hm2⟩ := Real.arctan_mem_Ioo (1 / (2 * Real.sqrt 2))
  exact (Real.arcsin_sin' ⟨le_of_lt hm1, le_of_lt hm2⟩).symm

/-! ## Numeric bounds at the classical points -/

theorem g4v_atan_inv_sqrt2_bounds :
    (0.6154797083 : ℝ) ≤ Real.arctan (1 / Real.sqrt 2) ∧
      Real.arctan (1 / Real.sqrt 2) ≤ 0.6154797090 := by
  obtain ⟨ha1, ha2⟩ := g4v_arccos_third_bounds
  have heq := g4v_atan_inv_sqrt2
  constructor <;> rw [heq] <;> linarith

theorem g4v_atan_neg_inv_sqrt2_bounds :
    (-0.6154797090 : ℝ) ≤ Real.arctan (-(1 / Real.sqrt 2)) ∧
      Real.arctan (-(1 / Real.sqrt 2)) ≤ -0.6154797083 := by
  have h := g4v_atan_inv_sqrt2_bounds
  have := g4v_atan_neg_bounds h
  simpa using this

theorem g4v_atan_inv_two_sqrt2_bounds :
    (0.339836909 : ℝ) ≤ Real.arctan (1 / (2 * Real.sqrt 2)) ∧
      Real.arctan (1 / (2 * Real.sqrt 2)) ≤ 0.339836910 := by
  have heq := g4v_atan_inv_two_sqrt2
  obtain ⟨ha1, ha2⟩ := g4v_arcsin_third_bounds
  constructor <;> rw [heq] <;> linarith

theorem g4v_atan_neg_inv_two_sqrt2_bounds :
    (-0.339836910 : ℝ) ≤ Real.arctan (-(1 / (2 * Real.sqrt 2))) ∧
      Real.arctan (-(1 / (2 * Real.sqrt 2))) ≤ -0.339836909 := by
  have h := g4v_atan_inv_two_sqrt2_bounds
  have := g4v_atan_neg_bounds h
  simpa using this

/-- `arctan(1/3) ∈ [0.321750554, 0.321750555]` (width `1e-9`). -/
theorem g4v_atan_third_bounds :
    (0.321750554 : ℝ) ≤ Real.arctan (1 / 3) ∧
      Real.arctan (1 / 3) ≤ 0.321750555 := by
  have h := g4v_atan_pos_bounds (x := (1 / 3 : ℝ)) (lo := 0.321750554)
    (hi := 0.321750555) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact h

/-- `arctan 3 = π/2 − arctan(1/3) ∈ [1.2490457717, 1.2490457728]`. -/
theorem g4v_atan_three_bounds :
    (1.2490457717 : ℝ) ≤ Real.arctan 3 ∧ Real.arctan 3 ≤ 1.2490457728 := by
  obtain ⟨h1, h2⟩ := g4v_atan_third_bounds
  obtain ⟨hp1, hp2⟩ := g4v_pi_bounds
  have hinv : Real.arctan (3⁻¹) = Real.pi / 2 - Real.arctan 3 :=
    Real.arctan_inv_of_pos (by norm_num)
  have h3 : Real.arctan 3 = Real.pi / 2 - Real.arctan (3⁻¹) := by linarith
  have h13 : (3⁻¹ : ℝ) = 1 / 3 := by norm_num
  constructor <;> rw [h3, h13] <;> linarith

/-! ## Ratio lemmas for `t / √d` -/

/-- For `t < 0` and `0 < dlo ≤ √d ≤ dhi`: `t/√d ∈ [t/dhi, t/dlo]`. -/
theorem g4v_div_sqrt_neg_mem {t d dlo dhi : ℝ} (hdlo : 0 < dlo)
    (hslo : dlo ≤ Real.sqrt d) (hshi : Real.sqrt d ≤ dhi) (ht : t < 0) :
    t / dlo ≤ t / Real.sqrt d ∧ t / Real.sqrt d ≤ t / dhi := by
  have hsqrtpos : 0 < Real.sqrt d := lt_of_lt_of_le hdlo hslo
  have hdhipos : 0 < dhi := lt_of_lt_of_le hsqrtpos hshi
  constructor
  · have hden : 0 < dlo * Real.sqrt d := mul_pos hdlo hsqrtpos
    have hnum : t * (Real.sqrt d - dlo) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt ht) (by linarith)
    have heq : t / dlo - t / Real.sqrt d = t * (Real.sqrt d - dlo) / (dlo * Real.sqrt d) := by
      field_simp
    have hdiff : t / dlo - t / Real.sqrt d ≤ 0 := by
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)
    exact sub_nonpos.mp hdiff
  · have hden : 0 < Real.sqrt d * dhi := mul_pos hsqrtpos hdhipos
    have hnum : t * (dhi - Real.sqrt d) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_lt ht) (by linarith)
    have heq : t / Real.sqrt d - t / dhi = t * (dhi - Real.sqrt d) / (Real.sqrt d * dhi) := by
      field_simp
    have hdiff : t / Real.sqrt d - t / dhi ≤ 0 := by
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg hnum (le_of_lt hden)
    exact sub_nonpos.mp hdiff

/-- Wrapper: `t/√d` bounds from the `[t/dhi, t/dlo]` bracket and `arctan`
bounds at the rational endpoints, for `t < 0`. -/
theorem g4v_atan_ratio_neg_bounds {t d dlo dhi ulo uhi lo hi : ℝ}
    (hdlo : 0 < dlo) (hslo : dlo ≤ Real.sqrt d) (hshi : Real.sqrt d ≤ dhi)
    (ht : t < 0) (hu1 : ulo ≤ t / dlo) (hu2 : t / dhi ≤ uhi)
    (ha1 : lo ≤ Real.arctan ulo) (ha2 : Real.arctan uhi ≤ hi) :
    lo ≤ Real.arctan (t / Real.sqrt d) ∧ Real.arctan (t / Real.sqrt d) ≤ hi := by
  obtain ⟨hm1, hm2⟩ := g4v_div_sqrt_neg_mem hdlo hslo hshi ht
  constructor
  · exact le_trans ha1 (Real.arctan_mono (le_trans hu1 hm1))
  · exact le_trans (Real.arctan_mono (le_trans hm2 hu2)) ha2

/-- For `t > 0` and `0 < dlo ≤ √d ≤ dhi`: `t/√d ∈ [t/dhi, t/dlo]`. -/
theorem g4v_div_sqrt_pos_mem {t d dlo dhi : ℝ} (hdlo : 0 < dlo)
    (hslo : dlo ≤ Real.sqrt d) (hshi : Real.sqrt d ≤ dhi) (ht : 0 < t) :
    t / dhi ≤ t / Real.sqrt d ∧ t / Real.sqrt d ≤ t / dlo := by
  have hsqrtpos : 0 < Real.sqrt d := lt_of_lt_of_le hdlo hslo
  have hdhipos : 0 < dhi := lt_of_lt_of_le hsqrtpos hshi
  constructor
  · have hden : 0 < Real.sqrt d * dhi := mul_pos hsqrtpos hdhipos
    have hnum : 0 ≤ t * (dhi - Real.sqrt d) :=
      mul_nonneg (le_of_lt ht) (by linarith)
    have heq : t / dhi - t / Real.sqrt d = t * (Real.sqrt d - dhi) / (dhi * Real.sqrt d) := by
      field_simp
    have hdiff : t / dhi - t / Real.sqrt d ≤ 0 := by
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hnum]) (le_of_lt (mul_pos hdhipos hsqrtpos))
    exact sub_nonpos.mp hdiff
  · have hden : 0 < dlo * Real.sqrt d := mul_pos hdlo hsqrtpos
    have hnum : 0 ≤ t * (Real.sqrt d - dlo) :=
      mul_nonneg (le_of_lt ht) (by linarith)
    have heq : t / Real.sqrt d - t / dlo = t * (dlo - Real.sqrt d) / (Real.sqrt d * dlo) := by
      field_simp
    have hdiff : t / Real.sqrt d - t / dlo ≤ 0 := by
      rw [heq]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hnum]) (le_of_lt (mul_pos hsqrtpos hdlo))
    exact sub_nonpos.mp hdiff

/-- Wrapper for `t > 0`. -/
theorem g4v_atan_ratio_pos_bounds {t d dlo dhi ulo uhi lo hi : ℝ}
    (hdlo : 0 < dlo) (hslo : dlo ≤ Real.sqrt d) (hshi : Real.sqrt d ≤ dhi)
    (ht : 0 < t) (hu1 : ulo ≤ t / dhi) (hu2 : t / dlo ≤ uhi)
    (ha1 : lo ≤ Real.arctan ulo) (ha2 : Real.arctan uhi ≤ hi) :
    lo ≤ Real.arctan (t / Real.sqrt d) ∧ Real.arctan (t / Real.sqrt d) ≤ hi := by
  obtain ⟨hm1, hm2⟩ := g4v_div_sqrt_pos_mem hdlo hslo hshi ht
  constructor
  · exact le_trans ha1 (Real.arctan_mono (le_trans hu1 hm1))
  · exact le_trans (Real.arctan_mono (le_trans hm2 hu2)) ha2

/-! ## The three real `(2hplus, 2⁵)` corner arguments -/

/-- `arctan` of the three algebraic arguments at `(2hplus, 2,2,2,2,2)`.
`A1 = -0.109105851…` (slot 1), `A2 = -0.594328302…` (slots 2,3,5,6),
`A3 = +0.173685369…` (slot 4).  The rational brackets are 8-decimal
enclosures; the sqrt brackets are 7-decimal (`62.6807911/2`,
`47.2919806/7`), and the `arctan` brackets have width `1e-8`. -/

theorem g4v_atan_A1_bounds :
    (-0.108675992 : ℝ) ≤ Real.arctan
        ((-(267142230397359 / 39062500000000)) /
          Real.sqrt (59949975283774561462311 / 15258789062500000000)) ∧
      Real.arctan ((-(267142230397359 / 39062500000000)) /
          Real.sqrt (59949975283774561462311 / 15258789062500000000)) ≤ -0.108675980 := by
  have hp1 : (0.108675980 : ℝ) ≤ Real.arctan 0.10910586 ∧
      Real.arctan 0.10910586 ≤ 0.108675992 := by
    exact g4v_atan_pos_bounds (x := 0.10910586) (lo := 0.108675980)
      (hi := 0.108675992) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hp2 : (0.108675980 : ℝ) ≤ Real.arctan 0.10910585 ∧
      Real.arctan 0.10910585 ≤ 0.108675992 := by
    exact g4v_atan_pos_bounds (x := 0.10910585) (lo := 0.108675980)
      (hi := 0.108675992) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hn1 : (-0.108675992 : ℝ) ≤ Real.arctan (-0.10910586) := by
    rw [Real.arctan_neg]
    exact neg_le_neg_iff.mpr hp1.2
  have hn2 : Real.arctan (-0.10910585) ≤ -0.108675980 := by
    rw [Real.arctan_neg]
    exact neg_le_neg_iff.mpr hp2.1
  have hs1 : (62.6807911 : ℝ) ≤
      Real.sqrt (59949975283774561462311 / 15258789062500000000) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : Real.sqrt (59949975283774561462311 / 15258789062500000000) ≤
      62.6807912 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have h := g4v_atan_ratio_neg_bounds
    (t := (-(267142230397359 / 39062500000000)))
    (d := (59949975283774561462311 / 15258789062500000000))
    (dlo := 62.6807911) (dhi := 62.6807912)
    (ulo := -0.10910586) (uhi := -0.10910585)
    (lo := -0.108675992) (hi := -0.108675980)
    (by norm_num) hs1 hs2 (by norm_num) (by norm_num) (by norm_num) hn1 hn2
  exact h

theorem g4v_atan_A2_bounds :
    (-0.536238704 : ℝ) ≤ Real.arctan
        ((-(43917129 / 1562500)) /
          Real.sqrt (1365070455397359 / 610351562500)) ∧
      Real.arctan ((-(43917129 / 1562500)) /
          Real.sqrt (1365070455397359 / 610351562500)) ≤ -0.536238695 := by
  have hp1 : (0.536238695 : ℝ) ≤ Real.arctan 0.59432831 ∧
      Real.arctan 0.59432831 ≤ 0.536238704 := by
    exact g4v_atan_pos_bounds (x := 0.59432831) (lo := 0.536238695)
      (hi := 0.536238704) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hp2 : (0.536238695 : ℝ) ≤ Real.arctan 0.59432830 ∧
      Real.arctan 0.59432830 ≤ 0.536238704 := by
    exact g4v_atan_pos_bounds (x := 0.59432830) (lo := 0.536238695)
      (hi := 0.536238704) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hn1 : (-0.536238704 : ℝ) ≤ Real.arctan (-0.59432831) := by
    rw [Real.arctan_neg]
    exact neg_le_neg_iff.mpr hp1.2
  have hn2 : Real.arctan (-0.59432830) ≤ -0.536238695 := by
    rw [Real.arctan_neg]
    exact neg_le_neg_iff.mpr hp2.1
  have hs1 : (47.2919806 : ℝ) ≤
      Real.sqrt (1365070455397359 / 610351562500) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : Real.sqrt (1365070455397359 / 610351562500) ≤ 47.2919807 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have h := g4v_atan_ratio_neg_bounds
    (t := (-(43917129 / 1562500)))
    (d := (1365070455397359 / 610351562500))
    (dlo := 47.2919806) (dhi := 47.2919807)
    (ulo := -0.59432831) (uhi := -0.59432830)
    (lo := -0.536238704) (hi := -0.536238695)
    (by norm_num) hs1 hs2 (by norm_num) (by norm_num) (by norm_num) hn1 hn2
  exact h

theorem g4v_atan_A3_bounds :
    (0.171969806 : ℝ) ≤ Real.arctan
        ((6417129 / 781250) /
          Real.sqrt (1365070455397359 / 610351562500)) ∧
      Real.arctan ((6417129 / 781250) /
          Real.sqrt (1365070455397359 / 610351562500)) ≤ 0.171969817 := by
  have hp1 : (0.171969806 : ℝ) ≤ Real.arctan 0.17368536 ∧
      Real.arctan 0.17368536 ≤ 0.171969817 := by
    exact g4v_atan_pos_bounds (x := 0.17368536) (lo := 0.171969806)
      (hi := 0.171969817) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hp2 : (0.171969806 : ℝ) ≤ Real.arctan 0.17368537 ∧
      Real.arctan 0.17368537 ≤ 0.171969817 := by
    exact g4v_atan_pos_bounds (x := 0.17368537) (lo := 0.171969806)
      (hi := 0.171969817) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hs1 : (47.2919806 : ℝ) ≤
      Real.sqrt (1365070455397359 / 610351562500) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : Real.sqrt (1365070455397359 / 610351562500) ≤ 47.2919807 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have h := g4v_atan_ratio_pos_bounds
    (t := (6417129 / 781250))
    (d := (1365070455397359 / 610351562500))
    (dlo := 47.2919806) (dhi := 47.2919807)
    (ulo := 0.17368536) (uhi := 0.17368537)
    (lo := 0.171969806) (hi := 0.171969817)
    (by norm_num) hs1 hs2 (by norm_num) (by norm_num) (by norm_num) hp1.1 hp2.2
  exact h

/-! ## Axiom audit -/

#print axioms g4v_atan_pos_bounds
#print axioms g4v_atan_neg_bounds
#print axioms g4v_atan_inv_sqrt2
#print axioms g4v_atan_inv_two_sqrt2
#print axioms g4v_atan_inv_sqrt2_bounds
#print axioms g4v_atan_neg_inv_sqrt2_bounds
#print axioms g4v_atan_inv_two_sqrt2_bounds
#print axioms g4v_atan_neg_inv_two_sqrt2_bounds
#print axioms g4v_atan_third_bounds
#print axioms g4v_atan_three_bounds
#print axioms g4v_div_sqrt_neg_mem
#print axioms g4v_atan_ratio_neg_bounds
#print axioms g4v_div_sqrt_pos_mem
#print axioms g4v_atan_ratio_pos_bounds
#print axioms g4v_atan_A1_bounds
#print axioms g4v_atan_A2_bounds
#print axioms g4v_atan_A3_bounds

end Kepler.Text
