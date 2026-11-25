/-
Kepler.Text.TaylorSecond.LeafKitPrec — lane `wt1-matan-precision-w1` (2026-11-25).

Tight value brackets for `matan` on the positive branch (the wt1 `w1aF` **value**
channel).  The landed `lk_matan_direct` / `lk_matan_u` use the order-5/7 pair
(`lkA5` / `lkA7`), whose point enclosure is `r³/7` wide — `1.79e-2` at `r = 0.5`
(≈2 %) — and that width dominates the value channel of the thin `15869`/`15874`
boxes.  This file supplies the order-9/11 pair instead, of exact width `r⁵/11`
(`6.3×` tighter at `r = 0.5`, `25×` at `r = 1/4`), plus the mirror identity that
routes `r > 1` back to `1/r`, so the tight series is always evaluated at
argument `≤ 1`.

Content.
* §0 the order-9 truncation `lkA9` (upper) and the order-11 truncation `lkB11`
  (lower), with derivative certificates (`s^10/(1+s^2) ≥ 0`, `s^12/(1+s^2) ≥ 0`),
  the two global bounds via `nb12_nonneg_of_deriv`, and monotonicity on `[0, 1]`.
* §1 `lk_matan_direct9`: direct-form point enclosure with the a9/b11 pair,
  valid for every `r > 0` (tightness at `r ≤ 1/4` is the caller's business).
* §2 `lk_matan_mirror`: `matan r = π/(2√r) − matan (1/r)/r`, so `r > 1` reduces
  to the direct form at `1/r < 1`.
* §3 `lk_matan_u9`: u-form point enclosure (the `lk_matan_u` shape) with a9/b11.

New file only; nothing already landed is modified.  No `axiom` / `sorry` /
`admit` / `native_decide`; standard three axioms, audited at the tail.
-/
import Kepler.Text.TaylorSecond.LeafKit

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

/-! ## 0. The order-9 / order-11 truncations -/

/-- The order-9 truncation `s − s³/3 + s⁵/5 − s⁷/7 + s⁹/9`. -/
noncomputable def lkA9 (s : ℝ) : ℝ := s - s ^ 3 / 3 + s ^ 5 / 5 - s ^ 7 / 7 + s ^ 9 / 9

/-- The order-11 truncation `lkA9 s − s¹¹/11`. -/
noncomputable def lkB11 (s : ℝ) : ℝ := lkA9 s - s ^ 11 / 11

theorem lk_hasDerivAt_a9 (x : ℝ) :
    HasDerivAt lkA9 (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8) x := by
  have h9 : HasDerivAt (fun x : ℝ => x ^ 9 / 9) (x ^ 8) x := by
    have := (hasDerivAt_pow 9 x).div_const 9
    simpa [pow_succ] using this
  have h := (lk_hasDerivAt_a7 x).add h9
  rw [show lkA9 = fun x : ℝ => lkA7 x + x ^ 9 / 9 from rfl]
  exact h

theorem lk_deriv_a9 (x : ℝ) : deriv lkA9 x = 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 :=
  (lk_hasDerivAt_a9 x).deriv

theorem lk_hasDerivAt_b11 (x : ℝ) :
    HasDerivAt lkB11 (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10) x := by
  have h11 : HasDerivAt (fun x : ℝ => x ^ 11 / 11) (x ^ 10) x := by
    have := (hasDerivAt_pow 11 x).div_const 11
    simpa [pow_succ] using this
  have h := (lk_hasDerivAt_a9 x).sub h11
  rw [show lkB11 = fun x : ℝ => lkA9 x - x ^ 11 / 11 from rfl]
  exact h

theorem lk_deriv_b11 (x : ℝ) :
    deriv lkB11 x = 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 :=
  (lk_hasDerivAt_b11 x).deriv

theorem lk_continuous_a9 : Continuous lkA9 :=
  continuous_iff_continuousAt.mpr (fun x => (lk_hasDerivAt_a9 x).continuousAt)

theorem lk_continuous_b11 : Continuous lkB11 :=
  continuous_iff_continuousAt.mpr (fun x => (lk_hasDerivAt_b11 x).continuousAt)

/-- **`arctan` to ninth order**: `arctan s ≤ lkA9 s` for `s ≥ 0`
(the derivative of the difference is `s¹⁰/(1+s²) ≥ 0`). -/
theorem lk_atan_le_a9 {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ lkA9 s := by
  have h := Kepler.NliBanks12.nb12_nonneg_of_deriv
    (f := fun x : ℝ => lkA9 x - Real.arctan x)
    (hC := lk_continuous_a9.sub Real.continuous_arctan)
    (hD := fun x => (lk_hasDerivAt_a9 x).differentiableAt.sub
      Real.differentiable_arctan.differentiableAt)
    (h0 := by simp [lkA9])
    (hd := by
      intro x _
      have hderiv : HasDerivAt (fun y : ℝ => lkA9 y - Real.arctan y)
          (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - 1 / (1 + x ^ 2)) x :=
        (lk_hasDerivAt_a9 x).sub (Real.hasDerivAt_arctan x)
      rw [hderiv.deriv]
      have hfrac : 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - 1 / (1 + x ^ 2)
          = x ^ 10 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [hfrac]
      positivity) s hs
  linarith

/-- **`arctan` to eleventh order**: `lkB11 s ≤ arctan s` for `s ≥ 0`
(the derivative of `arctan − lkB11` is `s¹²/(1+s²) ≥ 0`). -/
theorem lk_atan_ge_b11 {s : ℝ} (hs : 0 ≤ s) : lkB11 s ≤ Real.arctan s := by
  have h := Kepler.NliBanks12.nb12_nonneg_of_deriv
    (f := fun x : ℝ => Real.arctan x - lkB11 x)
    (hC := Real.continuous_arctan.sub lk_continuous_b11)
    (hD := fun x => Real.differentiable_arctan.differentiableAt.sub
      (lk_hasDerivAt_b11 x).differentiableAt)
    (h0 := by simp [lkB11, lkA9])
    (hd := by
      intro x _
      have hderiv : HasDerivAt (fun y : ℝ => Real.arctan y - lkB11 y)
          (1 / (1 + x ^ 2) - (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10)) x :=
        (Real.hasDerivAt_arctan x).sub (lk_hasDerivAt_b11 x)
      rw [hderiv.deriv]
      have hfrac : 1 / (1 + x ^ 2) - (1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10)
          = x ^ 12 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [hfrac]
      positivity) s hs
  linarith


/-- `lkA9 0 = 0`. -/
theorem lk_a9_zero : lkA9 0 = 0 := by simp [lkA9]

/-- `lkB11 0 = 0`. -/
theorem lk_b11_zero : lkB11 0 = 0 := by simp [lkB11, lkA9]

/-- `lkA9` is increasing on `[0, 1]` (derivative `(1−x²)(1+x⁴) + x⁸ ≥ 0`). -/
theorem lk_a9_mono {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) : lkA9 a ≤ lkA9 b := by
  have hsign : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (0 : ℝ) ≤ 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 := by
    intro x hx0 hx1
    have hle : x ^ 2 ≤ 1 := by nlinarith
    have hexp : 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 = (1 - x ^ 2) * (1 + x ^ 4) + x ^ 8 := by
      ring
    rw [hexp]
    exact add_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)
  have hdiff : Differentiable ℝ lkA9 := fun x => (lk_hasDerivAt_a9 x).differentiableAt
  have hcont : ContinuousOn lkA9 (Set.Icc a b) := hdiff.continuous.continuousOn
  have hdif : DifferentiableOn ℝ lkA9 (interior (Set.Icc a b)) := fun x _ =>
    (lk_hasDerivAt_a9 x).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn lkA9 (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdif (by
      intro x hx
      rw [interior_Icc] at hx
      rw [lk_deriv_a9]
      exact hsign x (le_trans ha0 hx.1.le) (le_trans hx.2.le hb1))
  exact hmono (Set.mem_Icc.mpr ⟨le_refl _, hab⟩) (Set.mem_Icc.mpr ⟨hab, le_refl _⟩) hab

/-- `lkB11` is increasing on `[0, 1]` (derivative `(1−x²)(1+x⁴+x⁸) ≥ 0`). -/
theorem lk_b11_mono {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    lkB11 a ≤ lkB11 b := by
  have hsign : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      (0 : ℝ) ≤ 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10 := by
    intro x hx0 hx1
    have hle : x ^ 2 ≤ 1 := by nlinarith
    have hexp : 1 - x ^ 2 + x ^ 4 - x ^ 6 + x ^ 8 - x ^ 10
        = (1 - x ^ 2) * (1 + x ^ 4 + x ^ 8) := by
      ring
    rw [hexp]
    exact mul_nonneg (by linarith) (by positivity)
  have hdiff : Differentiable ℝ lkB11 := fun x => (lk_hasDerivAt_b11 x).differentiableAt
  have hcont : ContinuousOn lkB11 (Set.Icc a b) := hdiff.continuous.continuousOn
  have hdif : DifferentiableOn ℝ lkB11 (interior (Set.Icc a b)) := fun x _ =>
    (lk_hasDerivAt_b11 x).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn lkB11 (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdif (by
      intro x hx
      rw [interior_Icc] at hx
      rw [lk_deriv_b11]
      exact hsign x (le_trans ha0 hx.1.le) (le_trans hx.2.le hb1))
  exact hmono (Set.mem_Icc.mpr ⟨le_refl _, hab⟩) (Set.mem_Icc.mpr ⟨hab, le_refl _⟩) hab


/-! ## 1. Tight direct-form point enclosure -/

/-- Direct-form point enclosure with the order-9/11 pair: for `r > 0`,
`matan r ∈ [1 − r/3 + r²/5 − r³/7 + r⁴/9 − r⁵/11,
            1 − r/3 + r²/5 − r³/7 + r⁴/9]`.

The bracket holds for every `r > 0`.  Its exact width is `r⁵/11` — in the
`s = √r` variable the series remainder is `s¹⁰/11` — so on the direct branch
`r ≤ 1/4` it is `≤ 8.9e-5` (the landed a5/a7 pair gives `2.23e-3` there, and
`1.95e-2` at `r ≈ 0.5`; see `lk_matan_mirror` for routing `r > 1` into this). -/
theorem lk_matan_direct9 (V : QInterval) (tI : ℚ) (ht : (0:ℚ) < tI)
    (hV : V = QInterval.mk
      (1 - tI / 3 + tI ^ 2 / 5 - tI ^ 3 / 7 + tI ^ 4 / 9 - tI ^ 5 / 11)
      (1 - tI / 3 + tI ^ 2 / 5 - tI ^ 3 / 7 + tI ^ 4 / 9)) :
    V.mem (matan ((tI : ℚ) : ℝ)) := by
  rw [hV, QInterval.mem]
  simp only [QInterval.lo, QInterval.hi, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_one, Rat.cast_mul, Rat.cast_pow]
  have hr : (0:ℝ) < ((tI : ℚ) : ℝ) := by exact_mod_cast ht
  have hsq : Real.sqrt ((tI : ℚ) : ℝ) ^ 2 = ((tI : ℚ) : ℝ) := Real.sq_sqrt hr.le
  have hme := lk_matan_eq hr
  have s0 : (0:ℝ) ≤ Real.sqrt ((tI : ℚ) : ℝ) := Real.sqrt_nonneg _
  have hlo := lk_atan_ge_b11 s0
  have hhi := lk_atan_le_a9 s0
  simp only [lkA9, lkB11] at hlo hhi
  rw [show (3:ℕ) = 2 * 1 + 1 by norm_num, lk_sqrt_pow hsq,
      show (5:ℕ) = 2 * 2 + 1 by norm_num, lk_sqrt_pow hsq,
      show (7:ℕ) = 2 * 3 + 1 by norm_num, lk_sqrt_pow hsq,
      show (9:ℕ) = 2 * 4 + 1 by norm_num, lk_sqrt_pow hsq,
      show (11:ℕ) = 2 * 5 + 1 by norm_num, lk_sqrt_pow hsq] at hlo
  rw [show (3:ℕ) = 2 * 1 + 1 by norm_num, lk_sqrt_pow hsq,
      show (5:ℕ) = 2 * 2 + 1 by norm_num, lk_sqrt_pow hsq,
      show (7:ℕ) = 2 * 3 + 1 by norm_num, lk_sqrt_pow hsq,
      show (9:ℕ) = 2 * 4 + 1 by norm_num, lk_sqrt_pow hsq] at hhi
  simp only [pow_one] at hlo hhi
  simp only [hme, le_div_iff₀ (Real.sqrt_pos.mpr hr), div_le_iff₀ (Real.sqrt_pos.mpr hr)]
  push_cast
  constructor
  · nlinarith [hlo, hr.le]
  · nlinarith [hhi, hr.le]


/-! ## 2. The mirror identity -/

/-- Pure algebra behind the mirror identity: with `r = s²`,
`(p/2 − a)/s = p/(2s) − a/(1/s)/r`. -/
theorem lk_mirror_alg {p a s r : ℝ} (hs : s ≠ 0) (hr : r ≠ 0) (hsq : r = s * s) :
    (p / 2 - a) / s = p / (2 * s) - a / (1 / s) / r := by
  rw [hsq]
  field_simp

/-- **Mirror identity**: for `0 < r`,
`matan r = π/(2√r) − matan (1/r)/r`.
Comes from `arctan s = π/2 − arctan (1/s)` at `s = √r` and `√(1/r) = 1/√r`. -/
theorem lk_matan_mirror {r : ℝ} (hr : 0 < r) :
    matan r = Real.pi / (2 * Real.sqrt r) - matan (1 / r) / r := by
  have hr1 : (0:ℝ) < 1 / r := by positivity
  have hsp : (0:ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsqi : Real.sqrt (1 / r) = 1 / Real.sqrt r := by
    rw [one_div, Real.sqrt_inv, one_div]
  have h1 := lk_matan_eq hr
  have h2 := lk_matan_eq hr1
  have hinv := lk_arctan_inv hsp
  have hsq : r = Real.sqrt r * Real.sqrt r := by
    rw [show Real.sqrt r * Real.sqrt r = Real.sqrt r ^ 2 by ring]
    exact (Real.sq_sqrt hr.le).symm
  have hs0 : Real.sqrt r ≠ 0 := ne_of_gt hsp
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [h1, h2, hsqi, hinv]
  exact lk_mirror_alg (p := Real.pi) (a := Real.arctan (1 / Real.sqrt r))
    (s := Real.sqrt r) (r := r) hs0 hr0 hsq


/-! ## 3. u-form point enclosure at order 9/11 -/

/-- u-form point enclosure at order 9/11 for `1 < r` with rational sqrt brackets
`ql² ≤ r ≤ qh²`, `1 ≤ ql ≤ qh`: matan r is enclosed by
`(πlo/2 − a9(1/ql))/qh .. (πhi/2 − b11(1/qh))/ql`.
(`lk_matan_u` is the a5/a7 version; here the *upper* truncation `a9` bounds
`arctan (1/s)` from above at the small end `1/ql`, and the *lower* truncation
`b11` bounds it from below at `1/qh` — so both series arguments are `≤ 1`.) -/
theorem lk_matan_u9 (V : QInterval) (tI ql qh : ℚ) (ht : (1:ℚ) < tI)
    (hql2 : ((ql : ℚ) : ℝ) ^ 2 ≤ ((tI : ℚ) : ℝ))
    (hqh2 : ((tI : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) ^ 2)
    (hq0 : (0:ℚ) < ql) (hq1 : ql ≤ qh) (hq2 : (1:ℚ) ≤ qh) (hq3 : (1:ℚ) ≤ ql)
    (hV : V = QInterval.mk
      ((lkPIlo / 2 - (1 / ql - (1 / ql) ^ 3 / 3 + (1 / ql) ^ 5 / 5
        - (1 / ql) ^ 7 / 7 + (1 / ql) ^ 9 / 9)) / qh)
      ((lkPIhi / 2 - (1 / qh - (1 / qh) ^ 3 / 3 + (1 / qh) ^ 5 / 5
        - (1 / qh) ^ 7 / 7 + (1 / qh) ^ 9 / 9 - (1 / qh) ^ 11 / 11)) / ql)) :
    V.mem (matan ((tI : ℚ) : ℝ)) := by
  have hLoB : ((((lkPIlo / 2 - (1 / ql - (1 / ql) ^ 3 / 3 + (1 / ql) ^ 5 / 5
      - (1 / ql) ^ 7 / 7 + (1 / ql) ^ 9 / 9)) / qh : ℚ) : ℝ))
      = ((lkPIlo : ℝ) / 2 - lkA9 (1 / ((ql : ℚ) : ℝ))) / ((qh : ℚ) : ℝ) := by
    simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_pow]
    unfold lkA9
    ring
  have hHiB : ((((lkPIhi / 2 - (1 / qh - (1 / qh) ^ 3 / 3 + (1 / qh) ^ 5 / 5
      - (1 / qh) ^ 7 / 7 + (1 / qh) ^ 9 / 9 - (1 / qh) ^ 11 / 11)) / ql : ℚ) : ℝ))
      = ((lkPIhi : ℝ) / 2 - lkB11 (1 / ((qh : ℚ) : ℝ))) / ((ql : ℚ) : ℝ) := by
    simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_pow]
    unfold lkB11 lkA9
    ring
  rw [hV, QInterval.mem, hLoB, hHiB]
  obtain ⟨s, hsd⟩ : ∃ z : ℝ, z = Real.sqrt ((tI : ℚ) : ℝ) := ⟨_, rfl⟩
  have hr : (0:ℝ) < ((tI : ℚ) : ℝ) := by
    have h01 : (0:ℝ) < ((1:ℚ) : ℝ) := by norm_num
    exact lt_of_lt_of_le h01 (Rat.cast_le.mpr ht.le)
  have hsp : (0:ℝ) < s := by
    rw [hsd]
    exact Real.sqrt_pos.mpr hr
  have hs : (1:ℝ) < s := by
    rw [hsd]
    refine Real.lt_sqrt_of_sq_lt ?_
    have h2 : ((1:ℚ) : ℝ) < ((tI : ℚ) : ℝ) := Rat.cast_lt.mpr ht
    calc (1:ℝ) ^ 2 = 1 := by norm_num
      _ ≤ ((1:ℚ) : ℝ) := by norm_num
      _ < ((tI : ℚ) : ℝ) := h2
  have hsqb : s ≤ ((qh : ℚ) : ℝ) := by
    rw [hsd]
    exact (Real.sqrt_le_left (Rat.cast_nonneg.mpr (by linarith : (0:ℚ) ≤ qh))).mpr hqh2
  have hsqb2 : ((ql : ℚ) : ℝ) ≤ s := by
    rw [hsd]
    exact Real.le_sqrt_of_sq_le hql2
  have hqh0 : (0:ℝ) < ((qh : ℚ) : ℝ) := Rat.cast_pos.mpr (by linarith : (0:ℚ) < qh)
  have hql0 : (0:ℝ) < ((ql : ℚ) : ℝ) := Rat.cast_pos.mpr hq0
  have hql1R : (1:ℝ) ≤ ((ql : ℚ) : ℝ) := by exact_mod_cast hq3
  have hqh1R : (1:ℝ) ≤ ((qh : ℚ) : ℝ) := by exact_mod_cast hq2
  have hzlo : (1:ℝ) / ((qh : ℚ) : ℝ) ≤ 1 / s := by
    rw [div_le_div_iff₀ hqh0 hsp]
    linarith [hsqb]
  have hzhi : 1 / s ≤ (1:ℝ) / ((ql : ℚ) : ℝ) := by
    rw [div_le_div_iff₀ hsp hql0]
    linarith [hsqb2]
  have hz1 : 1 / s ≤ (1:ℝ) := (div_le_one hsp).mpr (by linarith : (1:ℝ) ≤ s)
  have hzs0 : (0:ℝ) ≤ 1 / s := div_nonneg (by norm_num) hsp.le
  have hx0u : (0:ℝ) ≤ Real.pi / 2 - Real.arctan (1 / s) := by
    have hlt := Real.arctan_lt_pi_div_two (1 / s)
    have hp2 : (0:ℝ) < Real.pi / 2 := by positivity
    linarith
  have hqzn0 : (0:ℝ) ≤ 1 / ((qh : ℚ) : ℝ) := div_nonneg (by norm_num) hqh0.le
  have hqzn1 : (1:ℝ) / ((qh : ℚ) : ℝ) ≤ 1 := (div_le_one hqh0).mpr hqh1R
  have hqlz1 : (1:ℝ) / ((ql : ℚ) : ℝ) ≤ 1 := (div_le_one hql0).mpr hql1R
  have h7 : lkB11 (1 / ((qh : ℚ) : ℝ)) ≤ Real.arctan (1 / s) :=
    le_trans (lk_atan_ge_b11 hqzn0) (Real.arctan_mono hzlo)
  have h5 : Real.arctan (1 / s) ≤ lkA9 (1 / ((ql : ℚ) : ℝ)) :=
    le_trans (lk_atan_le_a9 hzs0) (lk_a9_mono hzs0 hzhi hqlz1)
  have hzln : (0:ℝ) ≤ lkB11 (1 / ((qh : ℚ) : ℝ)) := by
    have h := lk_b11_mono (a := (0:ℝ)) (le_refl 0) hqzn0 hqzn1
    linarith [h, lk_b11_zero]
  have hme := lk_matan_eq hr
  rw [← hsd] at hme
  rw [lk_arctan_inv (by linarith : (0:ℝ) < s)] at hme
  have hpi2 : (lkPIlo : ℝ) / 2 ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ (lkPIhi : ℝ) / 2 := by
    have h := lk_pi_mem
    exact ⟨div_le_div_of_nonneg_right h.1 (by norm_num),
      div_le_div_of_nonneg_right h.2 (by norm_num)⟩
  have hp2b : (0:ℝ) ≤ Real.pi / 2 := by positivity
  have hnumlo : (lkPIlo : ℝ) / 2 - lkA9 (1 / ((ql : ℚ) : ℝ))
      ≤ Real.pi / 2 - Real.arctan (1 / s) := by
    linarith [hpi2.1, h5]
  have hnumhi : Real.pi / 2 - Real.arctan (1 / s)
      ≤ (lkPIhi : ℝ) / 2 - lkB11 (1 / ((qh : ℚ) : ℝ)) := by
    linarith [hpi2.2, h7]
  have hnumhi0 : (0:ℝ) ≤ (lkPIhi : ℝ) / 2 - lkB11 (1 / ((qh : ℚ) : ℝ)) := by
    linarith [hpi2.2, hp2b, hzln]
  constructor
  · rw [hme, div_le_div_iff₀ hqh0 hsp]
    exact mul_le_mul hnumlo hsqb hsp.le hx0u
  · rw [hme, div_le_div_iff₀ hsp hql0]
    exact mul_le_mul hnumhi hsqb2 hql0.le hnumhi0


/-! ## Audit (standard three) -/

#print axioms lk_atan_le_a9
#print axioms lk_atan_ge_b11
#print axioms lk_matan_direct9
#print axioms lk_matan_mirror
#print axioms lk_matan_u9
#print axioms lk_mirror_alg

end Kepler.Text.TaylorSecond
