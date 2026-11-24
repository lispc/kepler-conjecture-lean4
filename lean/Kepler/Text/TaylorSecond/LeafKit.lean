/-
Kepler.Text.TaylorSecond.LeafKit — lane `wt1-leaf-chain-w1` (2026-11-24),
phase 1 core: the interval machinery consumed by the generated single-leaf
`w1F2` D11 chain (`LeafD11`).

Content.
* §0 constant brackets (pi, sqrt 2, mm1, mm2) as real memberships.
* §1 the landed A7/A5 arctan pair (`nb12w_arctan_ge_sub7`,
  `Kepler.NliBanks12.nb12_arctan_le_sub5`) plus monotonicity on `[0, 1]`.
* §2 the three arctan identities (via Mathlib `arctan_add` /
  `arctan_inv_of_pos`).
* §3 matan point enclosures: direct form, w-form (`r > 1`), u-form — each
  fully generic, concluded at rational brackets, so the generated per-point
  lemmas are norm_num only.
* §4 transports: matan value (strict antitone, `nb12w_matan_strictAntiOn`),
  matanDD (strict antitone, landed) with endpoint coherent enclosures,
  matanD (pure interval ops through `e(t) = 1/(1+t) - matan t`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.Text.TaylorSecond.QInterval
import Kepler.Text.Wt1TowerDeriv
import Kepler.Text.Wt1MatanDDAnti
import Kepler.Text.PackingAuto2
import Kepler.Text.PackingAuto21
import Kepler.Text.Gamma4Val
import Kepler.NliBanks12

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

/-! ## 0. Constant brackets -/

/-- Lower pi bracket (weakened `g4v_pi_bounds_d8`). -/
def lkPIlo : ℚ := 314159265 / 10 ^ 8

/-- Upper pi bracket. -/
def lkPIhi : ℚ := 314159266 / 10 ^ 8

/-- Lower sqrt2 bracket (weakened `g4v_sqrt2_bounds`). -/
def lkS2lo : ℚ := 141421356 / 10 ^ 8

/-- Upper sqrt2 bracket. -/
def lkS2hi : ℚ := 141421357 / 10 ^ 8

theorem lk_pi_mem : (lkPIlo : ℝ) ≤ Real.pi ∧ Real.pi ≤ (lkPIhi : ℝ) := by
  have h1 : (lkPIlo : ℝ) = (3.14159265 : ℝ) := by norm_num [lkPIlo]
  have h2 : (lkPIhi : ℝ) = (3.14159266 : ℝ) := by norm_num [lkPIhi]
  rw [h1, h2]
  exact ⟨le_of_lt g4v_pi_bounds_d8.1, le_of_lt g4v_pi_bounds_d8.2⟩

theorem lk_sqrt2_mem : (lkS2lo : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (lkS2hi : ℝ) := by
  have h1 : (lkS2lo : ℝ) = (1.41421356 : ℝ) := by norm_num [lkS2lo]
  have h2 : (lkS2hi : ℝ) = (1.41421357 : ℝ) := by norm_num [lkS2hi]
  rw [h1, h2]
  exact ⟨le_of_lt g4v_sqrt2_bounds.1, le_of_lt g4v_sqrt2_bounds.2⟩

theorem lk_mm1_mem : ((1.0120808 : ℚ) : ℝ) ≤ mm1 ∧ mm1 ≤ ((1.0120809 : ℚ) : ℝ) :=
  ⟨g4v_mm1_bounds.1, g4v_mm1_bounds.2⟩

theorem lk_mm2_mem : ((0.02541450 : ℚ) : ℝ) ≤ mm2 ∧ mm2 ≤ ((0.02541451 : ℚ) : ℝ) :=
  ⟨g4v_mm2_bounds.1, g4v_mm2_bounds.2⟩

/-! ## 1. The landed A7/A5 pair and monotonicity on `[0, 1]` -/

/-- The order-5 truncation `s - s³/3 + s⁵/5`. -/
noncomputable def lkA5 (s : ℝ) : ℝ := s - s ^ 3 / 3 + s ^ 5 / 5

/-- The order-7 truncation `s - s³/3 + s⁵/5 - s⁷/7`. -/
noncomputable def lkA7 (s : ℝ) : ℝ := s - s ^ 3 / 3 + s ^ 5 / 5 - s ^ 7 / 7

theorem lk_hasDerivAt_a5 (x : ℝ) : HasDerivAt lkA5 (1 - x ^ 2 + x ^ 4) x := by
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (x ^ 2) x := by
    have := (hasDerivAt_pow 3 x).div_const 3
    simpa [pow_succ] using this
  have h5 : HasDerivAt (fun x : ℝ => x ^ 5 / 5) (x ^ 4) x := by
    have := (hasDerivAt_pow 5 x).div_const 5
    simpa [pow_succ] using this
  have h : HasDerivAt (fun x : ℝ => x - x ^ 3 / 3 + x ^ 5 / 5) (1 - x ^ 2 + x ^ 4) x :=
    ((hasDerivAt_id x).sub h3).add h5
  rw [show (fun x : ℝ => x - x ^ 3 / 3 + x ^ 5 / 5) = lkA5 from rfl] at h
  exact h

theorem lk_deriv_a5 (x : ℝ) : deriv lkA5 x = 1 - x ^ 2 + x ^ 4 :=
  (lk_hasDerivAt_a5 x).deriv

theorem lk_hasDerivAt_a7 (x : ℝ) : HasDerivAt lkA7 (1 - x ^ 2 + x ^ 4 - x ^ 6) x := by
  have h7 : HasDerivAt (fun x : ℝ => x ^ 7 / 7) (x ^ 6) x := by
    have := (hasDerivAt_pow 7 x).div_const 7
    simpa [pow_succ] using this
  have h := (lk_hasDerivAt_a5 x).sub h7
  rw [show lkA7 = fun x : ℝ => lkA5 x - x ^ 7 / 7 from rfl]
  exact h

theorem lk_deriv_a7 (x : ℝ) : deriv lkA7 x = 1 - x ^ 2 + x ^ 4 - x ^ 6 :=
  (lk_hasDerivAt_a7 x).deriv

theorem lk_atan_ge_a7 {s : ℝ} (hs : 0 ≤ s) : lkA7 s ≤ Real.arctan s :=
  nb12w_arctan_ge_sub7 hs

theorem lk_atan_le_a5 {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ lkA5 s :=
  Kepler.NliBanks12.nb12_arctan_le_sub5 hs

/-- `A5` is increasing on `[0, 1]`. -/
theorem lk_a5_mono {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) : lkA5 a ≤ lkA5 b := by
  have hsign : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (0 : ℝ) ≤ 1 - x ^ 2 + x ^ 4 := by
    intro x hx0 hx1
    have h2 : (0 : ℝ) ≤ (x ^ 2 - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith
  have hdiff : Differentiable ℝ lkA5 := fun x => (lk_hasDerivAt_a5 x).differentiableAt
  have hcont : ContinuousOn lkA5 (Set.Icc a b) := hdiff.continuous.continuousOn
  have hdif : DifferentiableOn ℝ lkA5 (interior (Set.Icc a b)) := fun x _ =>
    (lk_hasDerivAt_a5 x).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn lkA5 (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdif (by
      intro x hx
      rw [interior_Icc] at hx
      rw [lk_deriv_a5]
      exact hsign x (le_trans ha0 hx.1.le) (le_trans hx.2.le hb1))
  exact hmono (Set.mem_Icc.mpr ⟨le_refl _, hab⟩) (Set.mem_Icc.mpr ⟨hab, le_refl _⟩) hab

/-- `A7` is increasing on `[0, 1]`. -/
theorem lk_a7_mono {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) : lkA7 a ≤ lkA7 b := by
  have hsign : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (0 : ℝ) ≤ 1 - x ^ 2 + x ^ 4 - x ^ 6 := by
    intro x hx0 hx1
    have hle : x ^ 2 ≤ 1 := by nlinarith
    have hp : (0 : ℝ) ≤ (1 - x ^ 2) * (1 + x ^ 4) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg (x ^ 2)])
    have hexp : 1 - x ^ 2 + x ^ 4 - x ^ 6 = (1 - x ^ 2) * (1 + x ^ 4) := by ring
    rw [hexp]
    exact hp
  have hdiff : Differentiable ℝ lkA7 := fun x => (lk_hasDerivAt_a7 x).differentiableAt
  have hcont : ContinuousOn lkA7 (Set.Icc a b) := hdiff.continuous.continuousOn
  have hdif : DifferentiableOn ℝ lkA7 (interior (Set.Icc a b)) := fun x _ =>
    (lk_hasDerivAt_a7 x).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn lkA7 (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdif (by
      intro x hx
      rw [interior_Icc] at hx
      rw [lk_deriv_a7]
      exact hsign x (le_trans ha0 hx.1.le) (le_trans hx.2.le hb1))
  exact hmono (Set.mem_Icc.mpr ⟨le_refl _, hab⟩) (Set.mem_Icc.mpr ⟨hab, le_refl _⟩) hab

/-! ## 2. The three arctan identities -/

/-- For `0 < s < 1`: `arctan s = π/4 − arctan ((1−s)/(1+s))`. -/
theorem lk_arctan_wminus {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.arctan s = Real.pi / 4 - Real.arctan ((1 - s) / (1 + s)) := by
  have hws : ((1 - s) / (1 + s)) * s < 1 := by
    calc ((1 - s) / (1 + s)) * s
        < ((1 - s) / (1 + s)) * 1 := mul_lt_mul_of_pos_left hs1 (by positivity)
      _ = ((1 - s) / (1 + s)) := by ring
      _ < 1 := by
            rw [div_lt_one (by linarith : (0:ℝ) < 1 + s)]
            linarith
  have hadd := Real.arctan_add hws
  have hrat : ((1 - s) / (1 + s) + s) / (1 - (1 - s) / (1 + s) * s) = 1 := by
    have hpos : (0:ℝ) < 1 - (1 - s) / (1 + s) * s := sub_pos.mpr hws
    rw [div_eq_iff (ne_of_gt hpos)]
    field_simp
    ring
  rw [hrat, Real.arctan_one] at hadd
  linarith

/-- For `1 < s`: `arctan s = π/4 + arctan ((s−1)/(s+1))`. -/
theorem lk_arctan_wplus {s : ℝ} (hs1 : 1 < s) :
    Real.arctan s = Real.pi / 4 + Real.arctan ((s - 1) / (s + 1)) := by
  have hs0 : (0:ℝ) < s := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hs1.le
  have hinv0 : (0:ℝ) < 1 / s := by positivity
  have hlt1 : 1 / s < 1 := (div_lt_one hs0).mpr hs1
  have hw := lk_arctan_wminus hinv0 hlt1
  have hform : (1 - 1 / s) / (1 + 1 / s) = (s - 1) / (s + 1) := by
    field_simp
  rw [hform] at hw
  have hinv := Real.arctan_inv_of_pos hs0
  have h1s : ((1:ℝ) / s) = s⁻¹ := by rw [div_eq_mul_inv, one_mul]
  rw [h1s] at hw
  linarith [Real.pi_pos]

/-- For `0 < s`: `arctan s = π/2 − arctan (1/s)`. -/
theorem lk_arctan_inv {s : ℝ} (hs0 : 0 < s) :
    Real.arctan s = Real.pi / 2 - Real.arctan (1 / s) := by
  have h1s : ((1:ℝ) / s) = s⁻¹ := by rw [div_eq_mul_inv, one_mul]
  have h := Real.arctan_inv_of_pos hs0
  rw [h1s.symm] at h
  linarith

/-! ## 3. matan point enclosures (all concluded at rational brackets) -/

/-- `matan r = arctan (√r) / √r` for `0 < r`. -/
theorem lk_matan_eq {r : ℝ} (hr : 0 < r) :
    matan r = Real.arctan (Real.sqrt r) / Real.sqrt r := by
  unfold matan
  rw [if_neg (ne_of_gt hr), if_pos hr]

/-- Odd powers of a square root split. -/
theorem lk_sqrt_pow {t : ℝ} (hsq : Real.sqrt t ^ 2 = t) (n : ℕ) :
    Real.sqrt t ^ (2 * n + 1) = Real.sqrt t * t ^ n := by
  rw [pow_succ]
  have h2 : Real.sqrt t ^ (2 * n) = t ^ n := by
    rw [pow_mul, hsq]
  rw [h2]
  ring

/-- Direct-form point enclosure: for `r > 0`,
`matan r ∈ [1 − r/3 + r²/5 − r³/7, 1 − r/3 + r²/5]`. -/
theorem lk_matan_direct (V : QInterval) (tI : ℚ) (ht : (0:ℚ) < tI)
    (hV : V = QInterval.mk (1 - tI / 3 + tI ^ 2 / 5 - tI ^ 3 / 7) (1 - tI / 3 + tI ^ 2 / 5)) :
    V.mem (matan ((tI : ℚ) : ℝ)) := by
  rw [hV, QInterval.mem]
  simp only [QInterval.lo, QInterval.hi, Rat.cast_div, Rat.cast_sub, Rat.cast_add,
    Rat.cast_one, Rat.cast_mul, Rat.cast_pow]
  have hr : (0:ℝ) < ((tI : ℚ) : ℝ) := by exact_mod_cast ht
  have hsq : Real.sqrt ((tI : ℚ) : ℝ) ^ 2 = ((tI : ℚ) : ℝ) := Real.sq_sqrt hr.le
  have hme := lk_matan_eq hr
  have s0 : (0:ℝ) ≤ Real.sqrt ((tI : ℚ) : ℝ) := Real.sqrt_nonneg _
  have hlo := lk_atan_ge_a7 s0
  have hhi := lk_atan_le_a5 s0
  simp only [lkA7, lkA5] at hlo hhi
  rw [show (3:ℕ) = 2 * 1 + 1 by norm_num, lk_sqrt_pow hsq,
      show (5:ℕ) = 2 * 2 + 1 by norm_num, lk_sqrt_pow hsq,
      show (7:ℕ) = 2 * 3 + 1 by norm_num, lk_sqrt_pow hsq] at hlo
  rw [show (3:ℕ) = 2 * 1 + 1 by norm_num, lk_sqrt_pow hsq,
      show (5:ℕ) = 2 * 2 + 1 by norm_num, lk_sqrt_pow hsq] at hhi
  simp only [pow_one] at hlo hhi
  simp only [hme, le_div_iff₀ (Real.sqrt_pos.mpr hr), div_le_iff₀ (Real.sqrt_pos.mpr hr)]
  push_cast
  constructor
  · nlinarith [hlo, hr.le]
  · nlinarith [hhi, hr.le]

/-- w-form point enclosure for `1 < r` with rational sqrt brackets
`ql² ≤ r ≤ qh²`, `1 ≤ ql ≤ qh < 1 + ql`: matan r is enclosed by
`(πlo/4 + a7((ql−1)/(qh+1)))/qh .. (πhi/4 + a5((qh−1)/(ql+1)))/ql`. -/
theorem lk_matan_wplus (V : QInterval) (tI ql qh : ℚ) (ht : (1:ℚ) < tI)
    (hql2 : ((ql : ℚ) : ℝ) ^ 2 ≤ ((tI : ℚ) : ℝ))
    (hqh2 : ((tI : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) ^ 2)
    (hq0 : (0:ℚ) < ql) (hq1 : ql ≤ qh) (hq2 : (1:ℚ) ≤ qh) (hq3 : (qh:ℚ) < 1 + ql)
    (hq4 : (1:ℚ) ≤ ql)
    (hV : V = QInterval.mk
      ((lkPIlo / 4 + ((ql - 1) / (qh + 1) - ((ql - 1) / (qh + 1)) ^ 3 / 3
          + ((ql - 1) / (qh + 1)) ^ 5 / 5 - ((ql - 1) / (qh + 1)) ^ 7 / 7)) / qh)
      ((lkPIhi / 4 + ((qh - 1) / (ql + 1) - ((qh - 1) / (ql + 1)) ^ 3 / 3
          + ((qh - 1) / (ql + 1)) ^ 5 / 5)) / ql)) :
    V.mem (matan ((tI : ℚ) : ℝ)) := by
  have hLoB : ((((lkPIlo / 4 + ((ql - 1) / (qh + 1) - ((ql - 1) / (qh + 1)) ^ 3 / 3
      + ((ql - 1) / (qh + 1)) ^ 5 / 5 - ((ql - 1) / (qh + 1)) ^ 7 / 7)) / qh : ℚ) : ℝ))
      = ((lkPIlo : ℝ) / 4 + lkA7 ((((ql : ℚ) : ℝ) - 1) / (((qh : ℚ) : ℝ) + 1)))
        / ((qh : ℚ) : ℝ) := by
    simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_pow]
    unfold lkA7
    ring
  have hHiB : ((((lkPIhi / 4 + ((qh - 1) / (ql + 1) - ((qh - 1) / (ql + 1)) ^ 3 / 3
      + ((qh - 1) / (ql + 1)) ^ 5 / 5)) / ql : ℚ) : ℝ))
      = ((lkPIhi : ℝ) / 4 + lkA5 ((((qh : ℚ) : ℝ) - 1) / (((ql : ℚ) : ℝ) + 1)))
        / ((ql : ℚ) : ℝ) := by
    simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_pow]
    unfold lkA5
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
  have hq1c : ((ql : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) := Rat.cast_le.mpr hq1
  have hql1c : (1:ℝ) ≤ ((ql : ℚ) : ℝ) := by exact_mod_cast hq4
  have hq3c : ((qh : ℚ) : ℝ) < 1 + ((ql : ℚ) : ℝ) := by exact_mod_cast hq3
  have h2w : (0:ℝ) < ((qh : ℚ) : ℝ) + 1 := by linarith
  have h1w : (0:ℝ) < s + 1 := by linarith
  have h3w : (0:ℝ) < ((ql : ℚ) : ℝ) + 1 := by linarith
  have hwlo : (((ql : ℚ) : ℝ) - 1) / (((qh : ℚ) : ℝ) + 1) ≤ (s - 1) / (s + 1) := by
    rw [div_le_div_iff₀ h2w h1w]
    have hprodA : (0:ℝ) ≤ (s - ((ql : ℚ) : ℝ)) * (((qh : ℚ) : ℝ) - ((ql : ℚ) : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    have hprod2 : (0:ℝ) ≤ (((ql : ℚ) : ℝ) - 1) * (((qh : ℚ) : ℝ) - ((ql : ℚ) : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprodA, hprod2, hsp, hql1c, hq1c]
  have hwhi : (s - 1) / (s + 1) ≤ (((qh : ℚ) : ℝ) - 1) / (((ql : ℚ) : ℝ) + 1) := by
    rw [div_le_div_iff₀ h1w h3w]
    have hprodA : (0:ℝ) ≤ (s - ((ql : ℚ) : ℝ)) * (((qh : ℚ) : ℝ) - ((ql : ℚ) : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    have hprodC : (0:ℝ) ≤ (((qh : ℚ) : ℝ) - s) * (((ql : ℚ) : ℝ) + 2) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [hprodA, hprodC, hq1c, hql1c]
  have h05 : lkA5 (0:ℝ) = 0 := by unfold lkA5; norm_num
  have h07 : lkA7 (0:ℝ) = 0 := by unfold lkA7; norm_num
  have hwlgeR : (0:ℝ) ≤ (((ql : ℚ) : ℝ) - 1) / (((qh : ℚ) : ℝ) + 1) :=
    div_nonneg (by linarith) (by linarith)
  have hwlleR : (((ql : ℚ) : ℝ) - 1) / (((qh : ℚ) : ℝ) + 1) ≤ (1:ℝ) := by
    rw [div_le_one (by linarith : (0:ℝ) < ((qh : ℚ) : ℝ) + 1)]
    linarith
  have hwhgeR : (0:ℝ) ≤ (((qh : ℚ) : ℝ) - 1) / (((ql : ℚ) : ℝ) + 1) :=
    div_nonneg (by linarith) (by linarith)
  have hwhleR : (((qh : ℚ) : ℝ) - 1) / (((ql : ℚ) : ℝ) + 1) ≤ (1:ℝ) := by
    rw [div_le_one (by linarith : (0:ℝ) < ((ql : ℚ) : ℝ) + 1)]
    linarith [hq3c]
  have hw0 : (0:ℝ) ≤ (s - 1) / (s + 1) :=
    div_nonneg (by linarith) (by linarith)
  have hwle1 : (s - 1) / (s + 1) ≤ (1:ℝ) := by
    rw [div_le_one (by linarith : (0:ℝ) < s + 1)]
    linarith
  have hx0 : (0:ℝ) ≤ Real.pi / 4 + Real.arctan ((s - 1) / (s + 1)) := by
    have hpa := (Real.arctan_pos).mpr
      (div_pos (by linarith : (0:ℝ) < s - 1) (by linarith : (0:ℝ) < s + 1))
    have hp4 : (0:ℝ) < Real.pi / 4 := by positivity
    linarith
  have h7 : lkA7 ((((ql : ℚ) : ℝ) - 1) / (((qh : ℚ) : ℝ) + 1))
      ≤ Real.arctan ((s - 1) / (s + 1)) :=
    le_trans (lk_a7_mono hwlgeR hwlo hwle1) (lk_atan_ge_a7 hw0)
  have h5 : Real.arctan ((s - 1) / (s + 1))
      ≤ lkA5 ((((qh : ℚ) : ℝ) - 1) / (((ql : ℚ) : ℝ) + 1)) :=
    le_trans (lk_atan_le_a5 hw0) (lk_a5_mono hw0 hwhi hwhleR)
  have hwhn : (0:ℝ) ≤ lkA5 ((((qh : ℚ) : ℝ) - 1) / (((ql : ℚ) : ℝ) + 1)) := by
    have h := lk_a5_mono (a := (0:ℝ)) (le_refl 0) hwhgeR hwhleR
    linarith [h, h05]
  have hme := lk_matan_eq hr
  rw [← hsd] at hme
  rw [lk_arctan_wplus hs] at hme
  have hpi4 : (lkPIlo : ℝ) / 4 ≤ Real.pi / 4 ∧ Real.pi / 4 ≤ (lkPIhi : ℝ) / 4 := by
    have h := lk_pi_mem
    exact ⟨div_le_div_of_nonneg_right h.1 (by norm_num),
      div_le_div_of_nonneg_right h.2 (by norm_num)⟩
  have hp4 : (0:ℝ) ≤ Real.pi / 4 := by positivity
  have hnumlo : (lkPIlo : ℝ) / 4 + lkA7 ((((ql : ℚ) : ℝ) - 1) / (((qh : ℚ) : ℝ) + 1))
      ≤ Real.pi / 4 + Real.arctan ((s - 1) / (s + 1)) := by
    linarith [hpi4.1, h7]
  have hnumhi : Real.pi / 4 + Real.arctan ((s - 1) / (s + 1))
      ≤ (lkPIhi : ℝ) / 4 + lkA5 ((((qh : ℚ) : ℝ) - 1) / (((ql : ℚ) : ℝ) + 1)) := by
    linarith [hpi4.2, h5]
  have hnumhi0 : (0:ℝ) ≤ (lkPIhi : ℝ) / 4
      + lkA5 ((((qh : ℚ) : ℝ) - 1) / (((ql : ℚ) : ℝ) + 1)) := by
    linarith [hpi4.2, hp4, hwhn]
  constructor
  · rw [hme, div_le_div_iff₀ hqh0 hsp]
    exact mul_le_mul hnumlo hsqb hsp.le hx0
  · rw [hme, div_le_div_iff₀ hsp hql0]
    exact mul_le_mul hnumhi hsqb2 hql0.le hnumhi0

/-- u-form point enclosure for `1 < r` with rational sqrt brackets
`ql² ≤ r ≤ qh²`, `1 ≤ ql ≤ qh`: matan r is enclosed by
`(πlo/2 − a5(1/qh))/qh .. (πhi/2 − a7(1/ql))/ql`. -/
theorem lk_matan_u (V : QInterval) (tI ql qh : ℚ) (ht : (1:ℚ) < tI)
    (hql2 : ((ql : ℚ) : ℝ) ^ 2 ≤ ((tI : ℚ) : ℝ))
    (hqh2 : ((tI : ℚ) : ℝ) ≤ ((qh : ℚ) : ℝ) ^ 2)
    (hq0 : (0:ℚ) < ql) (hq1 : ql ≤ qh) (hq2 : (1:ℚ) ≤ qh) (hq3 : (1:ℚ) ≤ ql)
    (hV : V = QInterval.mk
      ((lkPIlo / 2 - (1 / ql - (1 / ql) ^ 3 / 3 + (1 / ql) ^ 5 / 5)) / qh)
      ((lkPIhi / 2 - (1 / qh - (1 / qh) ^ 3 / 3 + (1 / qh) ^ 5 / 5 - (1 / qh) ^ 7 / 7)) / ql)) :
    V.mem (matan ((tI : ℚ) : ℝ)) := by
  have hLoB : ((((lkPIlo / 2 - (1 / ql - (1 / ql) ^ 3 / 3 + (1 / ql) ^ 5 / 5)) / qh : ℚ) : ℝ))
      = ((lkPIlo : ℝ) / 2 - lkA5 (1 / ((ql : ℚ) : ℝ))) / ((qh : ℚ) : ℝ) := by
    simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_pow]
    unfold lkA5
    ring
  have hHiB : ((((lkPIhi / 2 - (1 / qh - (1 / qh) ^ 3 / 3 + (1 / qh) ^ 5 / 5
      - (1 / qh) ^ 7 / 7)) / ql : ℚ) : ℝ))
      = ((lkPIhi : ℝ) / 2 - lkA7 (1 / ((qh : ℚ) : ℝ))) / ((ql : ℚ) : ℝ) := by
    simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_mul, Rat.cast_pow]
    unfold lkA7
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
  have h05 : lkA5 (0:ℝ) = 0 := by unfold lkA5; norm_num
  have h07 : lkA7 (0:ℝ) = 0 := by unfold lkA7; norm_num
  have hqzn0 : (0:ℝ) ≤ 1 / ((qh : ℚ) : ℝ) := div_nonneg (by norm_num) hqh0.le
  have hqzn1 : (1:ℝ) / ((qh : ℚ) : ℝ) ≤ 1 := (div_le_one hqh0).mpr hqh1R
  have hqlz1 : (1:ℝ) / ((ql : ℚ) : ℝ) ≤ 1 := (div_le_one hql0).mpr hql1R
  have h7 : lkA7 (1 / ((qh : ℚ) : ℝ)) ≤ Real.arctan (1 / s) :=
    le_trans (lk_a7_mono hqzn0 hzlo hz1) (lk_atan_ge_a7 hzs0)
  have h5 : Real.arctan (1 / s) ≤ lkA5 (1 / ((ql : ℚ) : ℝ)) :=
    le_trans (lk_atan_le_a5 hzs0) (lk_a5_mono hzs0 hzhi hqlz1)
  have hzln : (0:ℝ) ≤ lkA7 (1 / ((qh : ℚ) : ℝ)) := by
    have h := lk_a7_mono (a := (0:ℝ)) (le_refl 0) hqzn0 hqzn1
    linarith [h, h07]
  have hme := lk_matan_eq hr
  rw [← hsd] at hme
  rw [lk_arctan_inv (by linarith : (0:ℝ) < s)] at hme
  have hpi2 : (lkPIlo : ℝ) / 2 ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ (lkPIhi : ℝ) / 2 := by
    have h := lk_pi_mem
    exact ⟨div_le_div_of_nonneg_right h.1 (by norm_num),
      div_le_div_of_nonneg_right h.2 (by norm_num)⟩
  have hp2b : (0:ℝ) ≤ Real.pi / 2 := by positivity
  have hnumlo : (lkPIlo : ℝ) / 2 - lkA5 (1 / ((ql : ℚ) : ℝ))
      ≤ Real.pi / 2 - Real.arctan (1 / s) := by
    linarith [hpi2.1, h5]
  have hnumhi : Real.pi / 2 - Real.arctan (1 / s)
      ≤ (lkPIhi : ℝ) / 2 - lkA7 (1 / ((qh : ℚ) : ℝ)) := by
    linarith [hpi2.2, h7]
  have hnumhi0 : (0:ℝ) ≤ (lkPIhi : ℝ) / 2 - lkA7 (1 / ((qh : ℚ) : ℝ)) := by
    linarith [hpi2.2, hp2b, hzln]
  constructor
  · rw [hme, div_le_div_iff₀ hqh0 hsp]
    exact mul_le_mul hnumlo hsqb hsp.le hx0u
  · rw [hme, div_le_div_iff₀ hsp hql0]
    exact mul_le_mul hnumhi hsqb2 hql0.le hnumhi0


/-! ## 4. Transports -/

/-- matan value transport (strict antitone on the positive branch). -/
theorem lk_matan_val_transport (lo hi t : ℝ) (hlo : 0 < lo) (hlt : lo ≤ t) (htu : t ≤ hi)
    (Vl Vh : QInterval) (hVl : Vl.mem (matan lo)) (hVh : Vh.mem (matan hi)) :
    (QInterval.mk Vh.lo Vl.hi).mem (matan t) := by
  have him : t ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  have hlo' : lo ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  have hhi' : hi ∈ Set.Ioi (-1) := Set.mem_Ioi.mpr (by linarith)
  have h1 : matan t ≤ matan lo := nb12w_matan_strictAntiOn.antitoneOn hlo' him hlt
  have h2 : matan hi ≤ matan t := nb12w_matan_strictAntiOn.antitoneOn him hhi' htu
  rw [QInterval.mem]
  exact ⟨le_trans hVh.1 h2, le_trans h1 hVl.2⟩

/-- matanDD transport (strict antitone on the positive branch, landed). -/
theorem lk_matanDD_transport (lo hi t : ℝ) (hlo : 0 < lo) (hlt : lo ≤ t) (htu : t ≤ hi)
    (Dl Dh : QInterval) (hDl : Dl.mem (matanDD lo)) (hDh : Dh.mem (matanDD hi)) :
    (QInterval.mk Dh.lo Dl.hi).mem (matanDD t) := by
  have ht : 0 < t := lt_of_lt_of_le hlo hlt
  have hi0 : 0 < hi := lt_of_lt_of_le ht htu
  have h1 : matanDD hi ≤ matanDD t :=
    matanDD_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr ht) (Set.mem_Ioi.mpr hi0) htu
  have h2 : matanDD t ≤ matanDD lo :=
    matanDD_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr (show 0 < lo from hlo))
      (Set.mem_Ioi.mpr ht) hlt
  rw [QInterval.mem]
  exact ⟨le_trans hDh.1 h1, le_trans h2 hDl.2⟩

/-- Pointwise `matanDD` enclosure from a coherent e-interval (generic). -/
theorem lk_matanDD_pt_mem (tI : ℚ) (V E D : QInterval) (ht : (0:ℚ) < tI)
    (hV : V.mem (matan ((tI : ℚ) : ℝ)))
    (hE : E = (QInterval.const (1 / (1 + tI))).sub V)
    (hD : D = (((QInterval.const (3 / (4 * tI * tI))).mul E).neg).sub
      (QInterval.const (1 / (2 * tI * (1 + tI) ^ 2)))) :
    D.mem (matanDD ((tI : ℚ) : ℝ)) := by
  have ht0 : ((tI : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  have hAc : (QInterval.const (1 / (1 + tI))).mem (1 / (1 + ((tI : ℚ) : ℝ))) := by
    simp only [QInterval.const, QInterval.mem, Rat.cast_div, Rat.cast_one, Rat.cast_add]
    exact ⟨le_of_eq rfl, le_of_eq rfl⟩
  have hsub := QInterval.mem_sub hAc hV
  have hcastC : (((3 / (4 * tI * tI) : ℚ) : ℝ))
      = (3:ℝ) / (4 * ((tI : ℚ) : ℝ) ^ 2) := by
    rw [Rat.cast_div, Rat.cast_mul, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_ofNat]
    congr 1
    ring
  have hconst : (QInterval.const (3 / (4 * tI * tI))).mem
      ((3:ℝ) / (4 * ((tI : ℚ) : ℝ) ^ 2)) := by
    have h := QInterval.mem_const (q := (3 / (4 * tI * tI) : ℚ))
    rw [hcastC] at h
    exact h
  have hterm1 := QInterval.mem_neg (QInterval.mem_mul hconst hsub)
  have hcastT : (((1 / (2 * tI * (1 + tI) ^ 2) : ℚ) : ℝ))
      = (1:ℝ) / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2) := by
    rw [Rat.cast_div, Rat.cast_mul, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_one, Rat.cast_ofNat]
  have hT : (QInterval.const (1 / (2 * tI * (1 + tI) ^ 2))).mem
      ((1:ℝ) / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2)) := by
    have h := QInterval.mem_const (q := (1 / (2 * tI * (1 + tI) ^ 2) : ℚ))
    rw [hcastT] at h
    exact h
  have hmem := QInterval.mem_sub hterm1 hT
  rw [matanDD_of_ne ht0]
  rw [show -((3 : ℝ) / (4 * ((tI : ℚ) : ℝ) ^ 2))
        * (1 / (1 + ((tI : ℚ) : ℝ)) - matan ((tI : ℚ) : ℝ))
        - 1 / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2)
      = -((3 : ℝ) / (4 * ((tI : ℚ) : ℝ) ^ 2)
          * (1 / (1 + ((tI : ℚ) : ℝ)) - matan ((tI : ℚ) : ℝ)))
        - 1 / (2 * ((tI : ℚ) : ℝ) * (1 + ((tI : ℚ) : ℝ)) ^ 2) from by ring]
  subst hE
  rw [hD]
  exact hmem

/-- matanD on the whole slot interval: pure interval ops through
`e(t) = 1/(1+t) − matan t` and `matanD t = (1/(2t)) · e(t)`. -/
theorem lk_matanD_ops (TI VI : QInterval) (hpos : (0:ℚ) < TI.lo) (horder : TI.lo ≤ TI.hi)
    (hVI : ∀ x : ℝ, ((TI.lo : ℚ) : ℝ) ≤ x → x ≤ ((TI.hi : ℚ) : ℝ) → VI.mem (matan x)) :
    ∀ t : ℝ, ((TI.lo : ℚ) : ℝ) ≤ t → t ≤ ((TI.hi : ℚ) : ℝ) →
      ((((QInterval.const (1:ℚ)).add TI).inv.sub VI).mul
        (((QInterval.const (2:ℚ)).mul TI).inv)).mem (matanD t) := by
  intro t h1t h2t
  have ht0 : t ≠ 0 := by
    have hp : (0:ℝ) < ((TI.lo : ℚ) : ℝ) := by exact_mod_cast hpos
    exact ne_of_gt (lt_of_lt_of_le hp h1t)
  rw [matanD_of_ne ht0]
  rw [show (1 / (2 * t)) * (1 / (1 + t) - matan t)
      = ((((1:ℚ) : ℝ) + t)⁻¹ - matan t) * ((((2:ℚ) : ℝ) * t)⁻¹) from by
    rw [one_div, one_div, Rat.cast_one, Rat.cast_ofNat]
    ring]
  have h1pos : (0:ℚ) < ((QInterval.const (1:ℚ)).add TI).lo := by
    show (0:ℚ) < (1:ℚ) + TI.lo
    linarith
  have h2pos : (0:ℚ) < ((QInterval.const (2:ℚ)).mul TI).lo := by
    show (0:ℚ) < min (min ((2:ℚ) * TI.lo) ((2:ℚ) * TI.hi))
      (min ((2:ℚ) * TI.lo) ((2:ℚ) * TI.hi))
    simp only [lt_min_iff]
    have hlo : (0:ℚ) < (2:ℚ) * TI.lo := mul_pos (by norm_num) hpos
    have hhi : (0:ℚ) < (2:ℚ) * TI.hi :=
      mul_pos (by norm_num) (lt_of_lt_of_le hpos horder)
    exact ⟨⟨hlo, hhi⟩, ⟨hlo, hhi⟩⟩
  have hAc : (QInterval.const (1:ℚ)).mem (((1:ℚ) : ℝ)) := QInterval.mem_const
  have hBc : (QInterval.const (2:ℚ)).mem (((2:ℚ) : ℝ)) := QInterval.mem_const
  have hA : (((QInterval.const (1:ℚ)).add TI)).mem ((((1:ℚ) : ℝ)) + t) :=
    QInterval.mem_add hAc ⟨h1t, h2t⟩
  have hAi := QInterval.mem_inv hA (Or.inl h1pos)
  have hsub := QInterval.mem_sub hAi (hVI t h1t h2t)
  have hB : (((QInterval.const (2:ℚ)).mul TI)).mem ((((2:ℚ) : ℝ)) * t) :=
    QInterval.mem_mul hBc ⟨h1t, h2t⟩
  have hBi := QInterval.mem_inv hB (Or.inl h2pos)
  exact QInterval.mem_mul hsub hBi


#print axioms lk_a5_mono
#print axioms lk_a7_mono
#print axioms lk_arctan_wminus
#print axioms lk_arctan_wplus
#print axioms lk_arctan_inv
#print axioms lk_matan_direct
#print axioms lk_matan_wplus
#print axioms lk_matan_u
#print axioms lk_matan_val_transport
#print axioms lk_matanDD_transport
#print axioms lk_matanDD_pt_mem
#print axioms lk_matanD_ops

end Kepler.Text.TaylorSecond
