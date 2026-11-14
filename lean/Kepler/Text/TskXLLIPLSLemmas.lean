/-
  TSKAJXY-XLLIPLS glue — part 1: the scalar identities.

  These are the "no new mathematics" ingredients the `evalReal` bridge
  (`Kepler.Text.PackIneqTskXLLIPLS`) needs in order to align the certificate
  expression's constant block with the Lean definitions:

  * `tsk_pi4`   — the case expression writes `pi` as `4 * atan 1`
                  (`pipeline/interval/emit_rpn.py`: "命名常量在展开期内联：
                  pi → 4*atan(1)").
  * `tsk_h0`    — the case expression writes `h0` as the exact rational
                  `63/50` (defs.json `h0 = 1.26` = 63/50).
  * `tsk_acos`  — the case expression expands `acos x` by the half-angle
                  `acos x = 2 * atan (sqrt (1 - x^2)/(1 + x))`
                  (`emit_rpn.py` docstring), used for `sol0 = 3*acos(1/3) - pi`.
  * `tsk_lmfun_ite` — the case expression encodes `lmfun`'s `h <= h0` guard as
                  the strict `h0 - h < 0` RPN `ite` (`ite(c<0, then, else)`).

  No new axiom / sorry / native_decide; standard three only.
-/
import Kepler.Text.PackingAuto2
import Mathlib

set_option maxHeartbeats 1000000

namespace Kepler.Text

/-! ## Constants -/

/-- `4 * arctan 1 = pi`. -/
theorem tsk_pi4 : 4 * Real.arctan 1 = Real.pi := by
  rw [Real.arctan_one]; ring

/-- The certificate's exact form of `h0 = 1.26`. -/
theorem tsk_h0 : h0 = 63 / 50 := by
  unfold h0; norm_num

/-- `cos (2 * arctan t) = (1 - t^2)/(1 + t^2)`. -/
theorem tsk_cos_two_arctan (t : ℝ) :
    Real.cos (2 * Real.arctan t) = (1 - t * t) / (1 + t * t) := by
  have hca : Real.cos (Real.arctan t) = 1 / Real.sqrt (1 + t ^ 2) :=
    Real.cos_arctan t
  have hsa : Real.sin (Real.arctan t) = t / Real.sqrt (1 + t ^ 2) :=
    Real.sin_arctan t
  have hD : (0 : ℝ) < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hD.le
  rw [show (2 : ℝ) * Real.arctan t = Real.arctan t + Real.arctan t by ring,
    Real.cos_add, hca, hsa]
  field_simp
  rw [hsq]

/-- `arccos x = 2 * arctan (sqrt (1 - x^2) / (1 + x))` on `(-1, 1]`
(the `emit_rpn.py` `acos` half-angle expansion at `x = 1/3`). -/
theorem tsk_acos (x : ℝ) (h1 : -1 < x) (h2 : x ≤ 1) :
    Real.arccos x = 2 * Real.arctan (Real.sqrt (1 - x * x) / (1 + x)) := by
  have hxx : x * x ≤ 1 := by nlinarith
  have hx1 : 0 < 1 + x := by linarith
  have hrad : 0 ≤ 1 - x * x := by linarith
  have hsq : Real.sqrt (1 - x * x) ^ 2 = 1 - x * x := Real.sq_sqrt hrad
  have hsqx : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := by
    rw [show (1 : ℝ) - x ^ 2 = 1 - x * x by ring]; exact hsq
  set t : ℝ := Real.sqrt (1 - x * x) / (1 + x) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact div_nonneg (Real.sqrt_nonneg _) hx1.le
  have hcos : Real.cos (2 * Real.arctan t) = x := by
    rw [tsk_cos_two_arctan, ht]
    field_simp
    rw [hsqx]; ring
  have h0le : 0 ≤ 2 * Real.arctan t := by
    have := Real.arctan_nonneg.mpr ht0
    linarith
  have hle : 2 * Real.arctan t ≤ Real.pi := by
    have := Real.arctan_lt_pi_div_two t
    linarith
  exact Real.arccos_eq_of_eq_cos h0le hle hcos.symm

/-- `lmfun` in the certificate's `ite(c < 0, then, else)` encoding
(`h0 - h < 0` is the negation of `h ≤ h0`, rewritten by `sub_lt_zero` to
`h0 < h`). -/
theorem tsk_lmfun_ite (h : ℝ) :
    (if (63 : ℝ) / 50 < h then (0 : ℝ)
      else ((63 : ℝ) / 50 - h) / ((63 : ℝ) / 50 - 1)) = lmfun h := by
  have h0' : h0 = (63 : ℝ) / 50 := tsk_h0
  unfold lmfun
  rw [h0']
  by_cases hh : h ≤ (63 : ℝ) / 50
  · rw [if_pos hh]
    rw [if_neg (by linarith : ¬ ((63 : ℝ) / 50 < h))]
  · rw [if_neg hh]
    rw [if_pos (by linarith : (63 : ℝ) / 50 < h)]

end Kepler.Text
