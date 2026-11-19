/-
Kepler.NliBanks21 — lane `cell3-wt1-build-w1`: the bank `bank_QZECFICwt1`
(Assembly debt `nliCell3QZECFICwt1`, HOL ineq.hl:1425 `QZECFIC wt1`,
box [√2,√2]³×[2hminus,2hplus]×[2,2hminus]², `h0cut y4` single-kink
parametrisation).

Part 1 (this file's first wave): the explicit kernel + the eta/delta
duality + the `bank_QZECFICwt1_of_core` reduction scaffold — the
`NliBanks19` (wt2A) shape adapted to the wt1 slots `(h0cut y4, 1, 1)`
(no `/2` step; y4 box upper end `2 * hplus`; single kink at `2.52`).

Structural facts proved here (wt1-specific):
* `nb21_dlt_eq` / `nb21_dlt_perm` — the three slot deltas of the
  A/B/C slot vectors all coincide with the symmetric three-coordinate
  Delta `Delta = -2(X4^2+X5^2+X6^2)+4(X4X5+X4X6+X5X6)-X4X5X6`
  (X_i = y_i^2); this is the single Delta of the eta duality;
* `nb21_d4_eq` — the slot `deltaX4` factorisations
  `deltaX4(u1,2,u3,2,u5,2) = u1*(u3+u5-u1)` at the three permutations;
* `nb21_delta_mono_y5` / `nb21_delta_mono_y6` — KEY LEMMA A: the
  symmetric Delta is nonincreasing in `y5` (resp. `y6`) on the whole
  wt1 box, via the identity
  `Delta(x5) - Delta(x5') = (x5 - x5')*(16 - (x4-4)*(x6-4) - 2*(x5+x5'))`
  whose second factor is `<= 0` on the box (equality only on the
  degenerate edge `x5 = x5' = x6 = 4`, `x4` free);
* `nb21_h0cut_lfun_vanish` — the kink smoothing identity in the right
  direction: `h0cut y * lfun (y * 0.5) = 0` for `2 * h0 <= y`.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.NliBanks11
import Kepler.NliBanks13
import Kepler.NliBanks17
import Kepler.NliBanks20  -- K1/K2 constant brackets, matan Taylor kit

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks21
open Kepler.Text
open Kepler.NliBanks11
open Kepler.NliBanks12
open Kepler.NliBanks13
open Kepler.NliBanks19

/-! ## 1. The wt1 kernel -/

/-- Left-hand kernel of `QZECFIC wt1` at `y1 = y2 = y3 = √2` (slots
`m4 = h0cut y4`, `m5 = m6 = 1`). -/
noncomputable def w1aG (y4 y5 y6 : ℝ) : ℝ :=
  yOfX (gamma3fXDivSqrtdelta (h0cut y4) 1 1) (Real.sqrt 2) (Real.sqrt 2)
    (Real.sqrt 2) y4 y5 y6

/-- Right-hand kernel of `QZECFIC wt1` at `y1 = y2 = y3 = √2`. -/
noncomputable def w1aD (y4 y5 y6 : ℝ) : ℝ :=
  yOfX dih4XDivSqrtdeltaPosbranch (Real.sqrt 2) (Real.sqrt 2) (Real.sqrt 2) y4 y5 y6

/-- First-disjunct margin of `QZECFIC wt1` (no `/2`, unlike wt2A). -/
noncomputable def w1aF (y4 y5 y6 : ℝ) : ℝ :=
  w1aG y4 y5 y6 - (0.008 : ℝ) * w1aD y4 y5 y6

/-- Explicit form of the left kernel (coordinates nonnegative). -/
theorem nb21_w1aG_explicit (y4 y5 y6 : ℝ) (h4 : 0 ≤ y4) (h5 : 0 ≤ y5) (h6 : 0 ≤ y6) :
    w1aG y4 y5 y6 =
      1 / 12 - (2 * mm1 / Real.pi) *
        (solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
          solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 +
          solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2) +
        (8 * mm2 / Real.pi) *
          (lfun (y4 * 0.5) * h0cut y4 *
              dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 +
            lfun (y5 * 0.5) * 1 *
              dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
            lfun (y6 * 0.5) * 1 *
              dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2) := by
  have hs4 : Real.sqrt (y4 * y4) = y4 := Real.sqrt_mul_self h4
  have hs5 : Real.sqrt (y5 * y5) = y5 := Real.sqrt_mul_self h5
  have hs6 : Real.sqrt (y6 * y6) = y6 := Real.sqrt_mul_self h6
  simp only [w1aG, yOfX, nb19_g3_unfold]
  rw [hs4, hs5, hs6]

/-- Explicit form of the right kernel (coordinates nonnegative). -/
theorem nb21_w1aD_explicit (y4 y5 y6 : ℝ) :
    w1aD y4 y5 y6 =
      dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [w1aD, yOfX, nb19_dih4_pin]
  rw [hs2]

/-! ## 2. Slot-Delta symmetry and the KEY LEMMA A monotonicity -/

/-- The three-coordinate Delta in symmetric form (all three slot-vector
deltas of the wt1 family coincide with it). -/
theorem nb21_dlt_eq (y4 y5 y6 : ℝ) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 =
      -2 * ((y4 * y4) ^ 2 + (y5 * y5) ^ 2 + (y6 * y6) ^ 2) +
        4 * ((y4 * y4) * (y5 * y5) + (y4 * y4) * (y6 * y6) +
          (y5 * y5) * (y6 * y6)) -
        (y4 * y4) * (y5 * y5) * (y6 * y6) := by
  rw [deltaX]
  ring

/-- The A-slot delta `deltaX (y5^2) 2 (y4^2) 2 (y6^2) 2` equals the
symmetric Delta (same for the B-slot permutation). -/
theorem nb21_dlt_perm (y4 y5 y6 : ℝ) :
    deltaX (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 =
      deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 := by
  rw [deltaX, deltaX]
  ring

/-- The slot `deltaX4` factorisation `deltaX4(u1,2,u3,2,u5,2) = u1*(u3+u5-u1)`
at the three wt1 slot vectors (A: u1 = y5², B: u1 = y6², C: u1 = y4²). -/
theorem nb21_d4A_eq (y4 y5 y6 : ℝ) :
    deltaX4 (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 =
      (y5 * y5) * ((y4 * y4) + (y6 * y6) - (y5 * y5)) := by
  rw [deltaX4]
  ring

theorem nb21_d4B_eq (y4 y5 y6 : ℝ) :
    deltaX4 (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 =
      (y6 * y6) * ((y5 * y5) + (y4 * y4) - (y6 * y6)) := by
  rw [deltaX4]
  ring

theorem nb21_d4C_eq (y4 y5 y6 : ℝ) :
    deltaX4 (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 =
      (y4 * y4) * ((y6 * y6) + (y5 * y5) - (y4 * y4)) := by
  rw [deltaX4]
  ring

/-- **KEY LEMMA A (y5 direction)**: on the wt1 box, the symmetric Delta is
nonincreasing in `y5` (so the y5-walk down to `y5 = 2` never leaves the
region `{Delta ≥ 0}`).

The difference factors as
`(x5 - x5')*(16 - (x4-4)*(x6-4) - 2*(x5+x5'))` with `x4 ≥ 4`, `x6 ≥ 4`
(so `16 - (x4-4)*(x6-4) ≤ 16`) and `x5, x5' ≥ 4` (so the whole second
factor is `≤ 0`); equality only on the degenerate edge `x5 = x5' = x6 = 4`. -/
theorem nb21_delta_mono_y5 {y4 y5 y5' y6 : ℝ}
    (hy4 : 2 * hminus ≤ y4) (hy5 : 2 ≤ y5) (hy5' : 2 ≤ y5') (hy5le : y5' ≤ y5)
    (hy6 : 2 ≤ y6) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤
      deltaX (y4 * y4) 2 (y5' * y5') 2 (y6 * y6) 2 := by
  have hhm : (2.4635 : ℝ) ≤ 2 * hminus := Kepler.NliBanks17.nb17_two_hminus_bounds.1
  have hy4lo : (2.4635 : ℝ) ≤ y4 := le_trans hhm hy4
  have hx4 : (4 : ℝ) ≤ y4 * y4 := by nlinarith [hy4lo]
  have hx5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith [hy5]
  have hx5' : (4 : ℝ) ≤ y5' * y5' := by nlinarith [hy5']
  have hx6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  have hfac : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2
      - deltaX (y4 * y4) 2 (y5' * y5') 2 (y6 * y6) 2
      = ((y5 * y5) - (y5' * y5')) *
          (16 - ((y4 * y4) - 4) * ((y6 * y6) - 4)
            - 2 * ((y5 * y5) + (y5' * y5'))) := by
    rw [nb21_dlt_eq, nb21_dlt_eq]
    ring
  have hd : (0 : ℝ) ≤ (y5 * y5) - (y5' * y5') := by
    nlinarith [hy5le, hy5, hy5']
  have hs : 16 - ((y4 * y4) - 4) * ((y6 * y6) - 4)
      - 2 * ((y5 * y5) + (y5' * y5')) ≤ 0 := by
    have h1 : (0 : ℝ) ≤ ((y4 * y4) - 4) * ((y6 * y6) - 4) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith [hfac, hd, hs]

/-- **KEY LEMMA A (y6 direction)**: same monotonicity in `y6`. -/
theorem nb21_delta_mono_y6 {y4 y5 y6 y6' : ℝ}
    (hy4 : 2 * hminus ≤ y4) (hy6 : 2 ≤ y6) (hy6' : 2 ≤ y6') (hy6le : y6' ≤ y6)
    (hy5 : 2 ≤ y5) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≤
      deltaX (y4 * y4) 2 (y5 * y5) 2 (y6' * y6') 2 := by
  have hhm : (2.4635 : ℝ) ≤ 2 * hminus := Kepler.NliBanks17.nb17_two_hminus_bounds.1
  have hy4lo : (2.4635 : ℝ) ≤ y4 := le_trans hhm hy4
  have hx4 : (4 : ℝ) ≤ y4 * y4 := by nlinarith [hy4lo]
  have hx5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith [hy5]
  have hx6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  have hx6' : (4 : ℝ) ≤ y6' * y6' := by nlinarith [hy6']
  have hfac : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2
      - deltaX (y4 * y4) 2 (y5 * y5) 2 (y6' * y6') 2
      = ((y6 * y6) - (y6' * y6')) *
          (16 - ((y4 * y4) - 4) * ((y5 * y5) - 4)
            - 2 * ((y6 * y6) + (y6' * y6'))) := by
    rw [nb21_dlt_eq, nb21_dlt_eq]
    ring
  have hd : (0 : ℝ) ≤ (y6 * y6) - (y6' * y6') := by
    nlinarith [hy6le, hy6, hy6']
  have hs : 16 - ((y4 * y4) - 4) * ((y5 * y5) - 4)
      - 2 * ((y6 * y6) + (y6' * y6')) ≤ 0 := by
    have h1 : (0 : ℝ) ≤ ((y4 * y4) - 4) * ((y5 * y5) - 4) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  nlinarith [hfac, hd, hs]

/-- **KEY LEMMA A (y4 direction)**: on the wt1 box, the symmetric Delta is
nonincreasing in `y4` as well.  The y4-partial factors as
`2*y4*(4*x5 + 4*x6 - 4*x4 - x5*x6)` and
`4*x5 + 4*x6 - x5*x6 = 16 - (x5-4)*(x6-4) <= 16 <= 4*x4`
(since `x5, x6 >= 4` and `x4 >= 6.06...`), so the partial is strictly
negative on the box.  The difference factors as
`(x4 - x4')*(16 - (x5-4)*(x6-4) - 4*x4 - ... )` — here expressed via
`Delta(x4) - Delta(x4') = (x4 - x4') * f` with
`f = -2*(x4+x4') + 4*x5 + 4*x6 - x5*x6 <= 0`. -/
theorem nb21_delta_mono_y4 {y4 y4' y5 y6 : ℝ}
    (hy4 : 2 * hminus ≤ y4) (hy4' : 2 * hminus ≤ y4') (hy4le : y4 ≤ y4')
    (hy5 : 2 ≤ y5) (hy6 : 2 ≤ y6) :
    deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 ≥
      deltaX (y4' * y4') 2 (y5 * y5) 2 (y6 * y6) 2 := by
  have hhm : (2.4635 : ℝ) ≤ 2 * hminus := Kepler.NliBanks17.nb17_two_hminus_bounds.1
  have hy4lo : (2.4635 : ℝ) ≤ y4 := le_trans hhm hy4
  have hy4'lo : (2.4635 : ℝ) ≤ y4' := le_trans hhm hy4'
  have hx5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith [hy5]
  have hx6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  have hfac : deltaX (y4' * y4') 2 (y5 * y5) 2 (y6 * y6) 2
      - deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2
      = ((y4' * y4') - (y4 * y4)) *
          (4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)
            - 2 * ((y4' * y4') + (y4 * y4))) := by
    rw [nb21_dlt_eq, nb21_dlt_eq]
    ring
  have hd : (0 : ℝ) ≤ (y4' * y4') - (y4 * y4) := by
    nlinarith [hy4le, hy4lo, hy4'lo]
  have hs : 4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)
      - 2 * ((y4' * y4') + (y4 * y4)) ≤ 0 := by
    have h1 : (0 : ℝ) ≤ ((y5 * y5) - 4) * ((y6 * y6) - 4) :=
      mul_nonneg (by linarith) (by linarith)
    have hx4 : (6.06 : ℝ) ≤ y4 * y4 := by nlinarith [hy4lo]
    have hx4' : (6.06 : ℝ) ≤ y4' * y4' := by nlinarith [hy4'lo]
    have hid : 4 * (y5 * y5) + 4 * (y6 * y6) - (y5 * y5) * (y6 * y6)
        = 16 - ((y5 * y5) - 4) * ((y6 * y6) - 4) := by ring
    rw [hid]
    linarith [h1, hx4, hx4']
  nlinarith [hfac, hd, hs]

/-! ## 3. The `eta`/`delta` duality on the wt1 box -/

/-- `upsX` at three squares (nb19 re-statement, local name for clarity). -/
theorem nb21_ups_eq (a b c : ℝ) :
    upsX (a * a) (b * b) (c * c) = 4 * (b * b) * (c * c) - (a * a - b * b - c * c) ^ 2 := by
  rw [upsX]
  ring

/-- `upsX > 0` on the wt1 box `y4 ∈ [2hminus, 2hplus]`, `y5, y6 ∈ [2, 2hminus]`:
`4 x5 x6 ≥ 64` while `(x4 - x5 - x6)^2 ≤ 6.07^2 < 37`. -/
theorem nb21_wt1_ups_pos {y4 y5 y6 : ℝ} (hy4 : 2 * hminus ≤ y4) (hy4' : y4 ≤ 2 * hplus)
    (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * hminus) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * hminus) :
    0 < upsX (y4 * y4) (y5 * y5) (y6 * y6) := by
  have hhm : (2.4635 : ℝ) ≤ 2 * hminus ∧ 2 * hminus ≤ 2.46352 :=
    Kepler.NliBanks17.nb17_two_hminus_bounds
  have hy4lo : (2.4635 : ℝ) ≤ y4 := le_trans hhm.1 hy4
  have hy4hi : y4 ≤ (2.6508 : ℝ) := by
    have h2hp : 2 * hplus = (2.6508 : ℝ) := by norm_num [hplus]
    rw [h2hp] at hy4'
    exact hy4'
  have hy5hi : y5 ≤ (2.46352 : ℝ) := le_trans hy5' hhm.2
  have hy6hi : y6 ≤ (2.46352 : ℝ) := le_trans hy6' hhm.2
  have hx5lo : (4 : ℝ) ≤ y5 * y5 := by nlinarith [hy5]
  have hx6lo : (4 : ℝ) ≤ y6 * y6 := by nlinarith [hy6]
  rw [nb21_ups_eq]
  have hprod : (64 : ℝ) ≤ 4 * (y5 * y5) * (y6 * y6) := by nlinarith [hx5lo, hx6lo]
  have hdiff : -(6.1 : ℝ) ≤ y4 * y4 - y5 * y5 - y6 * y6 ∧
      y4 * y4 - y5 * y5 - y6 * y6 ≤ -(0.9 : ℝ) := by
    constructor
    · have hx4lo : (6.068 : ℝ) ≤ y4 * y4 := by nlinarith [hy4lo]
      have hx5hi : y5 * y5 ≤ (6.07 : ℝ) := by nlinarith [hy5hi]
      have hx6hi : y6 * y6 ≤ (6.07 : ℝ) := by nlinarith [hy6hi]
      linarith
    · have hx4hi : y4 * y4 ≤ (7.03 : ℝ) := by nlinarith [hy4hi]
      have hx5lo' : (4 : ℝ) ≤ y5 * y5 := hx5lo
      have hx6lo' : (4 : ℝ) ≤ y6 * y6 := hx6lo
      linarith
  have hsqle : (y4 * y4 - y5 * y5 - y6 * y6) ^ 2 ≤ (37.3 : ℝ) := by
    have habs : |y4 * y4 - y5 * y5 - y6 * y6| ≤ (6.1 : ℝ) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |y4 * y4 - y5 * y5 - y6 * y6| * |y4 * y4 - y5 * y5 - y6 * y6|
        ≤ (6.1 : ℝ) * (6.1 : ℝ) := mul_self_le_mul_self (abs_nonneg _) habs
    have h3 : (y4 * y4 - y5 * y5 - y6 * y6) ^ 2
        = |y4 * y4 - y5 * y5 - y6 * y6| * |y4 * y4 - y5 * y5 - y6 * y6| := by
      rw [sq, ← abs_mul_abs_self]
    have h4 : (6.1 : ℝ) * 6.1 ≤ (37.3 : ℝ) := by norm_num
    linarith
  linarith

/-- **Right disjunct of `QZECFIC wt1`**: on the wt1 box, negative
three-coordinate Delta forces `eta_y ^ 2 > 2`. -/
theorem nb21_wt1_eta_dlt_neg {y4 y5 y6 : ℝ} (hy4 : 2 * hminus ≤ y4) (hy4' : y4 ≤ 2 * hplus)
    (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * hminus) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * hminus)
    (hd : deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 < 0) :
    eta_y y4 y5 y6 ^ 2 > 2 := by
  have hups := nb21_wt1_ups_pos hy4 hy4' hy5 hy5' hy6 hy6'
  have htri := nb19_dlt_eq y4 y5 y6
  have hhm : (2.4635 : ℝ) ≤ 2 * hminus := Kepler.NliBanks17.nb17_two_hminus_bounds.1
  have hy4pos : (0 : ℝ) ≤ y4 := by linarith
  have hy5pos : (0 : ℝ) ≤ y5 := by linarith [hy5]
  have hy6pos : (0 : ℝ) ≤ y6 := by linarith [hy6]
  have hP : (0 : ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6) :=
    mul_nonneg (mul_nonneg (mul_nonneg hy4pos hy4pos)
      (mul_nonneg hy5pos hy5pos)) (mul_nonneg hy6pos hy6pos)
  have hrel : 2 * upsX (y4 * y4) (y5 * y5) (y6 * y6)
      < y4 * y4 * (y5 * y5) * (y6 * y6) := by linarith
  have hquo : (0 : ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6)
      / upsX (y4 * y4) (y5 * y5) (y6 * y6) := div_nonneg hP hups.le
  have hrw : eta_y y4 y5 y6 ^ 2
      = y4 * y4 * (y5 * y5) * (y6 * y6)
        / upsX (y4 * y4) (y5 * y5) (y6 * y6) := by
    simp only [eta_y, etaY, etaX, pow_two, Real.mul_self_sqrt hquo]
  rw [hrw, gt_iff_lt, lt_div_iff₀ hups]
  exact hrel

/-- **Converse**: on the wt1 box, `eta_y ^ 2 ≤ 2` forces the symmetric Delta
to be nonnegative. -/
theorem nb21_wt1_delta_ge {y4 y5 y6 : ℝ} (hy4 : 2 * hminus ≤ y4) (hy4' : y4 ≤ 2 * hplus)
    (hy5 : 2 ≤ y5) (hy5' : y5 ≤ 2 * hminus) (hy6 : 2 ≤ y6) (hy6' : y6 ≤ 2 * hminus)
    (he : eta_y y4 y5 y6 ^ 2 ≤ 2) :
    0 ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 := by
  have hups := nb21_wt1_ups_pos hy4 hy4' hy5 hy5' hy6 hy6'
  have htri := nb19_dlt_eq y4 y5 y6
  have hhm : (2.4635 : ℝ) ≤ 2 * hminus := Kepler.NliBanks17.nb17_two_hminus_bounds.1
  have hy4pos : (0 : ℝ) ≤ y4 := by linarith
  have hy5pos : (0 : ℝ) ≤ y5 := by linarith [hy5]
  have hy6pos : (0 : ℝ) ≤ y6 := by linarith [hy6]
  have hP : (0 : ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6) :=
    mul_nonneg (mul_nonneg (mul_nonneg hy4pos hy4pos)
      (mul_nonneg hy5pos hy5pos)) (mul_nonneg hy6pos hy6pos)
  have hquo : (0 : ℝ) ≤ y4 * y4 * (y5 * y5) * (y6 * y6)
      / upsX (y4 * y4) (y5 * y5) (y6 * y6) := div_nonneg hP hups.le
  have hrw : eta_y y4 y5 y6 ^ 2
      = y4 * y4 * (y5 * y5) * (y6 * y6)
        / upsX (y4 * y4) (y5 * y5) (y6 * y6) := by
    simp only [eta_y, etaY, etaX, pow_two, Real.mul_self_sqrt hquo]
  rw [hrw] at he
  have h2u : y4 * y4 * (y5 * y5) * (y6 * y6)
      ≤ 2 * upsX (y4 * y4) (y5 * y5) (y6 * y6) := (div_le_iff₀ hups).mp he
  linarith

/-! ## 4. Kink pins -/

/-- The kink smoothing identity, right-branch form: for `y ≥ 2 * h0` the
product `h0cut y * lfun (y * 0.5)` vanishes (either `h0cut y = 0`, or
`y = 2 * h0` where `lfun (h0) = 0`). -/
theorem nb21_h0cut_lfun_vanish {y : ℝ} (hy : 2 * h0 ≤ y) :
    h0cut y * lfun (y * 0.5) = 0 := by
  by_cases hyk : y ≤ 2 * h0
  · have hye : y = 2 * h0 := le_antisymm hyk hy
    rw [nb19_h0cut_eq_one hyk]
    have h0v : h0 = (1.26 : ℝ) := rfl
    have hyh : y * 0.5 = h0 := by rw [hye, h0v]; norm_num
    have hl : lfun (y * 0.5) = 0 := by
      rw [hyh]
      unfold lfun
      rw [h0v]
      norm_num
    rw [hl, mul_zero]
  · rw [nb19_h0cut_eq_zero (lt_of_not_ge hyk), zero_mul]

/-! ## 5. Bank reduction scaffold -/

/-- `QZECFIC wt1` follows from the core margin inequality on the closed
Delta region.  Residual obligation (the analytic certificate):
`∀ y4 y5 y6` in the box with `deltaX (y4²) 2 (y5²) 2 (y6²) 2 ≥ 0`,
`0 < w1aF y4 y5 y6`. -/
theorem bank_QZECFICwt1_of_core
    (hcore : ∀ y4 y5 y6 : ℝ, 2 * hminus ≤ y4 → y4 ≤ 2 * hplus →
      2 ≤ y5 → y5 ≤ 2 * hminus → 2 ≤ y6 → y6 ≤ 2 * hminus →
      0 ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 →
      0 < w1aF y4 y5 y6) :
    bank_QZECFICwt1 := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hy1 : y1 = Real.sqrt 2 := le_antisymm h1' h1
  have hy2 : y2 = Real.sqrt 2 := le_antisymm h2' h2
  have hy3 : y3 = Real.sqrt 2 := le_antisymm h3' h3
  by_cases heta : (2 : ℝ) < eta_y y4 y5 y6 ^ 2
  · exact Or.inr heta
  · left
    have hd : 0 ≤ deltaX (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 :=
      nb21_wt1_delta_ge h4 h4' h5 h5' h6 h6' (le_of_not_gt heta)
    have hF := hcore y4 y5 y6 h4 h4' h5 h5' h6 h6' hd
    rw [hy1, hy2, hy3, ← w1aG, ← w1aD]
    unfold w1aF at hF
    linarith

/-! ## 6. Axiom audit -/

#print axioms nb21_w1aG_explicit
#print axioms nb21_w1aD_explicit
#print axioms nb21_dlt_eq
#print axioms nb21_dlt_perm
#print axioms nb21_d4A_eq
#print axioms nb21_d4B_eq
#print axioms nb21_d4C_eq
#print axioms nb21_delta_mono_y5
#print axioms nb21_delta_mono_y6
#print axioms nb21_delta_mono_y4
#print axioms nb21_wt1_ups_pos
#print axioms nb21_wt1_eta_dlt_neg
#print axioms nb21_wt1_delta_ge
#print axioms nb21_h0cut_lfun_vanish
#print axioms bank_QZECFICwt1_of_core

end Kepler.NliBanks21
