/-
Kepler.Text.TaylorSecond.Pq1KinkZero — lane `wt1-leafterm-w1` (2026-11-25).

`pq1` vanishes **identically** on the closed half-line `y4 ≥ 2*h0` (the HOL
`h0cut` kink), for any value of the `DIHCDD` factor:

* `h0 = 1.26` (`PackingAuto2.h0`), `lfun h = (h0 - h) / (h0 - 1)`
  (`PackingAuto2.lfun`), `h0cut x = if x ≤ 2*h0 then 1 else 0`
  (`PackingAuto21.h0cut`);
* at `y4 = 2*h0`: `lfun (y4/2) = lfun h0 = 0`;
* at `y4 > 2*h0`: `h0cut y4 = 0`.

So `pq1 = lfun (y4/2) * h0cut y4 * d = 0` — not an interval `[0,1]` bound.

Why this is the right closure for the 10 "kink boundary" boxes (9 leaves,
`y4lo = 63/25` exactly): `leafcore.h0cut_range` gives `h0cutI = {0}` there
(sound for `pq1`, since `pq1 ≡ 0`), but the landed per-box lemma
`h0cutI_mem : h0cut y4 ∈ {0}` is *false at the single point* `y4 = 2*h0`
(there `h0cut = 1`), so that proof can never close.  The interval side is
fine: `QInterval.mul (QInterval.mul I ⟨0,0⟩) J = ⟨0,0⟩` for every `I`, `J`
(`gtree_pq1`'s exact shape), so the generated `pq1_mem` is discharged directly
by `pq1_interval_mem_zero` plus `pq1_eq_zero_of_kink`, and it never mentions
`h0cutI_mem`.

Every lemma is closed; the axiom audit is at the tail.
-/
import Kepler.Text.TaylorSecond.LeafGenKit

set_option maxHeartbeats 8000000

namespace Kepler.Text.TaylorSecond

open Kepler.Text

-- >>> PQ1KINKZERO-INLINE-BEGIN
/-- `lfun` vanishes at the kink `h0`. -/
theorem pq1kz_lfun_h0_eq_zero : lfun h0 = 0 := by
  unfold lfun
  ring

/-- Above the kink the indicator is `0`. -/
theorem pq1kz_h0cut_eq_zero_of_gt {x : ℝ} (h : 2 * h0 < x) : h0cut x = 0 := by
  unfold h0cut
  rw [if_neg (not_le.mpr h)]

/-- `pq1` vanishes identically on `y4 ≥ 2*h0` (kink point included), for an
arbitrary `DIHCDD` value `d`. -/
theorem pq1kz_pq1_eq_zero {y4 d : ℝ} (hy : 2 * h0 ≤ y4) :
    lfun (y4 / 2) * h0cut y4 * d = 0 := by
  rcases eq_or_lt_of_le hy with heq | hgt
  · have hhalf : y4 / 2 = h0 := by rw [← heq]; ring
    rw [hhalf, pq1kz_lfun_h0_eq_zero]
    ring
  · rw [pq1kz_h0cut_eq_zero_of_gt hgt]
    ring

/-- The same in the slot's own spelling (`y4 * 0.5`), which is the shape the
generated `pq1` value has. -/
theorem pq1kz_pq1_eq_zero_mul_half {y4 d : ℝ} (hy : 2 * h0 ≤ y4) :
    lfun (y4 * 0.5) * h0cut y4 * d = 0 := by
  have h : y4 * 0.5 = y4 / 2 := by ring
  rw [h]
  exact pq1kz_pq1_eq_zero hy

/-- Interval product with the point interval `{0}` on the right. -/
theorem pq1kz_mul_right_zero (I : QInterval) :
    QInterval.mul I ⟨0, 0⟩ = ⟨0, 0⟩ := by
  cases I with
  | mk lo hi => simp [QInterval.mul, mul_zero, min_self]

/-- Interval product with the point interval `{0}` on the left. -/
theorem pq1kz_mul_left_zero (J : QInterval) :
    QInterval.mul ⟨0, 0⟩ J = ⟨0, 0⟩ := by
  cases J with
  | mk lo hi => simp [QInterval.mul, zero_mul, min_self]

/-- `gtree_pq1`'s exact shape with the middle factor `{0}` is the point
interval `{0}`. -/
theorem pq1kz_interval_eq_zero (I J : QInterval) :
    QInterval.mul (QInterval.mul I ⟨0, 0⟩) J = ⟨0, 0⟩ := by
  rw [pq1kz_mul_right_zero, pq1kz_mul_left_zero]

/-- … and that interval contains `0`. -/
theorem pq1kz_interval_mem_zero (I J : QInterval) :
    (QInterval.mul (QInterval.mul I ⟨0, 0⟩) J).mem 0 := by
  rw [pq1kz_interval_eq_zero]
  norm_num [QInterval.mem]
-- <<< PQ1KINKZERO-INLINE-END

/-! ## Audit -/

#print axioms pq1kz_lfun_h0_eq_zero
#print axioms pq1kz_h0cut_eq_zero_of_gt
#print axioms pq1kz_pq1_eq_zero
#print axioms pq1kz_pq1_eq_zero_mul_half
#print axioms pq1kz_mul_right_zero
#print axioms pq1kz_mul_left_zero
#print axioms pq1kz_interval_eq_zero
#print axioms pq1kz_interval_mem_zero

end Kepler.Text.TaylorSecond
