/-
Lane `wt1-dcbl-probe-w1` — **the dSqrt repair**: `Nat.sqrt` does not reduce in the
kernel, so no `decide` can ever see a `dSqrt` node.  Repair: never evaluate
`Nat.sqrt`; instead prove the two bracketing inequalities on `Nat` (plain
multiplication/comparison — kernel-reducible) and transport them through
`Nat.sqrt_le` / `Nat.lt_succ_sqrt`.

This file
  1. proves `nat_sqrt_eq_of_sq` (core-only, no Mathlib sqrt lemmas needed),
  2. defines the generic literal-square-root bridge `dSqrt_val`,
  3. applies it to a *real* node of the box (`dSqrt (dInv C4)`, k = 203,
     460-bit mantissas) and prints the axioms.
-/
import Kepler.Text.TaylorSecond.DCJet
import Kepler.Text.TaylorSecond.DCMatan

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000000

namespace Kepler.Text.TaylorSecond.DCSqrtLit

open Kepler.Text.TaylorSecond
open Kepler.Text.TaylorSecond.DCKit
open Kepler.Text.TaylorSecond.DCMatan

/-- **Uniqueness of `Nat.sqrt`**: the two bracketing inequalities force the value.
Core-only proof (`Nat.sqrt_le`, `Nat.lt_succ_sqrt`). -/
theorem nat_sqrt_eq_of_sq {n r : ℕ} (h1 : r * r ≤ n) (h2 : n < (r + 1) * (r + 1)) :
    Nat.sqrt n = r := by
  have hs1 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hs2 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have hle : Nat.sqrt n ≤ r := by
    by_contra h
    have h3 : r + 1 ≤ Nat.sqrt n := by omega
    have h4 : (r + 1) * (r + 1) ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul h3 h3
    omega
  have hge : r ≤ Nat.sqrt n := by
    by_contra h
    have h3 : Nat.sqrt n + 1 ≤ r := by omega
    have h4 : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ r * r := Nat.mul_le_mul h3 h3
    omega
  omega

#print axioms nat_sqrt_eq_of_sq

/-- **Literal square-root node.**  `K` is the output scale, `rlo`/`rhi` the two
mantissas; `nlo`/`nhi` the shifted mantissa inputs.  The four `Nat`/`ℤ`
side conditions are all closed by `decide` on literals. -/
theorem dSqrt_val {A : DC} {K rlo rhi : ℤ} {nlo nhi : ℕ}
    (hK : ((dClamp0 A).k + 201) / 2 = K)
    (hnlo : ((dClamp0 A).lo <<< (2 * K - (dClamp0 A).k).toNat).toNat = nlo)
    (hnhi : ((dClamp0 A).hi <<< (2 * K - (dClamp0 A).k).toNat).toNat = nhi)
    (hslo : Nat.sqrt nlo = rlo.toNat)
    (hshi : Nat.sqrt nhi = rhi.toNat)
    (hlo0 : 0 ≤ rlo) (hhi0 : 0 ≤ rhi) :
    dSqrt A = ⟨K, rlo, rhi + 1⟩ := by
  simp only [dSqrt, dSqrtCore, hK, hnlo, hnhi, hslo, hshi,
    Int.toNat_of_nonneg hlo0, Int.toNat_of_nonneg hhi0]

#print axioms dSqrt_val

/-! ## Apply it to a real box node: `dSqrt (dInv C4)` -/

/-- The value of `dInv C4` (compiled oracle, `Oracle2.lean`). -/
def C4 : DC := ⟨(194 : ℤ), (1575846670872766501956900779399903633256675471824533964885623 : ℤ), (1575846826673697034109489874084340603307556129352113753715292 : ℤ)⟩

/-- `dSqrt (dInv C4)` as a literal — proven, **not** evaluated by `decide`. -/
theorem dSqrt_inv_C4 :
    dSqrt (dInv C4) =
      ⟨(203 : ℤ), (1622712936537934665114260821269012797807137805202312181474461 : ℤ),
        (1622713016755186737674444072264332677426939287783435992603850 : ℤ)⟩ := by
  refine dSqrt_val (A := dInv C4) (K := 203)
    (rlo := 1622712936537934665114260821269012797807137805202312181474461)
    (rhi := 1622713016755186737674444072264332677426939287783435992603849)
    (nlo := 2633197274407567175896851609434013944139387983088140255024926799031124045628415278691244635750584105579664848535186046976)
    (nhi := 2633197534746718954040102942014124062329109541565446820801692304473666925941122290736056257804623635011959497115171815424)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · exact nat_sqrt_eq_of_sq (by decide) (by decide)
  · decide
  · decide

#print axioms dSqrt_inv_C4

end Kepler.Text.TaylorSecond.DCSqrtLit
