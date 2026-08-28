/-
  Phase 4, step 2: kernel-checkable **square roots** of dyadic intervals.

  `√` is not dyadic-exact, and — crucially for this project — Lean's
  `Int.sqrt`/`Nat.sqrt` are `Nat.sqrt.iter`-based and **do not kernel-reduce**
  under `decide`.  We therefore use the *certificate* pattern (as in
  `Kepler.LP.Cert`): the caller supplies the root mantissa `s`, and the kernel
  only *verifies* the two integer inequalities

  ```
  s * s ≤ d.m * 2^(d.e % 2)   and   d.m * 2^(d.e % 2) < (s + 1) * (s + 1)
  ```

  (big-integer arithmetic, kernel/GMP-friendly), from which soundness over `ℝ`
  follows.  Writing `k = d.e / 2` (floor) and `r = d.e % 2 ∈ {0, 1}` we have
  `d.toReal = (d.m * 2^r) * 2^(2k)` and therefore

  ```
  Real.sqrt d.toReal = 2^k * √(d.m * 2^r) ∈ [s * 2^k, (s+1) * 2^k],
  ```

  the returned interval.  Tightness is controlled by scaling the mantissa: for
  `√2` at ~1e-5 relative precision use `d = ⟨2^49, 0⟩` (see `sqrt2_bounds`).

  `sqrtI` fails (`none`) on negative radicands or a bad certificate.

  Checking layer: `Int` only. Semantic layer: `Real.sqrt`, `toReal` bridge.
  No `sorry`, no `native_decide`, no new axioms.

  ## Pilots (kernel `decide` only)

  `sqrt2_cert` verifies `⌊2^24·√2⌋ = 23726566` by kernel `decide`
  (i.e. `23726566² ≤ 2^49 < 23726567²`), and `sqrt2_bounds` turns it into the
  real statement `1.4142 ≤ √2 ≤ 1.4143`.
-/
import Kepler.Interval.Basic

namespace Kepler.Interval

/-! ## Scaling law for `Real.sqrt` -/

/-- `√(n · 2^(2t)) = 2^t · √n` — the range-reduction identity used by
`sqrtI` (`d.m * 2^r * 2^(2k)`) and by the `√2` pilot. -/
theorem sqrt_scale_pow {n : ℝ} (hn : 0 ≤ n) (t : ℤ) :
    Real.sqrt (n * (2:ℝ)^(2*t)) = (2:ℝ)^t * Real.sqrt n := by
  have hz : (2:ℝ)^(2*t) = ((2:ℝ)^t)^2 := by
    have h1 := zpow_add₀ (by norm_num : (2:ℝ) ≠ 0) t t
    rw [← two_mul t] at h1
    rw [h1, pow_two]
  have hznn : (0:ℝ) ≤ (2:ℝ)^t := zpow_nonneg (by norm_num) t
  rw [hz, Real.sqrt_mul hn, pow_two, Real.sqrt_mul_self hznn, mul_comm]

/-! ## Certificate-based dyadic square root -/

namespace Dyadic

/-- Square root by certificate: `sqrtI d s = some ⟨⟨s, d.e / 2⟩, ⟨s+1, d.e / 2⟩⟩`
iff `s ≥ 0`, `d.m ≥ 0`, and `s² ≤ d.m * 2^(d.e % 2) < (s+1)²`.  The kernel
checks only these integer inequalities (`decide`); the *generator* computes
`s` off-kernel (e.g. `Nat.sqrt` at certificate-production time). -/
def sqrtI (d : Dyadic) (s : Int) : Option DInterval :=
  if _h : 0 ≤ s ∧ 0 ≤ d.m ∧ s * s ≤ d.m * 2 ^ (d.e % 2).toNat
      ∧ d.m * 2 ^ (d.e % 2).toNat < (s + 1) * (s + 1) then
    some ⟨⟨s, d.e / 2⟩, ⟨s + 1, d.e / 2⟩⟩
  else none

/-- **Soundness of `sqrtI`** (over `ℝ`): the returned interval contains the
real square root of the radicand's semantics. -/
theorem sqrtI_sound {d : Dyadic} {s : Int} {I : DInterval}
    (h : d.sqrtI s = some I) :
    I.lo.toReal ≤ Real.sqrt d.toReal ∧ Real.sqrt d.toReal ≤ I.hi.toReal := by
  unfold sqrtI at h
  split at h
  · next hs =>
    obtain ⟨hs0, hm0, hslo, hshi⟩ := hs
    obtain rfl : I = ⟨⟨s, d.e / 2⟩, ⟨s + 1, d.e / 2⟩⟩ := (Option.some.inj h).symm
    -- radicand and bounds, all over ℝ
    have hn0 : (0:ℝ) ≤ ((d.m * 2 ^ (d.e % 2).toNat : ℤ) : ℝ) := by
      have hp : (0:ℤ) ≤ 2 ^ (d.e % 2).toNat := by positivity
      exact_mod_cast Int.mul_nonneg hm0 hp
    have hslo' : ((s : ℤ):ℝ) ^ 2 ≤ ((d.m * 2 ^ (d.e % 2).toNat : ℤ):ℝ) := by
      rw [sq]
      exact_mod_cast hslo
    have hshi' : ((d.m * 2 ^ (d.e % 2).toNat : ℤ):ℝ)
        < (((s:ℤ) + 1):ℝ) ^ 2 := by
      rw [sq]
      push_cast
      exact_mod_cast hshi
    -- s ≤ √n < s+1 (n = d.m * 2^(d.e % 2))
    have hsSqrt : ((s : ℤ):ℝ) ≤ Real.sqrt ((d.m * 2 ^ (d.e % 2).toNat : ℤ):ℝ) := by
      have hsq := Real.sqrt_sq (by exact_mod_cast hs0 : (0:ℝ) ≤ ((s:ℤ):ℝ))
      rw [← hsq]
      exact Real.sqrt_le_sqrt hslo'
    have hSqrtS : Real.sqrt ((d.m * 2 ^ (d.e % 2).toNat : ℤ):ℝ)
        < (((s:ℤ) + 1):ℝ) := by
      have hlt := Real.sqrt_lt_sqrt hn0 hshi'
      rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ (((s:ℤ):ℝ) + 1))] at hlt
    -- radicand semantics: d.toReal = n * 2^(2 * (d.e / 2))
    have hsplit : 2 * (d.e / 2) + d.e % 2 = d.e := Int.mul_ediv_add_emod d.e 2
    have hdval : d.toReal = ((d.m * 2 ^ (d.e % 2).toNat : ℤ) : ℝ)
        * (2:ℝ)^(2 * (d.e / 2)) := by
      have hp : (2:ℝ)^d.e = (2:ℝ)^(2 * (d.e / 2)) * (2:ℝ)^(d.e % 2) := by
        conv_lhs => rw [← hsplit]
        exact zpow_add₀ (by norm_num : (2:ℝ) ≠ 0) _ _
      have hrnn : (((d.e % 2).toNat : ℤ)) = d.e % 2 :=
        Int.toNat_of_nonneg (Int.emod_nonneg _ two_ne_zero)
      rw [toReal_def, hp]
      push_cast
      rw [← zpow_natCast, hrnn]
      ring
    -- assemble
    constructor
    · show Dyadic.toReal ⟨s, d.e / 2⟩ ≤ Real.sqrt d.toReal
      rw [hdval, toReal_def, sqrt_scale_pow hn0 (d.e / 2)]
      exact le_trans
        (mul_le_mul_of_nonneg_right hsSqrt (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (d.e / 2)))
        (le_of_eq (by dsimp only; push_cast; ring))
    · show Real.sqrt d.toReal ≤ Dyadic.toReal ⟨s + 1, d.e / 2⟩
      rw [hdval, toReal_def, sqrt_scale_pow hn0 (d.e / 2)]
      exact le_trans
        (mul_le_mul_of_nonneg_left (le_of_lt hSqrtS)
          (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (d.e / 2)))
        (le_of_eq (by dsimp only; push_cast; ring))
  · exact absurd h (by simp)

/-- Interface for branch-and-bound: if `x ≥ 0` and `x²` is in the radicand's
semantics, then `x` is in the certified interval. -/
theorem sqrtI_mem {d : Dyadic} {s : Int} {I : DInterval} {x : ℝ}
    (h : d.sqrtI s = some I) (hx : 0 ≤ x) (hsq : d.toReal = x * x) :
    I.mem x := by
  obtain ⟨h1, h2⟩ := sqrtI_sound h
  have hxsq : Real.sqrt d.toReal = x := by
    rw [hsq, Real.sqrt_mul_self hx]
  rw [hxsq] at h1 h2
  exact ⟨h1, h2⟩

/-- Case analysis on a successful `sqrtI`: the kernel-checked conjunction
yields `0 ≤ s`, `0 ≤ d.m` (nonnegative radicand) and the two bracketing
inequalities (mirrors `Dyadic.divFloorQ_cases` in `Div.lean`). -/
theorem sqrtI_cases {d : Dyadic} {s : Int} {I : DInterval}
    (h : d.sqrtI s = some I) :
    0 ≤ s ∧ 0 ≤ d.m ∧ s * s ≤ d.m * 2 ^ (d.e % 2).toNat
      ∧ d.m * 2 ^ (d.e % 2).toNat < (s + 1) * (s + 1) := by
  unfold sqrtI at h
  split at h
  · next hs => exact hs
  · exact absurd h (by simp)

/-- A successful `sqrtI` certificate implies a nonnegative radicand (used by
the `.sqrt` node of `Kepler.Interval.Expr.IExpr`). -/
theorem sqrtI_nonneg {d : Dyadic} {s : Int} {I : DInterval}
    (h : d.sqrtI s = some I) : 0 ≤ d.toReal := by
  obtain ⟨_, hm, _, _⟩ := sqrtI_cases h
  rw [toReal_def]
  exact mul_nonneg (by exact_mod_cast hm) (zpow_nonneg (by norm_num) d.e)

end Dyadic

/-! ## Pilot: `√2 ∈ [1.4142, 1.4143]` (kernel `decide` only) -/

/-- The certificate: `⌊√(2^49)⌋ = 23726566`, verified by the kernel (two
big-integer comparisons; no `Int.sqrt` reduction involved). -/
theorem sqrt2_cert :
    Dyadic.sqrtI ⟨562949953421312, 0⟩ 23726566
      = some ⟨⟨23726566, 0⟩, ⟨23726567, 0⟩⟩ := by
  decide

/-- End-to-end real statement: `1.4142 ≤ √2 ≤ 1.4143`. -/
theorem sqrt2_bounds : (14142:ℝ)/10000 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (14143:ℝ)/10000 := by
  obtain ⟨h1, h2⟩ := Dyadic.sqrtI_sound sqrt2_cert
  -- semantics of the certificate's interval
  have hlo : Dyadic.toReal ⟨23726566, 0⟩ = (23726566:ℝ) := Dyadic.toReal_int _
  have hhi : Dyadic.toReal ⟨23726567, 0⟩ = (23726567:ℝ) := Dyadic.toReal_int _
  have hd : Dyadic.toReal ⟨562949953421312, 0⟩ = (2:ℝ)^49 := by
    rw [Dyadic.toReal_int]
    norm_num
  dsimp only at h1 h2
  rw [hlo, hd] at h1
  rw [hhi, hd] at h2
  -- range reduction: √(2^49) = 2^24 * √2
  have hscale : Real.sqrt ((2:ℝ)^49) = (16777216:ℝ) * Real.sqrt 2 := by
    have hE : ((2:ℝ)^49) = 2 * ((16777216:ℝ) * 16777216) := by norm_num
    rw [hE, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
      Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 16777216)]
    ring
  rw [hscale] at h1 h2
  constructor
  · calc (14142:ℝ)/10000 ≤ 23726566/16777216 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 16777216), div_mul_eq_mul_div,
            div_le_iff₀ (by norm_num : (0:ℝ) < 10000)]
          norm_num
    _ ≤ Real.sqrt 2 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16777216)]
        linarith [h1]
  · calc Real.sqrt 2 ≤ 23726567/16777216 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 16777216)]
          linarith [h2]
    _ ≤ 14143/10000 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16777216), div_mul_eq_mul_div,
          le_div_iff₀ (by norm_num : (0:ℝ) < 10000)]
        norm_num

end Kepler.Interval
