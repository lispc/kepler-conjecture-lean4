/-
  Phase 4, step 1: kernel-checkable **division / reciprocal** for dyadic intervals.

  Extends `Kepler.Interval.Basic` (exact `+ - × Neg` on `Dyadic = m · 2^e`) with
  the first non-exact operation, following the interface notes in the header of
  `Basic.lean` ("Division/reciprocal"):

  - `Dyadic.divFloorQ a b out`: the **floor of `a / b` at output granularity
    `2^out`**: `some q` with `q.toReal ≤ a.toReal / b.toReal` and
    `a.toReal / b.toReal ≤ Dyadic.toReal ⟨q.m + 1, out⟩` (an explicit one-ulp
    error; see also `divFloorQ_err`). Computed entirely in `Int` as
    `(a.m * 2^k) / b.m` with `k = a.e - b.e - out ≥ 0`; Lean's `Int./` is
    Euclidean (= floor only for positive divisors), so for `b.m < 0` the
    mantissa is compensated by `- 1`. `Option`-valued: `none` when `b.m = 0` or
    when the requested granularity leaves no scaling room (`k < 0`); the caller
    retries with a larger `out`.
  - `DInterval.recip I out`: reciprocal of an interval whose closure misses `0`
    (`0 < I.lo` or `I.hi < 0`; on such intervals `x ↦ 1/x` is antitone, so the
    image of `[lo, hi]` is `[1/hi, 1/lo]`). Soundness over `ℝ` (`recip_sound`).
  - `DInterval.div I J out = I * recip J out` with `div_sound`.

  Checking layer: `Int` only (kernel `decide` evaluates every operation — no
  `Rat` arithmetic ever reaches the kernel). Semantic layer: soundness over
  `ℝ` via `toReal`. No `sorry`, no `native_decide`, no new axioms.

  ## Pilots (kernel `decide` only)

  `exRecip_accept` / `exDiv_accept` compute concrete reciprocals/quotients by
  `decide`; `exRecip_end_to_end` / `exDiv_end_to_end` turn them into real
  inequalities (`1/5 < 1/y` on `[2,4]`; `0 < x/y` on `[1,2] × [2,4]`).
-/
import Kepler.Interval.Basic

namespace Kepler.Interval

/-! ## Integer division vs. real division

Lean's division on `ℤ` is Euclidean: `a % b ∈ [0, |b|)` and
`b * (a / b) + a % b = a`, hence `a / b` is the floor of the real quotient
when `b > 0` and its ceiling when `b < 0`. -/

/-- Euclidean division never overshoots the product: `(a / b) * b ≤ a`. -/
theorem Int_ediv_mul_le (a : ℤ) {b : ℤ} (hb : b ≠ 0) : ((a / b : ℤ) : ℝ) * b ≤ a := by
  have h' : (a / b : ℤ) * b + a % b = a := by
    rw [mul_comm]
    exact Int.mul_ediv_add_emod a b
  have hnn : (0:ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg a hb
  have h1 : (a : ℝ) = ((a / b : ℤ) : ℝ) * b + ((a % b : ℤ) : ℝ) := by exact_mod_cast h'.symm
  linarith

/-- For a positive divisor, `(a / b) + 1` rounds up: `a < ((a / b) + 1) * b`. -/
theorem Int_lt_succ_ediv_mul (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (a : ℝ) < (((a / b : ℤ) + 1 : ℤ) : ℝ) * b := by
  have h' : (a / b : ℤ) * b + a % b = a := by
    rw [mul_comm]
    exact Int.mul_ediv_add_emod a b
  have hlt : ((a % b : ℤ) : ℝ) < (b : ℝ) := by
    have := Int.emod_lt a (ne_of_gt hb)
    rw [Int.natAbs_of_nonneg (le_of_lt hb)] at this
    exact_mod_cast this
  have h1 : (a : ℝ) = ((a / b : ℤ) : ℝ) * b + ((a % b : ℤ) : ℝ) := by exact_mod_cast h'.symm
  have h2 : ((a / b : ℤ) : ℝ) * b + b = (((a / b : ℤ) + 1 : ℤ) : ℝ) * b := by
    push_cast
    ring
  linarith

/-- For a negative divisor Euclidean division rounds *towards `+∞`*, so the
useful up-rounding is `a ≤ ((a / b) - 1) * b`. -/
theorem Int_le_subOne_ediv_mul (a : ℤ) {b : ℤ} (hb : b < 0) :
    (a : ℝ) ≤ (((a / b : ℤ) - 1 : ℤ) : ℝ) * b := by
  have h' : (a / b : ℤ) * b + a % b = a := by
    rw [mul_comm]
    exact Int.mul_ediv_add_emod a b
  have hlt : ((a % b : ℤ) : ℝ) < -((b : ℝ)) := by
    have hbabs : b.natAbs = -b := by omega
    have := Int.emod_lt a (ne_of_lt hb)
    rw [hbabs] at this
    exact_mod_cast this
  have h1 : (a : ℝ) = ((a / b : ℤ) : ℝ) * b + ((a % b : ℤ) : ℝ) := by exact_mod_cast h'.symm
  have h2 : ((a / b : ℤ) : ℝ) * b - b = (((a / b : ℤ) - 1 : ℤ) : ℝ) * b := by
    push_cast
    ring
  linarith

/-! ## Real helpers: reciprocal is antitone off zero -/

theorem one_div_le_one_div_neg {a b : ℝ} (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  have hp : (0:ℝ) < -b := neg_pos.2 hb
  have h' : -b ≤ -a := neg_le_neg h
  have h2 := one_div_le_one_div_of_le hp h'
  rw [div_neg, div_neg] at h2
  linarith

/-! ## Dyadic floor division at a fixed output granularity -/

namespace Dyadic

/-- One ulp at granularity `out` (the explicit error term of `divFloorQ`). -/
def ulp (out : Int) : Dyadic := ⟨1, out⟩

theorem toReal_ulp (out : Int) : (ulp out).toReal = (2 : ℝ) ^ out := by
  simp [ulp, toReal_def]

/-- Strict negativity (sign of a dyadic = sign of its mantissa). -/
def isNeg (d : Dyadic) : Bool := decide (d.m < 0)

theorem isNeg_iff (d : Dyadic) : d.isNeg = true ↔ d.toReal < 0 := by
  have hp : (0:ℝ) < (2:ℝ)^d.e := zpow_pos (by norm_num) d.e
  simp only [isNeg, decide_eq_true_eq, toReal_def]
  constructor
  · intro h
    exact mul_neg_of_neg_of_pos (by exact_mod_cast h) hp
  · intro h
    rcases lt_trichotomy (d.m : ℝ) 0 with hn | h0 | hp2
    · exact_mod_cast hn
    · rw [h0, zero_mul] at h
      linarith
    · exact absurd (mul_pos hp2 hp) (by linarith)

/-- `divFloorQ a b out = some q` where `q` is the floor of `a / b` at output
granularity `2^out` (see `divFloorQ_spec` for the two-sided error bound).
Fails (`none`) if `b.m = 0` or `a.e - b.e - out < 0`. All arithmetic is in
`Int` — kernel-checkable by `decide`. -/
def divFloorQ (a b : Dyadic) (out : Int) : Option Dyadic :=
  if _hk : 0 ≤ a.e - b.e - out then
    if _hb : b.m ≠ 0 then
      if 0 < b.m then some ⟨a.m * 2 ^ (a.e - b.e - out).toNat / b.m, out⟩
      else some ⟨a.m * 2 ^ (a.e - b.e - out).toNat / b.m - 1, out⟩
    else none
  else none

/-- Scaling identity: since `(kn : ℤ) = a.e - out`, the semantics factors as
`(a.m * 2^kn) * 2^out`. -/
theorem toReal_scale (a : Dyadic) (kn : ℕ) (out : Int) (hke : ((kn : Int)) = a.e - out) :
    a.toReal = ((a.m * 2 ^ kn : ℤ) : ℝ) * (2 : ℝ) ^ out := by
  have e1 : ((kn : Int)) + out = a.e := by omega
  have h2 : ((2:ℝ)^a.e) = (2:ℝ)^((kn:ℤ)) * (2:ℝ)^out := by
    rw [← e1, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  have h3 : (2:ℝ)^((kn:ℤ)) = ((2:ℤ)^kn : ℝ) := by
    push_cast
    exact zpow_natCast (2:ℝ) kn
  rw [toReal_def, h2, h3]
  push_cast
  ring

/-- Case analysis on a successful `divFloorQ` (used by `divFloorQ_spec`):
either `0 < b.m` and `q` is the plain Euclidean quotient, or `b.m < 0` and the
mantissa is compensated by `- 1`. -/
theorem divFloorQ_cases {a b : Dyadic} {out : Int} {q : Dyadic}
    (h : divFloorQ a b out = some q) :
    (0 < b.m ∧ 0 ≤ a.e - b.e - out ∧ q = ⟨a.m * 2 ^ (a.e - b.e - out).toNat / b.m, out⟩) ∨
    (b.m < 0 ∧ 0 ≤ a.e - b.e - out ∧
      q = ⟨a.m * 2 ^ (a.e - b.e - out).toNat / b.m - 1, out⟩) := by
  unfold divFloorQ at h
  split at h
  · next hk =>
    split at h
    · next _hb =>
      split at h
      · next hpos => exact Or.inl ⟨hpos, hk, (Option.some.inj h).symm⟩
      · next hneg => exact Or.inr ⟨by omega, hk, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Exponent bookkeeping: `divFloorQ` always returns exponent `out`. -/
theorem divFloorQ_e {a b : Dyadic} {out : Int} {q : Dyadic}
    (h : divFloorQ a b out = some q) : q.e = out := by
  rcases divFloorQ_cases h with ⟨_, _, hq⟩ | ⟨_, _, hq⟩
  · rw [hq]
  · rw [hq]

/-- **Soundness of `divFloorQ`**: the returned dyadic is a floor of `a / b` at
granularity `2^out`, and `⟨q.m + 1, out⟩` is a ceiling — the gap is one ulp. -/
theorem divFloorQ_spec {a b : Dyadic} {out : Int} {q : Dyadic}
    (h : divFloorQ a b out = some q) :
    q.toReal ≤ a.toReal / b.toReal ∧
      a.toReal / b.toReal ≤ Dyadic.toReal ⟨q.m + 1, out⟩ := by
  have hcases := divFloorQ_cases h
  have hb : b.m ≠ 0 := by
    rcases hcases with ⟨h1, _, _⟩ | ⟨h1, _, _⟩ <;> omega
  have hk : 0 ≤ a.e - b.e - out := by
    rcases hcases with ⟨_, hk, _⟩ | ⟨_, hk, _⟩ <;> exact hk
  have hkz : (((a.e - b.e - out).toNat : Int)) = a.e - b.e - out :=
    Int.toNat_of_nonneg hk
  have hbne : b.toReal ≠ 0 := by
    rw [toReal_def]
    exact mul_ne_zero (by exact_mod_cast hb) (zpow_ne_zero b.e (by norm_num : (2:ℝ) ≠ 0))
  have hAsc : a.toReal = ((a.m * 2 ^ (a.e - b.e - out).toNat : ℤ) : ℝ)
      * (2 : ℝ) ^ (out + b.e) :=
    toReal_scale a _ (out + b.e) (by omega)
  have hp2 : (0:ℝ) < (2:ℝ)^(out + b.e) := zpow_pos (by norm_num) _
  have hz : (2:ℝ)^out * (2:ℝ)^b.e = (2:ℝ)^(out + b.e) :=
    (zpow_add₀ (by norm_num : (2:ℝ) ≠ 0) out b.e).symm
  -- the shared regrouping step as a linear identity
  have hreg : ∀ (r : Int), Dyadic.toReal ⟨r, out⟩ * b.toReal
      = ((r : ℝ) * (b.m : ℝ)) * (2:ℝ)^(out + b.e) := by
    intro r
    simp only [toReal_def]
    linear_combination (r:ℝ) * (b.m:ℝ) * hz
  rcases hcases with ⟨hpos, _, hq⟩ | ⟨hneg, _, hq⟩
  · -- positive divisor: plain floor
    subst hq
    have hbpos : (0:ℝ) < b.toReal := by
      rw [toReal_def]
      exact mul_pos (by exact_mod_cast hpos) (zpow_pos (by norm_num) b.e)
    constructor
    · rw [le_div_iff₀ hbpos, hAsc, hreg]
      exact mul_le_mul_of_nonneg_right
        (Int_ediv_mul_le (a.m * 2 ^ (a.e - b.e - out).toNat) hb) (le_of_lt hp2)
    · rw [div_le_iff₀ hbpos, hAsc, hreg]
      exact mul_le_mul_of_nonneg_right
        (le_of_lt (Int_lt_succ_ediv_mul (a.m * 2 ^ (a.e - b.e - out).toNat) hpos)) (le_of_lt hp2)
  · -- negative divisor: compensate the ceil rounding by `- 1`
    subst hq
    have hbneg : b.toReal < 0 := by
      rw [toReal_def]
      exact mul_neg_of_neg_of_pos (by exact_mod_cast hneg) (zpow_pos (by norm_num) b.e)
    constructor
    · rw [le_div_iff_of_neg hbneg, hAsc, hreg]
      exact mul_le_mul_of_nonneg_right
        (Int_le_subOne_ediv_mul (a.m * 2 ^ (a.e - b.e - out).toNat) hneg) (le_of_lt hp2)
    · rw [div_le_iff_of_neg hbneg, hAsc, hreg]
      have hn1 : (⟨a.m * 2 ^ (a.e - b.e - out).toNat / b.m - 1, out⟩ : Dyadic).m + 1
          = a.m * 2 ^ (a.e - b.e - out).toNat / b.m := by
        show (a.m * 2 ^ (a.e - b.e - out).toNat / b.m - 1) + 1
            = a.m * 2 ^ (a.e - b.e - out).toNat / b.m
        ring
      rw [hn1]
      exact mul_le_mul_of_nonneg_right
        (Int_ediv_mul_le (a.m * 2 ^ (a.e - b.e - out).toNat) hb) (le_of_lt hp2)

/-- Explicit-error version of `divFloorQ_spec.2`: the truncation error is at
most one ulp at the output granularity. -/
theorem divFloorQ_err {a b : Dyadic} {out : Int} {q : Dyadic}
    (h : divFloorQ a b out = some q) :
    a.toReal / b.toReal - q.toReal ≤ (Dyadic.ulp out).toReal := by
  have h2 := (divFloorQ_spec h).2
  have hq : q.e = out := divFloorQ_e h
  have h3 : Dyadic.toReal ⟨q.m + 1, out⟩ = q.toReal + (Dyadic.ulp out).toReal := by
    rw [Dyadic.toReal_ulp]
    simp only [toReal_def]
    rw [hq]
    push_cast
    ring
  rw [h3] at h2
  linarith

/-- Reciprocal floor at granularity `2^out` (`= divFloorQ 1 b out`). -/
def recipFloor (b : Dyadic) (out : Int) : Option Dyadic := divFloorQ ⟨1, 0⟩ b out

theorem recipFloor_spec {b : Dyadic} {out : Int} {q : Dyadic}
    (h : b.recipFloor out = some q) :
    q.toReal ≤ 1 / b.toReal ∧ 1 / b.toReal ≤ Dyadic.toReal ⟨q.m + 1, out⟩ := by
  have hq : divFloorQ ⟨1, 0⟩ b out = some q := h
  have hspec := divFloorQ_spec hq
  have h1 : (⟨1, 0⟩ : Dyadic).toReal = 1 := by
    rw [toReal_def]
    norm_num
  rw [h1] at hspec
  exact hspec

end Dyadic

/-! ## Interval reciprocal and division -/

namespace DInterval

/-- Reciprocal of an interval: `some` iff the interval's closure misses `0`
(`0 < lo` or `hi < 0`); the image of `[lo, hi]` under `x ↦ 1/x` is
`[1/hi, 1/lo]`, so the endpoints are reciprocal floors of `hi` and `lo`. -/
def recip (I : DInterval) (out : Int) : Option DInterval :=
  if I.lo.isPos = true ∨ I.hi.isNeg = true then
    match I.hi.recipFloor out, I.lo.recipFloor out with
    | some fl, some fu => some ⟨fl, ⟨fu.m + 1, out⟩⟩
    | _, _ => none
  else none

/-- **Soundness of interval reciprocal** (over `ℝ`): if the check succeeds,
every real `y` in the input interval has its reciprocal in the output. -/
theorem recip_sound {I : DInterval} {out : Int} {J : DInterval} {y : ℝ}
    (hy : I.mem y) (h : I.recip out = some J) : J.mem ((1:ℝ) / y) := by
  obtain ⟨hy1, hy2⟩ := hy
  unfold recip at h
  split at h
  · next hcond =>
    rcases hcond with hlo | hhi
    · -- 0 < lo ≤ y ≤ hi
      have hlo' : 0 < I.lo.toReal := (Dyadic.isPos_iff I.lo).mp hlo
      have hy0 : 0 < y := lt_of_lt_of_le hlo' hy1
      cases hh : I.hi.recipFloor out with
      | none => rw [hh] at h; simp at h
      | some fl =>
        cases hl : I.lo.recipFloor out with
        | none => rw [hh, hl] at h; simp at h
        | some fu =>
          rw [hh, hl] at h
          have hJ : ⟨fl, ⟨fu.m + 1, out⟩⟩ = J := by simpa using h
          obtain rfl : J = ⟨fl, ⟨fu.m + 1, out⟩⟩ := hJ.symm
          obtain ⟨hspec1, hspec2⟩ := Dyadic.recipFloor_spec hh
          obtain ⟨hspec1', hspec2'⟩ := Dyadic.recipFloor_spec hl
          constructor
          · exact le_trans hspec1 (one_div_le_one_div_of_le hy0 hy2)
          · exact le_trans (one_div_le_one_div_of_le hlo' hy1) hspec2'
    · -- lo ≤ y ≤ hi < 0
      have hhi' : I.hi.toReal < 0 := (Dyadic.isNeg_iff I.hi).mp hhi
      have hy0 : y < 0 := lt_of_le_of_lt hy2 hhi'
      cases hh : I.hi.recipFloor out with
      | none => rw [hh] at h; simp at h
      | some fl =>
        cases hl : I.lo.recipFloor out with
        | none => rw [hh, hl] at h; simp at h
        | some fu =>
          rw [hh, hl] at h
          have hJ : ⟨fl, ⟨fu.m + 1, out⟩⟩ = J := by simpa using h
          obtain rfl : J = ⟨fl, ⟨fu.m + 1, out⟩⟩ := hJ.symm
          obtain ⟨hspec1, hspec2⟩ := Dyadic.recipFloor_spec hh
          obtain ⟨hspec1', hspec2'⟩ := Dyadic.recipFloor_spec hl
          constructor
          · exact le_trans hspec1 (one_div_le_one_div_neg hhi' hy2)
          · exact le_trans (one_div_le_one_div_neg hy0 hy1) hspec2'
  · exact absurd h (by simp)

/-- Division: `I / J = I * (1/J)`, available whenever `J` misses `0`. -/
def div (I J : DInterval) (out : Int) : Option DInterval :=
  match J.recip out with
  | some r => some (I.mul r)
  | none => none

/-- **Soundness of interval division** (over `ℝ`). -/
theorem div_sound {I J : DInterval} {out : Int} {K : DInterval} {x y : ℝ}
    (h : DInterval.div I J out = some K) (hx : I.mem x) (hy : J.mem y) :
    K.mem (x / y) := by
  unfold DInterval.div at h
  cases hr : J.recip out with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr] at h
    have hK : I.mul r = K := by simpa using h
    obtain rfl : K = I.mul r := hK.symm
    have hyr : r.mem ((1:ℝ) / y) := J.recip_sound hy hr
    have hyz : y ≠ 0 := by
      by_contra hy0
      subst hy0
      obtain ⟨hy1, hy2⟩ := hy
      unfold DInterval.recip at hr
      split at hr
      · next hcond =>
        rcases hcond with hlo | hhi
        · have hlo' := (Dyadic.isPos_iff J.lo).mp hlo
          linarith
        · have hhi' := (Dyadic.isNeg_iff J.hi).mp hhi
          linarith
      · exact absurd hr (by simp)
    have hmul := DInterval.mem_mul hx hyr
    have heq : x / y = x * (1 / y) := by field_simp
    rwa [← heq] at hmul

end DInterval

/-! ## Small pilot cases (kernel `decide` only) -/

-- `1/x` on `[2,4]` at granularity `2^-2`: computes `[1/4, 3/4]`.
theorem exRecip_accept :
    DInterval.recip ⟨⟨2, 0⟩, ⟨4, 0⟩⟩ (-2) = some ⟨⟨1, -2⟩, ⟨3, -2⟩⟩ := by
  decide

-- End-to-end: `1/5 < 1/y` for every real `y ∈ [2,4]`.
theorem exRecip_end_to_end (y : ℝ) (hy1 : (2:ℝ) ≤ y) (hy2 : y ≤ 4) :
    (1:ℝ)/5 < 1/y := by
  have hmem : (⟨⟨2, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem y := by
    constructor
    · show Dyadic.toReal ⟨2, 0⟩ ≤ y
      rw [Dyadic.toReal_int]
      exact_mod_cast hy1
    · show y ≤ Dyadic.toReal ⟨4, 0⟩
      rw [Dyadic.toReal_int]
      exact_mod_cast hy2
  obtain ⟨h1, _⟩ := DInterval.recip_sound hmem exRecip_accept
  have hlo : Dyadic.toReal ⟨1, -2⟩ = 1/4 := by
    rw [Dyadic.toReal_def]
    norm_num
  rw [hlo] at h1
  linarith

-- `x/y` on `[1,2] × [2,4]` at granularity `2^-2`:
-- `recip [2,4] = [1/4, 3/4]`, then `[1,2] * [1/4, 3/4] = [1/4, 3/2]`.
theorem exDiv_accept :
    DInterval.div ⟨⟨1, 0⟩, ⟨2, 0⟩⟩ ⟨⟨2, 0⟩, ⟨4, 0⟩⟩ (-2)
      = some ⟨⟨1, -2⟩, ⟨6, -2⟩⟩ := by
  decide

-- End-to-end: `0 < x/y` for every real `x ∈ [1,2]`, `y ∈ [2,4]`.
theorem exDiv_end_to_end (x y : ℝ) (hx1 : (1:ℝ) ≤ x) (hx2 : x ≤ 2)
    (hy1 : (2:ℝ) ≤ y) (hy2 : y ≤ 4) : 0 < x / y := by
  have hmemI : (⟨⟨1, 0⟩, ⟨2, 0⟩⟩ : DInterval).mem x := by
    constructor
    · show Dyadic.toReal ⟨1, 0⟩ ≤ x
      rw [Dyadic.toReal_int]
      exact_mod_cast hx1
    · show x ≤ Dyadic.toReal ⟨2, 0⟩
      rw [Dyadic.toReal_int]
      exact_mod_cast hx2
  have hmemJ : (⟨⟨2, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem y := by
    constructor
    · show Dyadic.toReal ⟨2, 0⟩ ≤ y
      rw [Dyadic.toReal_int]
      exact_mod_cast hy1
    · show y ≤ Dyadic.toReal ⟨4, 0⟩
      rw [Dyadic.toReal_int]
      exact_mod_cast hy2
  obtain ⟨h1, _⟩ := DInterval.div_sound exDiv_accept hmemI hmemJ
  have hlo : Dyadic.toReal ⟨1, -2⟩ = 1/4 := by
    rw [Dyadic.toReal_def]
    norm_num
  rw [hlo] at h1
  linarith

end Kepler.Interval
