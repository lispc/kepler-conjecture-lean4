/-
Kepler.Text.TaylorSecond.DCKit — lane `wt1-emission-pilot-w1`, M0 of the DC
soundness layer (2026-11-25).

The dyadic interval core `DC` is **verbatim** the Route E kit
(`wt1-close-w1/lean/Wt1LeafKit.lean:31–100`, lane `wt1-close-w1`), so the 403
Route E shards' numeric facts stay valid.  This file adds the *semantics* that
kit lacks (`DC.mem`) and the primitive soundness lemmas.

`DC.mem I x` reads `x` in the dyadic interval `I`: with `s = 2^(-I.k) > 0`,
`(I.lo : ℝ) * s ≤ x ≤ (I.hi : ℝ) * s`.

No `axiom` / `sorry` / `admit` / `native_decide`.
-/
import Mathlib.Data.Int.Bitwise
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

namespace DCKit

/-! ## 1. The dyadic interval core (verbatim Route E bodies) -/

structure DC where
  k : ℤ
  lo : ℤ
  hi : ℤ

def dInt (n : ℤ) : DC := ⟨0, n, n⟩

def dnorm (k lo hi : ℤ) : DC :=
  let bl := max (Int.natAbs lo).log2 (Int.natAbs hi).log2 + 1
  if bl ≤ 200 then ⟨k, lo, hi⟩
  else
    let drop := min (bl - 200) (Int.natAbs k)
    ⟨k - drop, Int.shiftRight lo drop, -Int.shiftRight (-hi) drop⟩

def dAdd (A B : DC) : DC :=
  let k := max A.k B.k
  let s1 := A.lo <<< (k - A.k)
  let s2 := B.lo <<< (k - B.k)
  let h1 := A.hi <<< (k - A.k)
  let h2 := B.hi <<< (k - B.k)
  dnorm k (s1 + s2) (h1 + h2)

def dNeg (A : DC) : DC := ⟨A.k, -A.hi, -A.lo⟩

def dSub (A B : DC) : DC := dAdd A (dNeg B)

def dMul (A B : DC) : DC :=
  let K := A.k + B.k
  let c1 := A.lo * B.lo
  let c2 := A.lo * B.hi
  let c3 := A.hi * B.lo
  let c4 := A.hi * B.hi
  dnorm K (min c1 (min c2 (min c3 c4))) (max c1 (max c2 (max c3 c4)))

def dInv (B : DC) : DC :=
  let bl := (Int.natAbs B.lo).log2 + 1
  let S := 208 + bl
  let M := (1 : ℤ) <<< S
  dnorm (S - B.k) (M / B.hi) (-((-M) / B.lo))

def dDiv (A B : DC) : DC := dMul A (dInv B)


/-! ## 1b. Global bracket constants (verbatim Route E literals, k = 40) -/

def SQ2 : DC := ⟨40, 1554944255987, 1554944255988⟩

def PIbr : DC := ⟨40, 3454217652357, 3454217652358⟩

def K1 : DC := ⟨40, 708427049925, 708427119965⟩

def K2 : DC := ⟨40, 71157635854, 71157663892⟩

def ONE : DC := dInt 1

def THIRD : DC := dInv (dInt 3)

def FIFTH : DC := dInv (dInt 5)

def TWELFTH : DC := dInv (dInt 12)

def EIGHTH : DC := dInv (dInt 125)

/-! ## 2. Semantics -/

/-- `x` lies in the dyadic interval `I`. -/
def DC.mem (I : DC) (x : ℝ) : Prop :=
  (I.lo : ℝ) * (2 : ℝ) ^ (-(I.k : ℤ)) ≤ x ∧ x ≤ (I.hi : ℝ) * (2 : ℝ) ^ (-(I.k : ℤ))

theorem mem_zero_pow (k : ℤ) : (0:ℝ) < (2:ℝ) ^ (-k) := zpow_pos (by norm_num) _

/-! ## 3. Shift bridges -/

/-- `<<<` by a nat is multiplication by `2^d`. -/
theorem shiftLeft_eq_mul (x : ℤ) (d : ℕ) : x <<< (d : ℤ) = x * 2 ^ d :=
  Int.shiftLeft_eq_mul_pow x d

/-- **(⋆)** `>>>` is below the real division: `(x >>> d : ℝ) ≤ (x : ℝ)/2^d`
(all `x : ℤ`, `d : ℕ`).  This is all `dnorm_mem` needs — **not** the `ediv`
characterisation (which is over-strong and needs lemmas that do not exist in
this Mathlib). -/
theorem shiftRight_cast_le (x : ℤ) (d : ℕ) :
    ((x >>> (d : ℤ) : ℤ) : ℝ) ≤ (x : ℝ) / (2 : ℝ) ^ d := by
  induction x using Int.negInduction with
  | nat m =>
      have hL : ((m : ℤ) >>> (↑d : ℤ)) = (m : ℤ) / (2 : ℤ) ^ d := by
        rw [Int.shiftRight_natCast, Nat.shiftRight_eq_div_pow, Int.natCast_ediv]
        norm_num
      rw [hL]
      have hmul : ((m : ℤ) / (2 : ℤ) ^ d) * (2 : ℤ) ^ d ≤ (m : ℤ) :=
        Int.ediv_mul_le (m : ℤ) (by positivity)
      have hcast : ((((m : ℤ) / (2 : ℤ) ^ d : ℤ)) : ℝ) * (2 : ℝ) ^ d ≤ (m : ℝ) := by
        have h2 : ((((m : ℤ) / (2 : ℤ) ^ d) * (2 : ℤ) ^ d : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by
          exact_mod_cast hmul
        push_cast [Int.cast_pow] at h2
        simpa using h2
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)]
      exact hcast
  | neg ih n =>
      cases n with
      | zero => simp
      | succ k =>
          rw [show -(↑(Nat.succ k) : ℤ) = Int.negSucc k from rfl, Int.shiftRight_negSucc]
          have hmod : k % 2 ^ d < 2 ^ d := Nat.mod_lt k (Nat.two_pow_pos d)
          have hnat : k + 1 ≤ (k >>> d + 1) * 2 ^ d := by
            rw [Nat.shiftRight_eq_div_pow]
            set q : ℕ := k / 2 ^ d * 2 ^ d with hq
            have hqk : q + k % 2 ^ d = k := by
              rw [hq, Nat.mul_comm]
              exact Nat.div_add_mod k (2 ^ d)
            have hexp : (k / 2 ^ d + 1) * 2 ^ d = q + 2 ^ d := by
              rw [hq]; ring
            rw [hexp, ← hqk]
            omega
          have hR : ((k : ℝ) + 1) ≤ ((k >>> d : ℕ) + 1) * (2 : ℝ) ^ d := by
            have h' : ((k + 1 : ℕ) : ℝ) ≤ (((k >>> d + 1) * 2 ^ d : ℕ) : ℝ) := by
              exact_mod_cast hnat
            push_cast at h'
            linarith
          push_cast
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)]
          nlinarith

#print axioms shiftRight_cast_le

/-- **(⋆)** in the `Nat`-shift form the definition actually uses
(`Int.shiftRight : ℤ → ℕ → ℤ`). -/
lemma shiftRight_cast_le_nat (x : ℤ) (d : ℕ) :
    ((x.shiftRight d : ℤ) : ℝ) ≤ (x : ℝ) / (2 : ℝ) ^ d := by
  have h := shiftRight_cast_le x d
  rwa [Int.shiftRight_natCast_right] at h

#print axioms shiftRight_cast_le_nat

/-! ## 3b. Scale bookkeeping helpers -/

/-- `2^-k = 2^(kk-k) * 2^-kk` for `k ≤ kk`. -/
theorem zpow_scale (kk k : ℤ) (h : k ≤ kk) :
    (2:ℝ)^(-k) = (2:ℝ)^(kk - k) * (2:ℝ)^(-kk) := by
  rw [show (-k : ℤ) = (kk - k) + (-kk) by ring, zpow_add₀ (a := (2:ℝ)) (by norm_num)]

/-- `(x <<< (kk - k)) * 2^-kk = x * 2^-k` for `k ≤ kk`. -/
theorem shiftLeft_scale {x kk k : ℤ} (h : k ≤ kk) :
    ((x <<< (kk - k) : ℤ) : ℝ) * (2 : ℝ) ^ (-kk) = (x : ℝ) * (2 : ℝ) ^ (-k) := by
  have hn : (0:ℤ) ≤ kk - k := by omega
  have hcast : ((x <<< (kk - k) : ℤ) : ℝ) = (x:ℝ) * (2:ℝ) ^ (kk - k) := by
    have h1 := shiftLeft_eq_mul x (kk - k).toNat
    rw [show kk - k = ((kk - k).toNat : ℤ) from (Int.toNat_of_nonneg hn).symm]
    rw [h1]
    push_cast
    rw [zpow_natCast]
  rw [hcast, zpow_scale kk k h]
  ring

/-- `x / 2^d * 2^d = x` for `x : ℝ`. -/
theorem div_pow_mul_pow (x : ℝ) (d : ℕ) : x / (2:ℝ)^d * (2:ℝ)^d = x := by
  field_simp

/-! ## 4. Primitive soundness lemmas -/

/-- `dInt`. -/
theorem dInt_mem (n : ℤ) : (dInt n).mem (n : ℝ) := by
  refine ⟨?_, ?_⟩ <;> simp [dInt, DC.mem]

/-- `dNeg`. -/
theorem dNeg_mem {A : DC} {a : ℝ} (h : A.mem a) : (dNeg A).mem (-a) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · show ((-A.hi : ℤ) : ℝ) * (2:ℝ) ^ (-(A.k : ℤ)) ≤ -a
    push_cast
    linarith
  · show -a ≤ ((-A.lo : ℤ) : ℝ) * (2:ℝ) ^ (-(A.k : ℤ))
    push_cast
    linarith
/-- Flattens the `DC.mk` projections once and for all. -/
lemma DC.mem_mk (k lo hi : ℤ) (x : ℝ) :
    DC.mem ⟨k, lo, hi⟩ x ↔
      ((lo : ℝ) * (2:ℝ) ^ (-(k : ℤ)) ≤ x ∧ x ≤ (hi : ℝ) * (2:ℝ) ^ (-(k : ℤ))) :=
  Iff.rfl


/-! `dnorm_mem` — **still open** (M0 card in `HANDOFF-M0.md`, M0-D): the
mathematics is the two endpoint inequalities of the M0-C card, now with
`DC.mem_mk` in place; the remaining obstacle is purely syntactic — the goal's
shift appears as `Int.shiftRight lo ↑drop` while the helper's conclusion is
`↑(lo >>> ↑drop)`, so `rw`/`calc` steps do not match even after `set`
(`logs/dckit14.log`).  `set`-bound `L`/`U` versions of both branches are kept in
`/tmp/DCKit_wip.lean` for the next pass. -/

/-- `dnorm`: containment only (no bit-length invariant). -/
theorem dnorm_mem {k lo hi : ℤ} {x : ℝ} (h : (DC.mk k lo hi).mem x) :
    (dnorm k lo hi).mem x := by
  rw [DC.mem_mk] at h
  by_cases hb : max (Int.natAbs lo).log2 (Int.natAbs hi).log2 + 1 ≤ 200
  · rw [dnorm, if_pos hb, DC.mem_mk]; exact h
  · rw [dnorm, if_neg hb, DC.mem_mk]
    set drop : ℕ := min (max (Int.natAbs lo).log2 (Int.natAbs hi).log2 + 1 - 200)
      (Int.natAbs k) with hdrop
    have hpow : (2:ℝ) ^ (-(k - (drop:ℤ))) = (2:ℝ) ^ (-k) * (2:ℝ) ^ (drop:ℕ) := by
      rw [show -(k - (drop:ℤ)) = -k + (drop:ℤ) by ring,
        zpow_add₀ (a := (2:ℝ)) (by norm_num), zpow_natCast]
    have hpk : (0:ℝ) < (2:ℝ) ^ (-k) := mem_zero_pow k
    have hpd : (0:ℝ) < (2:ℝ) ^ (drop:ℕ) := by positivity
    refine ⟨?_, ?_⟩
    · have h1 := shiftRight_cast_le_nat lo drop
      have h1b : ((lo.shiftRight drop : ℤ) : ℝ) * (2:ℝ)^drop ≤ (lo:ℝ) := by
        calc ((lo.shiftRight drop : ℤ) : ℝ) * (2:ℝ)^drop
            ≤ ((lo:ℝ) / (2:ℝ)^drop) * (2:ℝ)^drop :=
              mul_le_mul_of_nonneg_right h1 hpd.le
          _ = (lo:ℝ) := div_pow_mul_pow _ _
      rw [hpow]
      calc ((lo.shiftRight drop : ℤ) : ℝ) * ((2:ℝ)^(-k) * (2:ℝ)^(drop:ℕ))
          = (((lo.shiftRight drop : ℤ) : ℝ) * (2:ℝ)^(drop:ℕ)) * (2:ℝ)^(-k) := by ring
        _ ≤ (lo:ℝ) * (2:ℝ)^(-k) := mul_le_mul_of_nonneg_right h1b hpk.le
        _ ≤ x := h.1
    · have h1 := shiftRight_cast_le_nat (-hi) drop
      have h1b : (((-hi).shiftRight drop : ℤ) : ℝ) * (2:ℝ)^drop ≤ -(hi:ℝ) := by
        calc (((-hi).shiftRight drop : ℤ) : ℝ) * (2:ℝ)^drop
            ≤ (((-hi:ℤ) : ℝ) / (2:ℝ)^drop) * (2:ℝ)^drop :=
              mul_le_mul_of_nonneg_right h1 hpd.le
          _ = ((-hi:ℤ) : ℝ) := div_pow_mul_pow _ _
          _ = -(hi:ℝ) := by push_cast; ring
      have hhi : (hi:ℝ) ≤ -((((-hi).shiftRight drop : ℤ) : ℝ)) * (2:ℝ)^drop := by linarith
      have hce : (((-((-hi).shiftRight drop) : ℤ)) : ℝ)
          = -((((-hi).shiftRight drop : ℤ) : ℝ)) := by push_cast; ring
      rw [hpow, hce]
      calc x ≤ (hi:ℝ) * (2:ℝ)^(-k) := h.2
        _ ≤ (-((((-hi).shiftRight drop : ℤ) : ℝ)) * (2:ℝ)^(drop:ℕ)) * (2:ℝ)^(-k) :=
            mul_le_mul_of_nonneg_right hhi hpk.le
        _ = -((((-hi).shiftRight drop : ℤ) : ℝ)) * ((2:ℝ)^(-k) * (2:ℝ)^(drop:ℕ)) := by ring

/-- `dAdd`. -/
theorem dAdd_mem {A B : DC} {a b : ℝ} (hA : A.mem a) (hB : B.mem b) :
    (dAdd A B).mem (a + b) := by
  rw [DC.mem_mk] at hA hB
  rw [dAdd]
  apply dnorm_mem
  rw [DC.mem_mk]
  have hAk : A.k ≤ max A.k B.k := le_max_left _ _
  have hBk : B.k ≤ max A.k B.k := le_max_right _ _
  have hsA := shiftLeft_scale (x := A.lo) hAk
  have hsB := shiftLeft_scale (x := B.lo) hBk
  have hhA := shiftLeft_scale (x := A.hi) hAk
  have hhB := shiftLeft_scale (x := B.hi) hBk
  refine ⟨?_, ?_⟩
  · have h1 : ((A.lo <<< (max A.k B.k - A.k) : ℤ) : ℝ) * (2:ℝ)^(-(max A.k B.k)) ≤ a := by
      rw [hsA]; exact hA.1
    have h2 : ((B.lo <<< (max A.k B.k - B.k) : ℤ) : ℝ) * (2:ℝ)^(-(max A.k B.k)) ≤ b := by
      rw [hsB]; exact hB.1
    have hsum : ((((A.lo <<< (max A.k B.k - A.k)) + (B.lo <<< (max A.k B.k - B.k)) : ℤ)) : ℝ)
        * (2:ℝ)^(-(max A.k B.k))
        = ((A.lo <<< (max A.k B.k - A.k) : ℤ) : ℝ) * (2:ℝ)^(-(max A.k B.k))
          + ((B.lo <<< (max A.k B.k - B.k) : ℤ) : ℝ) * (2:ℝ)^(-(max A.k B.k)) := by
      push_cast; ring
    rw [hsum]; linarith
  · have h1 : a ≤ ((A.hi <<< (max A.k B.k - A.k) : ℤ) : ℝ) * (2:ℝ)^(-(max A.k B.k)) := by
      rw [hhA]; exact hA.2
    have h2 : b ≤ ((B.hi <<< (max A.k B.k - B.k) : ℤ) : ℝ) * (2:ℝ)^(-(max A.k B.k)) := by
      rw [hhB]; exact hB.2
    have hsum : ((((A.hi <<< (max A.k B.k - A.k)) + (B.hi <<< (max A.k B.k - B.k)) : ℤ)) : ℝ)
        * (2:ℝ)^(-(max A.k B.k))
        = ((A.hi <<< (max A.k B.k - A.k) : ℤ) : ℝ) * (2:ℝ)^(-(max A.k B.k))
          + ((B.hi <<< (max A.k B.k - B.k) : ℤ) : ℝ) * (2:ℝ)^(-(max A.k B.k)) := by
      push_cast; ring
    rw [hsum]; linarith

/-- `dSub`. -/
theorem dSub_mem {A B : DC} {a b : ℝ} (hA : A.mem a) (hB : B.mem b) :
    (dSub A B).mem (a - b) := by
  have h := dAdd_mem hA (dNeg_mem hB)
  simpa [dSub, sub_eq_add_neg] using h

#print axioms dnorm_mem
#print axioms dAdd_mem
#print axioms dSub_mem

/-- Scaling helper: `a * 2^A.k` lies in `[A.lo, A.hi]`. -/
theorem scale_mem {A : DC} {a : ℝ} (h : A.mem a) :
    (A.lo : ℝ) ≤ a * (2:ℝ)^(A.k) ∧ a * (2:ℝ)^(A.k) ≤ (A.hi : ℝ) := by
  have hk : (0:ℝ) < (2:ℝ)^(A.k) := zpow_pos (by norm_num) _
  have hinv : (2:ℝ)^(-(A.k)) * (2:ℝ)^(A.k) = 1 := by
    rw [← zpow_add₀ (a := (2:ℝ)) (by norm_num), show (-(A.k) + A.k : ℤ) = 0 by ring,
      zpow_zero]
  refine ⟨?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_right h.1 hk.le
    rwa [mul_assoc, hinv, mul_one] at h1
  · have h1 := mul_le_mul_of_nonneg_right h.2 hk.le
    rwa [mul_assoc, hinv, mul_one] at h1

/-- The real-level four-corner bound (the heart of `dMul_mem`): for
`al ≤ x ≤ ah` and `bl ≤ y ≤ bh`, `x*y` lies between the min and the max of the
four corner products.  Two sign branches on `y`, one on a corner factor each. -/
theorem mul_mem_corners {al ah bl bh x y : ℝ} (h1 : al ≤ x) (h2 : x ≤ ah)
    (h3 : bl ≤ y) (h4 : y ≤ bh) :
    min (al * bl) (min (al * bh) (min (ah * bl) (ah * bh))) ≤ x * y ∧
      x * y ≤ max (al * bl) (max (al * bh) (max (ah * bl) (ah * bh))) := by
  have hM3 : ah * bh ≤ max (al * bl) (max (al * bh) (max (ah * bl) (ah * bh))) :=
    le_trans (le_max_right (ah * bl) (ah * bh))
      (le_trans (le_max_right (al * bh) (max (ah * bl) (ah * bh)))
        (le_max_right (al * bl) (max (al * bh) (max (ah * bl) (ah * bh)))))
  have hM2 : ah * bl ≤ max (al * bl) (max (al * bh) (max (ah * bl) (ah * bh))) :=
    le_trans (le_max_left (ah * bl) (ah * bh))
      (le_trans (le_max_right (al * bh) (max (ah * bl) (ah * bh)))
        (le_max_right (al * bl) (max (al * bh) (max (ah * bl) (ah * bh)))))
  have hM1 : al * bh ≤ max (al * bl) (max (al * bh) (max (ah * bl) (ah * bh))) :=
    le_trans (le_max_left (al * bh) (max (ah * bl) (ah * bh)))
      (le_max_right (al * bl) (max (al * bh) (max (ah * bl) (ah * bh))))
  have hM0 : al * bl ≤ max (al * bl) (max (al * bh) (max (ah * bl) (ah * bh))) :=
    le_max_left _ _
  have hm3 : min (al * bl) (min (al * bh) (min (ah * bl) (ah * bh))) ≤ ah * bh :=
    le_trans (min_le_right (al * bl) (min (al * bh) (min (ah * bl) (ah * bh))))
      (le_trans (min_le_right (al * bh) (min (ah * bl) (ah * bh)))
        (min_le_right (ah * bl) (ah * bh)))
  have hm2 : min (al * bl) (min (al * bh) (min (ah * bl) (ah * bh))) ≤ ah * bl :=
    le_trans (min_le_right (al * bl) (min (al * bh) (min (ah * bl) (ah * bh))))
      (le_trans (min_le_right (al * bh) (min (ah * bl) (ah * bh)))
        (min_le_left (ah * bl) (ah * bh)))
  have hm1 : min (al * bl) (min (al * bh) (min (ah * bl) (ah * bh))) ≤ al * bh :=
    le_trans (min_le_right (al * bl) (min (al * bh) (min (ah * bl) (ah * bh))))
      (min_le_left (al * bh) (min (ah * bl) (ah * bh)))
  have hm0 : min (al * bl) (min (al * bh) (min (ah * bl) (ah * bh))) ≤ al * bl :=
    min_le_left _ _
  constructor
  · rcases le_total 0 y with hy | hy
    · have hx : al * y ≤ x * y := mul_le_mul_of_nonneg_right h1 hy
      rcases le_total 0 al with ha | ha
      · exact le_trans (le_trans hm0 (mul_le_mul_of_nonneg_left h3 ha)) hx
      · exact le_trans (le_trans hm1 (mul_le_mul_of_nonpos_left h4 ha)) hx
    · have hx : ah * y ≤ x * y := mul_le_mul_of_nonpos_right h2 hy
      rcases le_total 0 ah with ha | ha
      · exact le_trans (le_trans hm2 (mul_le_mul_of_nonneg_left h3 ha)) hx
      · exact le_trans (le_trans hm3 (mul_le_mul_of_nonpos_left h4 ha)) hx
  · rcases le_total 0 y with hy | hy
    · have hx : x * y ≤ ah * y := mul_le_mul_of_nonneg_right h2 hy
      rcases le_total 0 ah with ha | ha
      · exact le_trans hx (le_trans (mul_le_mul_of_nonneg_left h4 ha) hM3)
      · exact le_trans hx (le_trans (mul_le_mul_of_nonpos_left h3 ha) hM2)
    · have hx : x * y ≤ al * y := mul_le_mul_of_nonpos_right h1 hy
      rcases le_total 0 al with ha | ha
      · exact le_trans hx (le_trans (mul_le_mul_of_nonneg_left h4 ha) hM1)
      · exact le_trans hx (le_trans (mul_le_mul_of_nonpos_left h3 ha) hM0)

#print axioms scale_mem
#print axioms mul_mem_corners
/-- Product memory: `dMul`'s four corners, via the ℝ-level `mul_mem_corners`. -/
theorem dMul_mem {A B : DC} {a b : ℝ} (hA : A.mem a) (hB : B.mem b) :
    (dMul A B).mem (a * b) := by
  rw [dMul]
  apply dnorm_mem
  rw [DC.mem_mk]
  push_cast
  obtain ⟨hAlo, hAhi⟩ := scale_mem hA
  obtain ⟨hBlo, hBhi⟩ := scale_mem hB
  obtain ⟨hmin, hmax⟩ := mul_mem_corners hAlo hAhi hBlo hBhi
  have hpos : (0:ℝ) < (2:ℝ)^(-(A.k + B.k)) := zpow_pos (by norm_num) _
  have e1 : (2:ℝ)^(A.k) * (2:ℝ)^(-(A.k)) = 1 := by
    rw [← zpow_add₀ (a := (2:ℝ)) (by norm_num), show (A.k + -(A.k)) = 0 by ring, zpow_zero]
  have e2 : (2:ℝ)^(B.k) * (2:ℝ)^(-(B.k)) = 1 := by
    rw [← zpow_add₀ (a := (2:ℝ)) (by norm_num), show (B.k + -(B.k)) = 0 by ring, zpow_zero]
  have hab : a * b =
      (a * (2:ℝ)^(A.k)) * (b * (2:ℝ)^(B.k)) * (2:ℝ)^(-(A.k + B.k)) := by
    calc a * b
        = (a * b) * ((2:ℝ)^(A.k) * (2:ℝ)^(-(A.k))) *
            ((2:ℝ)^(B.k) * (2:ℝ)^(-(B.k))) := by rw [e1, e2]; ring
      _ = (a * (2:ℝ)^(A.k)) * (b * (2:ℝ)^(B.k)) *
            ((2:ℝ)^(-(A.k)) * (2:ℝ)^(-(B.k))) := by ring
      _ = (a * (2:ℝ)^(A.k)) * (b * (2:ℝ)^(B.k)) * (2:ℝ)^(-(A.k + B.k)) := by
          rw [show (-(A.k + B.k) : ℤ) = -(A.k) + -(B.k) by ring,
            zpow_add₀ (a := (2:ℝ)) (by norm_num)]
  rw [hab]
  exact ⟨mul_le_mul_of_nonneg_right hmin hpos.le,
    mul_le_mul_of_nonneg_right hmax hpos.le⟩

#print axioms dMul_mem

#print axioms mem_zero_pow
#print axioms shiftLeft_eq_mul
#print axioms shiftRight_cast_le
#print axioms zpow_scale
#print axioms shiftLeft_scale
#print axioms div_pow_mul_pow
#print axioms DC.mem_mk
#print axioms dInt_mem
#print axioms dNeg_mem


/-- Inverse memory (denominator interval strictly positive).  The route is the
two `Int.ediv` castings of `dInv`'s endpoints; no definition is changed. -/
theorem dInv_mem {B : DC} {b : ℝ} (hlo : 0 < B.lo) (h : B.mem b) :
    (dInv B).mem b⁻¹ := by
  have hb0 : (0:ℝ) < (2:ℝ)^(-(B.k)) := zpow_pos (by norm_num) _
  have hbk : (0:ℝ) < (2:ℝ)^(B.k) := zpow_pos (by norm_num) _
  have hblo : (0:ℝ) < (B.lo : ℝ) := by exact_mod_cast hlo
  have hb : (0:ℝ) < b := lt_of_lt_of_le (mul_pos hblo hb0) h.1
  have hbhi : (0:ℝ) < (B.hi : ℝ) := by
    have h3 : (0:ℝ) < (B.hi:ℝ) * (2:ℝ)^(-(B.k)) := lt_of_lt_of_le hb h.2
    rw [mul_comm] at h3
    exact pos_of_mul_pos_right h3 hb0.le
  have hbhiZ : (0:ℤ) < B.hi := by exact_mod_cast hbhi
  rw [dInv]
  apply dnorm_mem
  rw [DC.mem_mk]
  set S : ℕ := 208 + ((Int.natAbs B.lo).log2 + 1) with hS
  generalize hM : ((1:ℤ) <<< S) = M
  have hMpow : (M : ℝ) = (2:ℝ)^(S:ℤ) := by
    rw [← hM, ← Int.shiftLeft_natCast_right, Int.shiftLeft_eq_mul_pow]
    push_cast
    simp
  have hSpow : (2:ℝ)^(S:ℤ) * (2:ℝ)^(-((S:ℤ) - B.k)) = (2:ℝ)^(B.k) := by
    rw [← zpow_add₀ (a := (2:ℝ)) (by norm_num)]
    congr 1
    ring
  -- floor / ceil castings
  have hfloorZ : (M / B.hi) * B.hi ≤ M := Int.ediv_mul_le M (ne_of_gt hbhiZ)
  have hfloor : (↑(M / B.hi) : ℝ) ≤ (M:ℝ) / (B.hi:ℝ) := by
    have h' : ((M / B.hi : ℤ) : ℝ) * (B.hi:ℝ) ≤ (M:ℝ) := by exact_mod_cast hfloorZ
    exact (le_div_iff₀ hbhi).mpr h'
  have hceilZ : ((-M) / B.lo) * B.lo ≤ -M := Int.ediv_mul_le (-M) (ne_of_gt hlo)
  have hceil : (M:ℝ) / (B.lo:ℝ) ≤ (↑(-((-M) / B.lo)) : ℝ) := by
    have h' : ((((-M) / B.lo : ℤ)) : ℝ) * (B.lo:ℝ) ≤ (-M:ℝ) := by exact_mod_cast hceilZ
    have h1 : ((((-M) / B.lo : ℤ)) : ℝ) ≤ (-M:ℝ) / (B.lo:ℝ) := (le_div_iff₀ hblo).mpr h'
    have h2 : -(((-M:ℝ) / (B.lo:ℝ))) ≤ -(((((-M) / B.lo : ℤ)) : ℝ)) := neg_le_neg h1
    simp only [neg_div, neg_neg] at h2
    have h3 : ((↑(-((-M) / B.lo)) : ℝ)) = -((↑((-M) / B.lo) : ℝ)) := by push_cast; ring
    rw [h3]
    exact h2
  -- the true-value bounds
  have hb_le : b * (2:ℝ)^(B.k) ≤ (B.hi:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right h.2 hbk.le
    calc b * (2:ℝ)^(B.k)
        ≤ ((B.hi:ℝ) * (2:ℝ)^(-(B.k))) * (2:ℝ)^(B.k) := h1
      _ = (B.hi:ℝ) := by
          rw [mul_assoc, ← zpow_add₀ (a := (2:ℝ)) (by norm_num),
            show (-(B.k) + B.k) = 0 by ring, zpow_zero, mul_one]
  have hscale_hi : (2:ℝ)^(B.k) / (B.hi:ℝ) ≤ b⁻¹ := by
    have h1 : (2:ℝ)^(B.k) ≤ b⁻¹ * (B.hi:ℝ) := by
      have h2 : (2:ℝ)^(B.k) * b ≤ (B.hi:ℝ) := by rwa [mul_comm] at hb_le
      calc (2:ℝ)^(B.k) = ((2:ℝ)^(B.k) * b) * b⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hb.ne', mul_one]
        _ ≤ (B.hi:ℝ) * b⁻¹ := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hb.le)
        _ = b⁻¹ * (B.hi:ℝ) := by ring
    exact (div_le_iff₀ hbhi).mpr h1
  have hlo_le : (B.lo:ℝ) ≤ b * (2:ℝ)^(B.k) := by
    have h1 := mul_le_mul_of_nonneg_right h.1 hbk.le
    calc (B.lo:ℝ)
        = ((B.lo:ℝ) * (2:ℝ)^(-(B.k))) * (2:ℝ)^(B.k) := by
          rw [mul_assoc, ← zpow_add₀ (a := (2:ℝ)) (by norm_num),
            show (-(B.k) + B.k) = 0 by ring, zpow_zero, mul_one]
      _ ≤ b * (2:ℝ)^(B.k) := h1
  have hscale_lo : b⁻¹ ≤ (2:ℝ)^(B.k) / (B.lo:ℝ) := by
    have h1 : b⁻¹ * (B.lo:ℝ) ≤ (2:ℝ)^(B.k) := by
      calc b⁻¹ * (B.lo:ℝ) ≤ b⁻¹ * (b * (2:ℝ)^(B.k)) :=
            mul_le_mul_of_nonneg_left hlo_le (inv_nonneg.mpr hb.le)
        _ = (2:ℝ)^(B.k) := by rw [← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]
    exact (le_div_iff₀ hblo).mpr h1
  constructor
  · calc (↑(M / B.hi) : ℝ) * (2:ℝ)^(-((S:ℤ) - B.k))
        ≤ ((M:ℝ) / (B.hi:ℝ)) * (2:ℝ)^(-((S:ℤ) - B.k)) :=
          mul_le_mul_of_nonneg_right hfloor (zpow_pos (by norm_num) _).le
      _ = ((2:ℝ)^(S:ℤ) / (B.hi:ℝ)) * (2:ℝ)^(-((S:ℤ) - B.k)) := by rw [hMpow]
      _ = (2:ℝ)^(B.k) / (B.hi:ℝ) := by rw [div_mul_eq_mul_div, hSpow]
      _ ≤ b⁻¹ := hscale_hi
  · calc b⁻¹ ≤ (2:ℝ)^(B.k) / (B.lo:ℝ) := hscale_lo
      _ = ((2:ℝ)^(S:ℤ) / (B.lo:ℝ)) * (2:ℝ)^(-((S:ℤ) - B.k)) := by
          rw [div_mul_eq_mul_div, hSpow]
      _ = ((M:ℝ) / (B.lo:ℝ)) * (2:ℝ)^(-((S:ℤ) - B.k)) := by rw [hMpow]
      _ ≤ (↑(-((-M) / B.lo)) : ℝ) * (2:ℝ)^(-((S:ℤ) - B.k)) :=
          mul_le_mul_of_nonneg_right hceil (zpow_pos (by norm_num) _).le

#print axioms dInv_mem

/-- Division memory: `dDiv A B = dMul A (dInv B)`. -/
theorem dDiv_mem {A B : DC} {a b : ℝ} (hlo : 0 < B.lo) (hA : A.mem a) (hB : B.mem b) :
    (dDiv A B).mem (a / b) := by
  rw [dDiv, div_eq_mul_inv]
  exact dMul_mem hA (dInv_mem hlo hB)

#print axioms dDiv_mem


end DCKit
end Kepler.Text.TaylorSecond
