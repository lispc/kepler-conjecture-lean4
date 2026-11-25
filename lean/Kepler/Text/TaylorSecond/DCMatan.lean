/-
Kepler.Text.TaylorSecond.DCMatan — lane `wt1-emission-pilot-w1`, M1
(2026-11-25).  `DCKit` is **frozen** (M0, landed); everything new lives here.

Contents
  1. local rational constants (1/2, 1/4, 1/7, 1/9, 1/11) + `_mem`
  2. Route-E gating predicates `dLoGt` / `dHiLt` / `dLoBig` (verbatim data
     level, `Bool`) + soundness into ℝ
  3. `dJoin` (lower end from one DC, upper end from another) + `mem`
  4. `dClamp0` / `dSqrtCore` / `dSqrt` + `dSqrt_mem`  (outward, Nat shifts only)

No `axiom` / `sorry` / `admit` / `native_decide`.
-/
import Kepler.Text.TaylorSecond.DCKit
import Kepler.Text.TaylorSecond.LeafKitPrec
import Kepler.Text.Wt1TowerKit

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

namespace DCMatan

open DCKit

/-! ## 1. Local constants -/

/-- `1/2`. -/
def HALF : DC := dInv (dInt 2)

/-- `1/4`. -/
def QUARTER : DC := dInv (dInt 4)

/-- `1/7`. -/
def SEVENTH : DC := dInv (dInt 7)

/-- `1/9`. -/
def NINTH : DC := dInv (dInt 9)

/-- `1/11`. -/
def ELEVENTH : DC := dInv (dInt 11)

theorem HALF_mem : HALF.mem ((2:ℝ)⁻¹) := by
  have h := dInv_mem (B := dInt 2) (b := (2:ℝ)) (by decide) (dInt_mem 2)
  simpa [HALF] using h

theorem QUARTER_mem : QUARTER.mem ((4:ℝ)⁻¹) := by
  have h := dInv_mem (B := dInt 4) (b := (4:ℝ)) (by decide) (dInt_mem 4)
  simpa [QUARTER] using h

theorem SEVENTH_mem : SEVENTH.mem ((7:ℝ)⁻¹) := by
  have h := dInv_mem (B := dInt 7) (b := (7:ℝ)) (by decide) (dInt_mem 7)
  simpa [SEVENTH] using h

theorem NINTH_mem : NINTH.mem ((9:ℝ)⁻¹) := by
  have h := dInv_mem (B := dInt 9) (b := (9:ℝ)) (by decide) (dInt_mem 9)
  simpa [NINTH] using h

theorem ELEVENTH_mem : ELEVENTH.mem ((11:ℝ)⁻¹) := by
  have h := dInv_mem (B := dInt 11) (b := (11:ℝ)) (by decide) (dInt_mem 11)
  simpa [ELEVENTH] using h

theorem THIRD_mem : THIRD.mem ((3:ℝ)⁻¹) := by
  have h := dInv_mem (B := dInt 3) (b := (3:ℝ)) (by decide) (dInt_mem 3)
  simpa [THIRD] using h

theorem FIFTH_mem : FIFTH.mem ((5:ℝ)⁻¹) := by
  have h := dInv_mem (B := dInt 5) (b := (5:ℝ)) (by decide) (dInt_mem 5)
  simpa [FIFTH] using h

/-! ## 2. Route-E gates (verbatim data level) -/

/-- `X`'s lower end exceeds `Y`'s lower end — common scale, exact shifts. -/
def dLoGt (X Y : DC) : Bool :=
  let kk := max X.k Y.k
  (X.lo <<< (kk - X.k)) > (Y.lo <<< (kk - Y.k))

/-- `X`'s upper end is below `Y`'s upper end — common scale. -/
def dHiLt (X Y : DC) : Bool :=
  let kk := max X.k Y.k
  (X.hi <<< (kk - X.k)) < (Y.hi <<< (kk - Y.k))

/-- `value(A.lo) ≥ 2^(-100)` — the magnitude floor of Route E. -/
def dLoBig (A : DC) : Bool :=
  if A.k ≥ 100 then ((1 : ℤ) <<< (A.k - 100)) ≤ A.lo else A.lo > 0

/-- Shifting a nonnegative ℤ amount: `(x <<< (kk - k)) · 2^(-kk) = x · 2^(-k)`. -/
theorem shiftLeft_mul_zpow {x : ℤ} {k kk : ℤ} (h : k ≤ kk) :
    ((x <<< (kk - k) : ℤ) : ℝ) * (2:ℝ)^(-kk) = (x:ℝ) * (2:ℝ)^(-k) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = kk - k :=
    ⟨(kk - k).toNat, Int.toNat_of_nonneg (by linarith)⟩
  rw [← hd, shiftLeft_eq_mul]
  push_cast
  rw [← zpow_natCast (2:ℝ) d, mul_assoc,
    ← zpow_add₀ (a := (2:ℝ)) (by norm_num)]
  congr 1
  have hexp : ((d:ℤ) + -kk) = -k := by rw [hd]; ring
  rw [hexp]

/-- Gate soundness: `dLoGt X Y = true` means `Y.lo < X.lo` as real values. -/
theorem dLoGt_sound {X Y : DC} (h : dLoGt X Y = true) :
    (Y.lo : ℝ) * (2:ℝ)^(-(Y.k)) < (X.lo : ℝ) * (2:ℝ)^(-(X.k)) := by
  simp only [dLoGt] at h
  have hlt : (Y.lo <<< (max X.k Y.k - Y.k)) < (X.lo <<< (max X.k Y.k - X.k)) :=
    of_decide_eq_true h
  have hX : X.k ≤ max X.k Y.k := le_max_left _ _
  have hY : Y.k ≤ max X.k Y.k := le_max_right _ _
  have hcast : ((Y.lo <<< (max X.k Y.k - Y.k) : ℤ) : ℝ)
      < ((X.lo <<< (max X.k Y.k - X.k) : ℤ) : ℝ) := by exact_mod_cast hlt
  have hpos : (0:ℝ) < (2:ℝ)^(-(max X.k Y.k)) := zpow_pos (by norm_num) _
  have := mul_lt_mul_of_pos_right hcast hpos
  rwa [shiftLeft_mul_zpow hY, shiftLeft_mul_zpow hX] at this

/-- Gate soundness: `dHiLt X Y = true` means `X.hi < Y.hi` as real values. -/
theorem dHiLt_sound {X Y : DC} (h : dHiLt X Y = true) :
    (X.hi : ℝ) * (2:ℝ)^(-(X.k)) < (Y.hi : ℝ) * (2:ℝ)^(-(Y.k)) := by
  simp only [dHiLt] at h
  have hlt : (X.hi <<< (max X.k Y.k - X.k)) < (Y.hi <<< (max X.k Y.k - Y.k)) :=
    of_decide_eq_true h
  have hX : X.k ≤ max X.k Y.k := le_max_left _ _
  have hY : Y.k ≤ max X.k Y.k := le_max_right _ _
  have hcast : ((X.hi <<< (max X.k Y.k - X.k) : ℤ) : ℝ)
      < ((Y.hi <<< (max X.k Y.k - Y.k) : ℤ) : ℝ) := by exact_mod_cast hlt
  have hpos : (0:ℝ) < (2:ℝ)^(-(max X.k Y.k)) := zpow_pos (by norm_num) _
  have := mul_lt_mul_of_pos_right hcast hpos
  rwa [shiftLeft_mul_zpow hX, shiftLeft_mul_zpow hY] at this

/-- `(1 : ℤ) <<< d > 0` for `d ≥ 0`. -/
theorem shiftLeft_one_pos {d : ℤ} (hd : 0 ≤ d) : (0:ℤ) < (1:ℤ) <<< d := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = d := ⟨d.toNat, Int.toNat_of_nonneg hd⟩
  rw [← hn, shiftLeft_eq_mul]
  have : (0:ℤ) < 2 ^ n := by positivity
  simpa using this

/-- Gate soundness: `dLoBig A = true` means the lower end is a positive real. -/
theorem dLoBig_sound {A : DC} (h : dLoBig A = true) : (0:ℝ) < (A.lo : ℝ) := by
  simp only [dLoBig] at h
  split at h
  · rename_i hk
    have h2 : (1 : ℤ) <<< (A.k - 100) ≤ A.lo := of_decide_eq_true h
    have h3 : (0:ℤ) < (1 : ℤ) <<< (A.k - 100) := shiftLeft_one_pos (by linarith)
    have h6 : ((1 : ℤ) <<< (A.k - 100) : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast h2
    have h4 : (0:ℝ) < ((1 : ℤ) <<< (A.k - 100) : ℝ) := by exact_mod_cast h3
    linarith
  · exact_mod_cast of_decide_eq_true h

/-! ## 3. Join -/

/-- `dJoin L H`: lower end from `L`, upper end from `H` (common scale). -/
def dJoin (L H : DC) : DC :=
  ⟨max L.k H.k, L.lo <<< (max L.k H.k - L.k), H.hi <<< (max L.k H.k - H.k)⟩

theorem dJoin_mem {L H : DC} {x y z : ℝ} (hL : L.mem x) (hH : H.mem y)
    (hxz : x ≤ z) (hzy : z ≤ y) : (dJoin L H).mem z := by
  have hLk : L.k ≤ max L.k H.k := le_max_left _ _
  have hHk : H.k ≤ max L.k H.k := le_max_right _ _
  have h1 : ((L.lo <<< (max L.k H.k - L.k) : ℤ) : ℝ) * (2:ℝ)^(-(max L.k H.k))
      = (L.lo : ℝ) * (2:ℝ)^(-(L.k)) := shiftLeft_mul_zpow hLk
  have h2 : ((H.hi <<< (max L.k H.k - H.k) : ℤ) : ℝ) * (2:ℝ)^(-(max L.k H.k))
      = (H.hi : ℝ) * (2:ℝ)^(-(H.k)) := shiftLeft_mul_zpow hHk
  rw [dJoin, DC.mem_mk]
  simp only [h1, h2]
  exact ⟨le_trans hL.1 hxz, le_trans hzy hH.2⟩

/-! ## 4. Outward dyadic square root -/

/-- Clamp the lower mantissa at `0` (negative lower ends become `0`). -/
def dClamp0 (A : DC) : DC := ⟨A.k, max A.lo 0, A.hi⟩

theorem dClamp0_mem {A : DC} {a : ℝ} (h : A.mem a) (ha : 0 ≤ a) :
    (dClamp0 A).mem a := by
  rw [DC.mem_mk] at h
  rw [dClamp0, DC.mem_mk]
  have hk : (0:ℝ) < (2:ℝ)^(-(A.k)) := zpow_pos (by norm_num) _
  push_cast
  refine ⟨?_, h.2⟩
  by_cases hl : (0:ℤ) ≤ A.lo
  · have hl' : (0:ℝ) ≤ (A.lo:ℝ) := by exact_mod_cast hl
    rw [max_eq_left hl']
    exact h.1
  · have hl' : (A.lo:ℝ) ≤ 0 := by
      have h0 : A.lo ≤ 0 := le_of_lt (not_le.mp hl)
      exact_mod_cast h0
    rw [max_eq_right hl', zero_mul]
    exact ha

/-- Outward dyadic square root of a **nonnegative** dyadic interval:
`K = ⌈(k+200)/2⌉` (mantissa shift `2K − k ∈ {200, 201}`), `Nat.sqrt` both ends,
upper end `+ 1`. -/
def dSqrtCore (A : DC) : DC :=
  ⟨(A.k + 201) / 2,
    (Nat.sqrt (A.lo <<< (2 * ((A.k + 201) / 2) - A.k).toNat).toNat : ℤ),
    (Nat.sqrt (A.hi <<< (2 * ((A.k + 201) / 2) - A.k).toNat).toNat : ℤ) + 1⟩

/-- The outward square root with the negative part clamped to `0`. -/
def dSqrt (A : DC) : DC := dSqrtCore (dClamp0 A)

/-- `⌈(k+200)/2⌉` gives `2K − k ∈ {200, 201}`. -/
theorem sqrtK_bounds (k : ℤ) :
    200 ≤ 2 * ((k + 201) / 2) - k ∧ 2 * ((k + 201) / 2) - k ≤ 201 := by
  have h1 : (k + 201) / 2 * 2 ≤ k + 201 := Int.ediv_mul_le (k + 201) (by norm_num)
  have h2 : k + 201 < ((k + 201) / 2 + 1) * 2 :=
    Int.lt_ediv_add_one_mul_self (k + 201) (by norm_num)
  constructor <;> linarith

/-- **Scaling identity for the outward sqrt**: with `d = 2K − k` the real value
`isqrt(x · 2^d) · 2^(-K)` sits at the scale of `√(x · 2^(-k))`. -/
theorem sqrt_shift_scale {x : ℤ} {k K : ℤ} {d : ℕ} (hx : 0 ≤ x)
    (hd : (d:ℤ) = 2 * K - k) :
    Real.sqrt ((x <<< d : ℤ) : ℝ) * (2:ℝ)^(-K)
      = Real.sqrt ((x:ℝ) * (2:ℝ)^(-k)) := by
  have hxZ : (0:ℝ) ≤ ((x <<< d : ℤ) : ℝ) := by
    have h2 : (0:ℤ) ≤ x <<< d := by
      rw [← Int.shiftLeft_natCast_right, shiftLeft_eq_mul]
      exact mul_nonneg hx (by positivity)
    exact_mod_cast h2
  have hcast : ((x <<< d : ℤ) : ℝ) = (x:ℝ) * (2:ℝ)^(d:ℤ) := by
    rw [← Int.shiftLeft_natCast_right, shiftLeft_eq_mul]
    push_cast
    rw [← zpow_natCast (2:ℝ) d]
  have h2 : ((2:ℝ)^(-K))^2 = (2:ℝ)^(-2*K) := by
    rw [sq, ← zpow_add₀ (a := (2:ℝ)) (by norm_num)]
    congr 1
    ring
  rw [← Real.sqrt_sq (zpow_pos (by norm_num) (-K)).le, ← Real.sqrt_mul hxZ]
  congr 1
  rw [hcast, h2, mul_assoc, ← zpow_add₀ (a := (2:ℝ)) (by norm_num)]
  congr 1
  rw [hd]
  ring

/-- `dSqrtCore` is sound on a nonnegative interval. -/
theorem dSqrtCore_mem {A : DC} {a : ℝ} (hlo : (0:ℝ) ≤ (A.lo : ℝ))
    (hhi : (0:ℝ) ≤ (A.hi : ℝ)) (h : A.mem a) : (dSqrtCore A).mem (Real.sqrt a) := by
  obtain ⟨hK1, hK2⟩ := sqrtK_bounds A.k
  rw [dSqrtCore, DC.mem_mk]
  push_cast
  set K : ℤ := (A.k + 201) / 2 with hK
  set d : ℕ := (2 * K - A.k).toNat with hddef
  have hdd : (d:ℤ) = 2 * K - A.k := Int.toNat_of_nonneg (by linarith)
  have hloZ : (0:ℤ) ≤ A.lo := by exact_mod_cast hlo
  have hhiZ : (0:ℤ) ≤ A.hi := by exact_mod_cast hhi
  have hloS : (0:ℤ) ≤ A.lo <<< d := by
    rw [← Int.shiftLeft_natCast_right, shiftLeft_eq_mul]
    exact mul_nonneg hloZ (by positivity)
  have hhiS : (0:ℤ) ≤ A.hi <<< d := by
    rw [← Int.shiftLeft_natCast_right, shiftLeft_eq_mul]
    exact mul_nonneg hhiZ (by positivity)
  constructor
  · have h1 : ((Nat.sqrt (A.lo <<< d).toNat : ℕ) : ℝ)
        ≤ Real.sqrt ((A.lo <<< d : ℤ) : ℝ) := by
      have hnat : Nat.sqrt (A.lo <<< d).toNat * Nat.sqrt (A.lo <<< d).toNat
          ≤ (A.lo <<< d).toNat := Nat.sqrt_le _
      have hnat' : ((Nat.sqrt (A.lo <<< d).toNat : ℕ) : ℝ)
          * ((Nat.sqrt (A.lo <<< d).toNat : ℕ) : ℝ)
          ≤ (((A.lo <<< d).toNat : ℕ) : ℝ) := by exact_mod_cast hnat
      have hcast2 : (((A.lo <<< d).toNat : ℕ) : ℝ) = ((A.lo <<< d : ℤ) : ℝ) := by
        have h := Int.toNat_of_nonneg hloS
        exact_mod_cast h
      rw [hcast2] at hnat'
      refine Real.le_sqrt_of_sq_le ?_
      rwa [sq]
    calc ((Nat.sqrt (A.lo <<< d).toNat : ℕ) : ℝ) * (2:ℝ)^(-K)
        ≤ Real.sqrt ((A.lo <<< d : ℤ) : ℝ) * (2:ℝ)^(-K) :=
          mul_le_mul_of_nonneg_right h1 (zpow_pos (by norm_num) _).le
      _ = Real.sqrt ((A.lo:ℝ) * (2:ℝ)^(-(A.k))) := sqrt_shift_scale hloZ hdd
      _ ≤ Real.sqrt a := Real.sqrt_le_sqrt h.1
  · have h0 : (0:ℝ) ≤ (2:ℝ)^(-K) := (zpow_pos (by norm_num) _).le
    have hlt : Real.sqrt ((A.hi <<< d : ℤ) : ℝ)
        < ((Nat.sqrt (A.hi <<< d).toNat : ℕ) : ℝ) + 1 := by
      have hnat : (A.hi <<< d).toNat < (Nat.sqrt (A.hi <<< d).toNat + 1) ^ 2 := by
        simpa using Nat.lt_succ_sqrt' (A.hi <<< d).toNat
      have h1r : Real.sqrt (((A.hi <<< d).toNat : ℕ) : ℝ)
          < ((Nat.sqrt (A.hi <<< d).toNat : ℕ) : ℝ) + 1 := by
        have hcast2 : (((Nat.sqrt (A.hi <<< d).toNat + 1) ^ 2 : ℕ) : ℝ)
            = (((Nat.sqrt (A.hi <<< d).toNat : ℕ) : ℝ) + 1) ^ 2 := by push_cast; ring
        calc Real.sqrt (((A.hi <<< d).toNat : ℕ) : ℝ)
            < Real.sqrt ((((Nat.sqrt (A.hi <<< d).toNat + 1) ^ 2 : ℕ) : ℝ)) := by
              rw [hcast2]
              exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hnat)
          _ = ((Nat.sqrt (A.hi <<< d).toNat : ℕ) : ℝ) + 1 := by
              rw [hcast2, Real.sqrt_sq (by positivity)]
      have hcast3 : (((A.hi <<< d).toNat : ℕ) : ℝ) = ((A.hi <<< d : ℤ) : ℝ) := by
        have h := Int.toNat_of_nonneg hhiS
        exact_mod_cast h
      rwa [hcast3] at h1r
    have hstep : Real.sqrt ((A.hi:ℝ) * (2:ℝ)^(-(A.k)))
        ≤ (((Nat.sqrt (A.hi <<< d).toNat : ℕ) : ℝ) + 1) * (2:ℝ)^(-K) := by
      have h1 := mul_le_mul_of_nonneg_right hlt.le h0
      rw [sqrt_shift_scale hhiZ hdd] at h1
      exact h1
    exact le_trans (Real.sqrt_le_sqrt h.2) hstep

/-- `dSqrt` is sound: `0 ≤ a`, `A.mem a` ⟹ `(dSqrt A).mem (√a)`. -/
theorem dSqrt_mem {A : DC} {a : ℝ} (ha : 0 ≤ a) (h : A.mem a) :
    (dSqrt A).mem (Real.sqrt a) := by
  have hk : (0:ℝ) < (2:ℝ)^(-(A.k)) := zpow_pos (by norm_num) _
  have hB := dClamp0_mem h ha
  have hlo : (0:ℝ) ≤ ((dClamp0 A).lo : ℝ) := by
    rw [dClamp0]
    dsimp only
    push_cast
    exact le_max_right _ _
  have hhi : (0:ℝ) ≤ ((dClamp0 A).hi : ℝ) := by
    rw [dClamp0]
    dsimp only
    have h1 : (0:ℝ) ≤ (A.hi:ℝ) * (2:ℝ)^(-(A.k)) := le_trans ha hB.2
    exact nonneg_of_mul_nonneg_left h1 hk
  exact dSqrtCore_mem hlo hhi hB

/-! ## 5. Polynomial brackets (Horner in DC) -/

theorem ONE_mem : ONE.mem (1:ℝ) := by
  have h := dInt_mem 1
  simpa [ONE] using h

/-- `π` bracket at `k = 40` (Route E literal): `PIbr.mem π`. -/
theorem PIbr_mem : PIbr.mem Real.pi := by
  rw [PIbr, DC.mem_mk]
  have h2 : (2:ℝ)^(-(40:ℤ)) = 1/1099511627776 := by norm_num [zpow_neg, zpow_natCast]
  refine ⟨?_, ?_⟩
  · have h := Real.pi_gt_d20
    have h' : ((3454217652357:ℤ) : ℝ) * (2:ℝ)^(-(40:ℤ)) < 3.14159265358979323846 := by
      rw [h2]; norm_num
    exact (h'.trans h).le
  · have h := Real.pi_lt_d20
    have h' : 3.14159265358979323847 < ((3454217652358:ℤ) : ℝ) * (2:ℝ)^(-(40:ℤ)) := by
      rw [h2]; norm_num
    exact (h.trans h').le

/-- Horner form of `1 − r/3 + r²/5 − r³/7 + r⁴/9 − r⁵/11`. -/
noncomputable def P9f (r : ℝ) : ℝ :=
  1 + r * (-(1/3) + r * (1/5 + r * (-(1/7) + r * (1/9 + r * (-(1/11))))))

/-- Horner form of `1 − r/3 + r²/5 − r³/7 + r⁴/9`. -/
noncomputable def A9f (r : ℝ) : ℝ :=
  1 + r * (-(1/3) + r * (1/5 + r * (-(1/7) + r * (1/9))))

/-- Horner form of `1 − r/3 + r²/5 − r³/7`. -/
noncomputable def A7f (r : ℝ) : ℝ :=
  1 + r * (-(1/3) + r * (1/5 + r * (-(1/7))))

/-- Horner form of `1 − r/3 + r²/5`. -/
noncomputable def A5f (r : ℝ) : ℝ :=
  1 + r * (-(1/3) + r * (1/5))

theorem P9f_eq (r : ℝ) : P9f r = 1 - r/3 + r^2/5 - r^3/7 + r^4/9 - r^5/11 := by
  simp only [P9f]; ring

theorem A9f_eq (r : ℝ) : A9f r = 1 - r/3 + r^2/5 - r^3/7 + r^4/9 := by
  simp only [A9f]; ring

theorem A7f_eq (r : ℝ) : A7f r = 1 - r/3 + r^2/5 - r^3/7 := by
  simp only [A7f]; ring

theorem A5f_eq (r : ℝ) : A5f r = 1 - r/3 + r^2/5 := by
  simp only [A5f]; ring

/-- DC Horner evaluation of `P9f`. -/
def evalP9 (A : DC) : DC :=
  dAdd ONE (dMul A (dAdd (dNeg THIRD) (dMul A (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH)
    (dMul A (dAdd NINTH (dMul A (dNeg ELEVENTH))))))))))

/-- DC Horner evaluation of `A9f`. -/
def evalA9 (A : DC) : DC :=
  dAdd ONE (dMul A (dAdd (dNeg THIRD) (dMul A (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH)
    (dMul A NINTH)))))))

/-- DC Horner evaluation of `A7f`. -/
def evalA7 (A : DC) : DC :=
  dAdd ONE (dMul A (dAdd (dNeg THIRD) (dMul A (dAdd FIFTH (dMul A (dNeg SEVENTH))))))

/-- DC Horner evaluation of `A5f`. -/
def evalA5 (A : DC) : DC :=
  dAdd ONE (dMul A (dAdd (dNeg THIRD) (dMul A FIFTH)))

theorem evalP9_mem {A : DC} {r : ℝ} (hA : A.mem r) : (evalP9 A).mem (P9f r) := by
  have h11 : (dMul A (dNeg ELEVENTH)).mem (r * (-(1/11))) :=
    dMul_mem hA (by simpa [one_div] using dNeg_mem ELEVENTH_mem)
  have h9 : (dAdd NINTH (dMul A (dNeg ELEVENTH))).mem (1/9 + r * (-(1/11))) :=
    dAdd_mem (by simpa [one_div] using NINTH_mem) h11
  have h8 : (dMul A (dAdd NINTH (dMul A (dNeg ELEVENTH)))).mem
      (r * (1/9 + r * (-(1/11)))) := dMul_mem hA h9
  have h7 : (dAdd (dNeg SEVENTH) (dMul A (dAdd NINTH (dMul A (dNeg ELEVENTH))))).mem
      (-(1/7) + r * (1/9 + r * (-(1/11)))) :=
    dAdd_mem (by simpa [one_div] using dNeg_mem SEVENTH_mem) h8
  have h6 : (dMul A (dAdd (dNeg SEVENTH) (dMul A (dAdd NINTH (dMul A (dNeg ELEVENTH)))))).mem
      (r * (-(1/7) + r * (1/9 + r * (-(1/11))))) := dMul_mem hA h7
  have h5 : (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH) (dMul A (dAdd NINTH
      (dMul A (dNeg ELEVENTH))))))).mem
      (1/5 + r * (-(1/7) + r * (1/9 + r * (-(1/11))))) :=
    dAdd_mem (by simpa [one_div] using FIFTH_mem) h6
  have h4 : (dMul A (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH) (dMul A (dAdd NINTH
      (dMul A (dNeg ELEVENTH)))))))).mem
      (r * (1/5 + r * (-(1/7) + r * (1/9 + r * (-(1/11)))))) := dMul_mem hA h5
  have h3 : (dAdd (dNeg THIRD) (dMul A (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH)
      (dMul A (dAdd NINTH (dMul A (dNeg ELEVENTH))))))))).mem
      (-(1/3) + r * (1/5 + r * (-(1/7) + r * (1/9 + r * (-(1/11)))))) :=
    dAdd_mem (by simpa [one_div] using dNeg_mem THIRD_mem) h4
  have h2 : (dMul A (dAdd (dNeg THIRD) (dMul A (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH)
      (dMul A (dAdd NINTH (dMul A (dNeg ELEVENTH)))))))))).mem
      (r * (-(1/3) + r * (1/5 + r * (-(1/7) + r * (1/9 + r * (-(1/11))))))) := dMul_mem hA h3
  have h1 := dAdd_mem ONE_mem h2
  simpa [evalP9, P9f] using h1

theorem evalA9_mem {A : DC} {r : ℝ} (hA : A.mem r) : (evalA9 A).mem (A9f r) := by
  have h9 : (dMul A NINTH).mem (r * (1/9)) := dMul_mem hA (by simpa [one_div] using NINTH_mem)
  have h7 : (dAdd (dNeg SEVENTH) (dMul A NINTH)).mem (-(1/7) + r * (1/9)) :=
    dAdd_mem (by simpa [one_div] using dNeg_mem SEVENTH_mem) h9
  have h6 : (dMul A (dAdd (dNeg SEVENTH) (dMul A NINTH))).mem
      (r * (-(1/7) + r * (1/9))) := dMul_mem hA h7
  have h5 : (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH) (dMul A NINTH)))).mem
      (1/5 + r * (-(1/7) + r * (1/9))) := dAdd_mem (by simpa [one_div] using FIFTH_mem) h6
  have h4 : (dMul A (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH) (dMul A NINTH))))).mem
      (r * (1/5 + r * (-(1/7) + r * (1/9)))) := dMul_mem hA h5
  have h3 : (dAdd (dNeg THIRD) (dMul A (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH)
      (dMul A NINTH)))))).mem (-(1/3) + r * (1/5 + r * (-(1/7) + r * (1/9)))) :=
    dAdd_mem (by simpa [one_div] using dNeg_mem THIRD_mem) h4
  have h2 : (dMul A (dAdd (dNeg THIRD) (dMul A (dAdd FIFTH (dMul A (dAdd (dNeg SEVENTH)
      (dMul A NINTH))))))).mem (r * (-(1/3) + r * (1/5 + r * (-(1/7) + r * (1/9))))) :=
    dMul_mem hA h3
  have h1 := dAdd_mem ONE_mem h2
  simpa [evalA9, A9f] using h1

theorem evalA7_mem {A : DC} {r : ℝ} (hA : A.mem r) : (evalA7 A).mem (A7f r) := by
  have h7 : (dMul A (dNeg SEVENTH)).mem (r * (-(1/7))) :=
    dMul_mem hA (by simpa [one_div] using dNeg_mem SEVENTH_mem)
  have h5 : (dAdd FIFTH (dMul A (dNeg SEVENTH))).mem (1/5 + r * (-(1/7))) :=
    dAdd_mem (by simpa [one_div] using FIFTH_mem) h7
  have h4 : (dMul A (dAdd FIFTH (dMul A (dNeg SEVENTH)))).mem
      (r * (1/5 + r * (-(1/7)))) := dMul_mem hA h5
  have h3 : (dAdd (dNeg THIRD) (dMul A (dAdd FIFTH (dMul A (dNeg SEVENTH))))).mem
      (-(1/3) + r * (1/5 + r * (-(1/7)))) :=
    dAdd_mem (by simpa [one_div] using dNeg_mem THIRD_mem) h4
  have h2 : (dMul A (dAdd (dNeg THIRD) (dMul A (dAdd FIFTH (dMul A (dNeg SEVENTH)))))).mem
      (r * (-(1/3) + r * (1/5 + r * (-(1/7))))) := dMul_mem hA h3
  have h1 := dAdd_mem ONE_mem h2
  simpa [evalA7, A7f] using h1

theorem evalA5_mem {A : DC} {r : ℝ} (hA : A.mem r) : (evalA5 A).mem (A5f r) := by
  have h5 : (dMul A FIFTH).mem (r * (1/5)) := dMul_mem hA (by simpa [one_div] using FIFTH_mem)
  have h3 : (dAdd (dNeg THIRD) (dMul A FIFTH)).mem (-(1/3) + r * (1/5)) :=
    dAdd_mem (by simpa [one_div] using dNeg_mem THIRD_mem) h5
  have h2 : (dMul A (dAdd (dNeg THIRD) (dMul A FIFTH))).mem (r * (-(1/3) + r * (1/5))) :=
    dMul_mem hA h3
  have h1 := dAdd_mem ONE_mem h2
  simpa [evalA5, A5f] using h1

/-! ## 6. The four tight arms -/

/-- **Direct arm** (order 9/11): sound for every `r > 0`; width `r⁵/11 ≤ 1e-6`
on the branch `r ≤ 0.1019`. -/
def dMatan9 (A : DC) : DC := dJoin (evalP9 A) (evalA9 A)

/-- Pointwise direct bracket (mirror of `lk_matan_direct9`, at real `r`). -/
theorem matan_direct9_real {r : ℝ} (hr : 0 < r) :
    1 - r/3 + r^2/5 - r^3/7 + r^4/9 - r^5/11 ≤ matan r ∧
      matan r ≤ 1 - r/3 + r^2/5 - r^3/7 + r^4/9 := by
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hme := lk_matan_eq hr
  have s0 : (0:ℝ) ≤ Real.sqrt r := Real.sqrt_nonneg _
  have hlo := lk_atan_ge_b11 s0
  have hhi := lk_atan_le_a9 s0
  simp only [lkB11, lkA9] at hlo hhi
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
  rw [hme]
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hr), div_le_iff₀ (Real.sqrt_pos.mpr hr)]
  constructor <;> nlinarith [hlo, hhi, hr.le]

theorem dMatan9_mem {A : DC} {r : ℝ} (hA : A.mem r) (hbig : dLoBig A = true) :
    (dMatan9 A).mem (matan r) := by
  have hr : 0 < r :=
    lt_of_lt_of_le (mul_pos (dLoBig_sound hbig) (zpow_pos (by norm_num : (0:ℝ) < 2) (-(A.k)))) hA.1
  obtain ⟨h1, h2⟩ := matan_direct9_real hr
  refine dJoin_mem (evalP9_mem hA) (evalA9_mem hA) ?_ ?_
  · rw [P9f_eq]; exact h1
  · rw [A9f_eq]; exact h2

/-- **w-form arm**: for `1 < r` with `s = √r`, `w = (s−1)/(s+1)`,
`matan r ∈ [(π/4 + A7(w))/s, (π/4 + A5(w))/s]`
(mirror of `lk_matan_wplus`). -/
def dMatanWp (A : DC) : DC :=
  let W := dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE)
  let W2 := dMul W W
  let X := dAdd (dMul QUARTER PIbr) (dMul W (evalA7 W2))
  let Y := dAdd (dMul QUARTER PIbr) (dMul W (evalA5 W2))
  dJoin (dDiv X (dSqrt A)) (dDiv Y (dSqrt A))

/-- Pointwise w-form bracket (mirror of `lk_matan_wplus`; the landed lemma
brackets `arctan` by the *series* `lkA7`/`lkA5` in `w`). -/
theorem matan_wplus_real {r : ℝ} (hr : 1 < r) :
    (Real.pi/4 + lkA7 ((Real.sqrt r - 1)/(Real.sqrt r + 1))) / Real.sqrt r ≤ matan r ∧
      matan r ≤ (Real.pi/4 + lkA5 ((Real.sqrt r - 1)/(Real.sqrt r + 1))) / Real.sqrt r := by
  have hr0 : 0 < r := by linarith
  have hs : 1 < Real.sqrt r := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hr
    rwa [Real.sqrt_one] at h
  have hs0 : (0:ℝ) < Real.sqrt r := by linarith
  have hw0 : (0:ℝ) ≤ (Real.sqrt r - 1)/(Real.sqrt r + 1) :=
    div_nonneg (by linarith) (by linarith)
  have hweq : matan r = (Real.pi/4 + Real.arctan ((Real.sqrt r - 1)/(Real.sqrt r + 1)))
      / Real.sqrt r := by
    rw [lk_matan_eq hr0, lk_arctan_wplus hs]
  have h7 := lk_atan_ge_a7 hw0
  have h5 := lk_atan_le_a5 hw0
  rw [hweq]
  exact ⟨div_le_div_of_nonneg_right (by linarith) hs0.le,
    div_le_div_of_nonneg_right (by linarith) hs0.le⟩

/-- `dSqrt A`'s lower mantissa is positive when `A` passes `dLoBig`. -/
theorem dSqrt_lo_pos {A : DC} (hbig : dLoBig A = true) : 0 < (dSqrt A).lo := by
  have hlo : (0:ℤ) < A.lo := by exact_mod_cast dLoBig_sound hbig
  have hmax : max A.lo 0 = A.lo := max_eq_left hlo.le
  have hBlo : (0:ℤ) < (dClamp0 A).lo := by
    rw [dClamp0]; dsimp only; rwa [hmax]
  set d : ℕ := (2 * (((dClamp0 A).k + 201) / 2) - (dClamp0 A).k).toNat with hd
  have h1 : (0:ℤ) < (dClamp0 A).lo <<< d := by
    rw [← Int.shiftLeft_natCast_right, shiftLeft_eq_mul]
    have h2 : (1:ℤ) ≤ 2 ^ d := by
      have := pow_pos (by norm_num : (0:ℤ) < 2) d
      omega
    have h3 : (1:ℤ) ≤ (dClamp0 A).lo := by omega
    calc (0:ℤ) < 1 := by norm_num
      _ ≤ (dClamp0 A).lo * 2 ^ d := by
          calc (1:ℤ) = 1 * 1 := by ring
            _ ≤ (dClamp0 A).lo * 2 ^ d := mul_le_mul h3 h2 (by norm_num) (by linarith)
  have hl : (0:ℤ) < (dClamp0 A).lo <<< d := h1
  have hp : 0 < ((dClamp0 A).lo <<< d).toNat := by
    have hne : ((dClamp0 A).lo <<< d).toNat ≠ 0 := by
      intro hz
      have h4 : ((dClamp0 A).lo <<< d) = 0 := by
        rw [← Int.toNat_of_nonneg (le_of_lt hl)]
        exact_mod_cast hz
      omega
    exact Nat.pos_of_ne_zero hne
  have hs : 0 < Nat.sqrt ((dClamp0 A).lo <<< d).toNat := Nat.sqrt_pos.mpr hp
  rw [dSqrt, dSqrtCore]
  dsimp only
  exact_mod_cast hs

theorem dMatanWp_mem {A : DC} {r : ℝ} (hA : A.mem r) (hbig : dLoBig A = true)
    (h1 : dLoGt A ONE = true) (hden : dLoBig (dAdd (dSqrt A) ONE) = true) :
    (dMatanWp A).mem (matan r) := by
  have hr : 0 < r :=
    lt_of_lt_of_le (mul_pos (dLoBig_sound hbig) (zpow_pos (by norm_num : (0:ℝ) < 2) (-(A.k)))) hA.1
  have hr1 : 1 < r := by
    have h := dLoGt_sound h1
    have hone : (ONE.lo : ℝ) * (2:ℝ)^(-(ONE.k)) = 1 := by
      simp [ONE, dInt]
    rw [hone] at h
    exact lt_of_lt_of_le h hA.1
  have hSQ : (dSqrt A).mem (Real.sqrt r) := dSqrt_mem hr.le hA
  have hSQ0 : (0:ℤ) < (dSqrt A).lo := dSqrt_lo_pos hbig
  have hd0 : (0:ℤ) < (dAdd (dSqrt A) ONE).lo := by exact_mod_cast dLoBig_sound hden
  have hnum : (dSub (dSqrt A) ONE).mem (Real.sqrt r - 1) := dSub_mem hSQ ONE_mem
  have hdenm : (dAdd (dSqrt A) ONE).mem (Real.sqrt r + 1) := dAdd_mem hSQ ONE_mem
  have hW : (dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE)).mem
      ((Real.sqrt r - 1)/(Real.sqrt r + 1)) := dDiv_mem hd0 hnum hdenm
  have hW2 : (dMul (dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE))
      (dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE))).mem
      (((Real.sqrt r - 1)/(Real.sqrt r + 1)) * ((Real.sqrt r - 1)/(Real.sqrt r + 1))) :=
    dMul_mem hW hW
  have hX : (dMul QUARTER PIbr).mem ((4:ℝ)⁻¹ * Real.pi) := dMul_mem QUARTER_mem PIbr_mem
  have h7 : (dMul (dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE))
      (evalA7 (dMul (dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE))
        (dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE))))).mem
      (lkA7 ((Real.sqrt r - 1)/(Real.sqrt r + 1))) := by
    have h := dMul_mem hW (evalA7_mem hW2)
    convert h using 1
    simp only [lkA7, A7f]
    ring
  have h5 : (dMul (dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE))
      (evalA5 (dMul (dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE))
        (dDiv (dSub (dSqrt A) ONE) (dAdd (dSqrt A) ONE))))).mem
      (lkA5 ((Real.sqrt r - 1)/(Real.sqrt r + 1))) := by
    have h := dMul_mem hW (evalA5_mem hW2)
    convert h using 1
    simp only [lkA5, A5f]
    ring
  have hloArm := dDiv_mem hSQ0 (dAdd_mem hX h7) hSQ
  have hhiArm := dDiv_mem hSQ0 (dAdd_mem hX h5) hSQ
  obtain ⟨hz1, hz2⟩ := matan_wplus_real hr1
  have hq1 : (4:ℝ)⁻¹ * Real.pi = Real.pi / 4 := by ring
  have hq1' : ((4:ℝ)⁻¹ * Real.pi + lkA7 ((Real.sqrt r - 1)/(Real.sqrt r + 1)))/Real.sqrt r
      = (Real.pi/4 + lkA7 ((Real.sqrt r - 1)/(Real.sqrt r + 1)))/Real.sqrt r := by rw [hq1]
  have hq2' : ((4:ℝ)⁻¹ * Real.pi + lkA5 ((Real.sqrt r - 1)/(Real.sqrt r + 1)))/Real.sqrt r
      = (Real.pi/4 + lkA5 ((Real.sqrt r - 1)/(Real.sqrt r + 1)))/Real.sqrt r := by rw [hq1]
  rw [hq1'] at hloArm
  rw [hq2'] at hhiArm
  exact dJoin_mem hloArm hhiArm hz1 hz2

/-- **u-form arm**: sound for every `r > 0` with `s = √r`,
`matan r ∈ [(π/2 − A9(1/s))/s, (π/2 − B11(1/s))/s]`
(mirror of `lk_matan_u9`). -/
def dMatanU9 (A : DC) : DC :=
  let SQ := dSqrt A
  let R := dInv SQ
  let R2 := dMul R R
  let X := dSub (dMul HALF PIbr) (dMul R (evalA9 R2))
  let Y := dSub (dMul HALF PIbr) (dMul R (evalP9 R2))
  dJoin (dDiv X SQ) (dDiv Y SQ)

/-- Pointwise u-form bracket (mirror of `lk_matan_u9`). -/
theorem matan_u9_real {r : ℝ} (hr : 0 < r) :
    (Real.pi/2 - lkA9 (1/Real.sqrt r)) / Real.sqrt r ≤ matan r ∧
      matan r ≤ (Real.pi/2 - lkB11 (1/Real.sqrt r)) / Real.sqrt r := by
  have hs0 : (0:ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hr
  have h1s : (0:ℝ) ≤ 1/Real.sqrt r := by positivity
  have hweq : matan r = (Real.pi/2 - Real.arctan (1/Real.sqrt r)) / Real.sqrt r := by
    rw [lk_matan_eq hr, lk_arctan_inv hs0]
  have h9 := lk_atan_le_a9 h1s
  have h11 := lk_atan_ge_b11 h1s
  rw [hweq]
  exact ⟨div_le_div_of_nonneg_right (by linarith) hs0.le,
    div_le_div_of_nonneg_right (by linarith) hs0.le⟩

theorem dMatanU9_mem {A : DC} {r : ℝ} (hA : A.mem r) (hbig : dLoBig A = true) :
    (dMatanU9 A).mem (matan r) := by
  have hr : 0 < r :=
    lt_of_lt_of_le (mul_pos (dLoBig_sound hbig) (zpow_pos (by norm_num : (0:ℝ) < 2) (-(A.k)))) hA.1
  have hSQ : (dSqrt A).mem (Real.sqrt r) := dSqrt_mem hr.le hA
  have hSQ0 : (0:ℤ) < (dSqrt A).lo := dSqrt_lo_pos hbig
  have hR : (dInv (dSqrt A)).mem ((Real.sqrt r)⁻¹) := dInv_mem hSQ0 hSQ
  have hR2 : (dMul (dInv (dSqrt A)) (dInv (dSqrt A))).mem
      ((Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹) := dMul_mem hR hR
  have hX : (dMul HALF PIbr).mem ((2:ℝ)⁻¹ * Real.pi) := dMul_mem HALF_mem PIbr_mem
  have h9 : (dMul (dInv (dSqrt A)) (evalA9 (dMul (dInv (dSqrt A)) (dInv (dSqrt A))))).mem
      (lkA9 (1/Real.sqrt r)) := by
    have h := dMul_mem hR (evalA9_mem hR2)
    convert h using 1
    rw [show (Real.sqrt r)⁻¹ = 1/Real.sqrt r by rw [one_div]]
    simp only [lkA9, A9f]
    ring
  have h11 : (dMul (dInv (dSqrt A)) (evalP9 (dMul (dInv (dSqrt A)) (dInv (dSqrt A))))).mem
      (lkB11 (1/Real.sqrt r)) := by
    have h := dMul_mem hR (evalP9_mem hR2)
    convert h using 1
    rw [show (Real.sqrt r)⁻¹ = 1/Real.sqrt r by rw [one_div]]
    simp only [lkB11, lkA9, P9f]
    ring
  have hloArm := dDiv_mem hSQ0 (dSub_mem hX h9) hSQ
  have hhiArm := dDiv_mem hSQ0 (dSub_mem hX h11) hSQ
  obtain ⟨hz1, hz2⟩ := matan_u9_real hr
  have hq1 : (2:ℝ)⁻¹ * Real.pi = Real.pi / 2 := by ring
  have hq1' : ((2:ℝ)⁻¹ * Real.pi - lkA9 (1/Real.sqrt r))/Real.sqrt r
      = (Real.pi/2 - lkA9 (1/Real.sqrt r))/Real.sqrt r := by rw [hq1]
  have hq2' : ((2:ℝ)⁻¹ * Real.pi - lkB11 (1/Real.sqrt r))/Real.sqrt r
      = (Real.pi/2 - lkB11 (1/Real.sqrt r))/Real.sqrt r := by rw [hq1]
  rw [hq1'] at hloArm
  rw [hq2'] at hhiArm
  exact dJoin_mem hloArm hhiArm hz1 hz2

/-- **Mirror arm**: `matan r = π/(2√r) − matan(1/r)/r`.  The inner bracket
`Minner.mem (matan (1/r))` is supplied by the caller (coarse `matanBr` arms —
**no recursion**). -/
def dMatanMir (A Minner : DC) : DC :=
  dSub (dDiv (dMul HALF PIbr) (dSqrt A)) (dDiv Minner A)

theorem dMatanMir_mem {A Minner : DC} {r : ℝ} (hA : A.mem r)
    (hMinner : Minner.mem (matan (1/r))) (hbig : dLoBig A = true) :
    (dMatanMir A Minner).mem (matan r) := by
  have hr : 0 < r :=
    lt_of_lt_of_le (mul_pos (dLoBig_sound hbig) (zpow_pos (by norm_num : (0:ℝ) < 2) (-(A.k)))) hA.1
  have hA0 : (0:ℤ) < A.lo := by exact_mod_cast dLoBig_sound hbig
  have hSQ : (dSqrt A).mem (Real.sqrt r) := dSqrt_mem hr.le hA
  have hSQ0 : (0:ℤ) < (dSqrt A).lo := dSqrt_lo_pos hbig
  have hnum : (dMul HALF PIbr).mem ((2:ℝ)⁻¹ * Real.pi) := dMul_mem HALF_mem PIbr_mem
  have h1 : (dDiv (dMul HALF PIbr) (dSqrt A)).mem ((2:ℝ)⁻¹ * Real.pi / Real.sqrt r) :=
    dDiv_mem hSQ0 hnum hSQ
  have h2 : (dDiv Minner A).mem (matan (1/r) / r) := dDiv_mem hA0 hMinner hA
  have h3 := dSub_mem h1 h2
  rw [dMatanMir]
  convert h3 using 1
  rw [lk_matan_mirror hr, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-! ## 7. `matanD`: the derivative bracket -/

/-- **`matan`'s derivative in the DC division form**: for `r > 0`,
`deriv matan r = (1/(1+r) − matan r)/(2r)` (from the landed
`matan_hasDerivAt` + `matanD_of_ne`). -/
theorem matan_deriv_eq {r : ℝ} (hr : 0 < r) :
    deriv matan r = (1/(1+r) - matan r)/(2*r) := by
  rw [(matan_hasDerivAt (by linarith : -1 < r)).deriv, matanD_of_ne (ne_of_gt hr)]
  rw [one_div, one_div, div_eq_mul_inv]
  ring

/-- `dMatanD A Mv : DC` — the derivative bracket `(1/(1+r) − matan r)/(2r)`,
built from the interval `A ∋ r` and the value bracket `Mv ∋ matan r`. -/
def dMatanD (A Mv : DC) : DC :=
  dDiv (dSub (dInv (dAdd ONE A)) Mv) (dMul (dInt 2) A)

theorem dMatanD_mem {A Mv : DC} {r : ℝ} (hA : A.mem r) (hMv : Mv.mem (matan r))
    (hbig : dLoBig A = true) (hden1 : dLoBig (dAdd ONE A) = true)
    (hden2 : dLoBig (dMul (dInt 2) A) = true) :
    (dMatanD A Mv).mem (deriv matan r) := by
  have hr : 0 < r :=
    lt_of_lt_of_le (mul_pos (dLoBig_sound hbig) (zpow_pos (by norm_num : (0:ℝ) < 2) (-(A.k)))) hA.1
  have h1 : (0:ℤ) < (dAdd ONE A).lo := by exact_mod_cast dLoBig_sound hden1
  have h2 : (0:ℤ) < (dMul (dInt 2) A).lo := by exact_mod_cast dLoBig_sound hden2
  have hinv : (dInv (dAdd ONE A)).mem (1/(1+r)) := by
    have h := dInv_mem h1 (dAdd_mem ONE_mem hA)
    simpa [one_div] using h
  have hsub := dSub_mem hinv hMv
  have htwo : (dMul (dInt 2) A).mem (2*r) := by
    have h := dMul_mem (dInt_mem 2) hA
    convert h using 1
    push_cast
    ring
  have h := dDiv_mem h2 hsub htwo
  rw [matan_deriv_eq hr]
  exact h

#print axioms matan_deriv_eq
#print axioms dMatanD_mem
#print axioms shiftLeft_mul_zpow
#print axioms dLoGt_sound
#print axioms dHiLt_sound
#print axioms dLoBig_sound
#print axioms dJoin_mem
#print axioms dClamp0_mem
#print axioms sqrtK_bounds
#print axioms sqrt_shift_scale
#print axioms dSqrtCore_mem
#print axioms dSqrt_mem
#print axioms THIRD_mem
#print axioms FIFTH_mem
#print axioms ONE_mem
#print axioms PIbr_mem
#print axioms P9f_eq
#print axioms A9f_eq
#print axioms evalP9_mem
#print axioms evalA9_mem
#print axioms evalA7_mem
#print axioms evalA5_mem
#print axioms matan_direct9_real
#print axioms dMatan9_mem
#print axioms matan_wplus_real
#print axioms dSqrt_lo_pos
#print axioms dMatanWp_mem
#print axioms matan_u9_real
#print axioms dMatanU9_mem
#print axioms dMatanMir_mem

end DCMatan
end Kepler.Text.TaylorSecond
