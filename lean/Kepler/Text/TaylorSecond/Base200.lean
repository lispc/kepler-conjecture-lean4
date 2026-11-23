import Kepler.Text.TaylorSecond.QInterval
import Mathlib.Tactic.NormNum

namespace Kepler.Text.TaylorSecond

/-- The numeric payload of the exported HOL base-200 ifloat.  The Boolean sign
is kept separately, exactly as in the certificate JSON. -/
structure IFloat200 where
  negative : Bool
  num : ℕ
  exp : ℤ
  minExp : ℕ
  deriving Repr, DecidableEq

namespace IFloat200

/-- Exact rational value `±num · 200^(exp-minExp)`. -/
def value (f : IFloat200) : ℚ :=
  (if f.negative then -(f.num : ℚ) else (f.num : ℚ)) * (200 : ℚ) ^ (f.exp - f.minExp)

/-- Exact rational interval represented by two exported endpoints. -/
def interval (lo hi : IFloat200) : QInterval := ⟨lo.value, hi.value⟩

/-- Exported pp=3 lower endpoint of `D11 = w1F2` on `LRLRLRLRL`. -/
def selectedD11Lo : IFloat200 := ⟨true, 596705, 47, 50⟩

/-- Exported pp=3 upper endpoint of `D11 = w1F2` on `LRLRLRLRL`. -/
def selectedD11Hi : IFloat200 := ⟨true, 101749, 47, 50⟩

theorem selectedD11Lo_value : selectedD11Lo.value = -119341 / 1600000 := by
  norm_num [selectedD11Lo, value, zpow_neg, zpow_ofNat]

theorem selectedD11Hi_value : selectedD11Hi.value = -101749 / 8000000 := by
  norm_num [selectedD11Hi, value, zpow_neg, zpow_ofNat]

theorem selectedD11_interval : interval selectedD11Lo selectedD11Hi =
    ⟨-119341 / 1600000, -101749 / 8000000⟩ := by
  rw [interval, selectedD11Lo_value, selectedD11Hi_value]

theorem selectedD11_upper_lt_zero : (interval selectedD11Lo selectedD11Hi).hi < 0 := by
  rw [selectedD11_interval]
  norm_num

theorem selectedD11_negative_of_mem {x : ℝ}
    (hx : (interval selectedD11Lo selectedD11Hi).mem x) :
    x ≤ -101749 / 8000000 ∧ -101749 / 8000000 < (0 : ℝ) := by
  rw [selectedD11_interval] at hx
  have hu := hx.2
  norm_num at hu
  exact ⟨by simpa only [neg_div] using hu, by norm_num⟩

#print axioms selectedD11Lo_value
#print axioms selectedD11Hi_value
#print axioms selectedD11_interval
#print axioms selectedD11_upper_lt_zero
#print axioms selectedD11_negative_of_mem

end IFloat200
end Kepler.Text.TaylorSecond
