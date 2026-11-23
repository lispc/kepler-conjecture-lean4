import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

private theorem mul_bounds_right {c d y : ℝ} (hc : c ≤ y) (hd : y ≤ d) (m : ℝ) :
    min (c * m) (d * m) ≤ y * m ∧ y * m ≤ max (c * m) (d * m) := by
  rcases le_total 0 m with hm | hm
  · have h1 : c * m ≤ y * m := mul_le_mul_of_nonneg_right hc hm
    have h2 : y * m ≤ d * m := mul_le_mul_of_nonneg_right hd hm
    exact ⟨by rwa [min_eq_left (le_trans h1 h2)], by rwa [max_eq_right (le_trans h1 h2)]⟩
  · have h1 : d * m ≤ y * m := mul_le_mul_of_nonpos_right hd hm
    have h2 : y * m ≤ c * m := mul_le_mul_of_nonpos_right hc hm
    exact ⟨by rwa [min_eq_right (le_trans h1 h2)], by rwa [max_eq_left (le_trans h1 h2)]⟩

private theorem mul_bounds_left {a b x : ℝ} (ha : a ≤ x) (hb : x ≤ b) (m : ℝ) :
    min (m * a) (m * b) ≤ m * x ∧ m * x ≤ max (m * a) (m * b) := by
  have h := mul_bounds_right ha hb m
  rwa [← mul_comm m a, ← mul_comm m b, ← mul_comm m x] at h

private theorem mul_mem_Icc {a b c d x y : ℝ} (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y)
    (hyd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  obtain ⟨hxy1, hxy2⟩ := mul_bounds_left hcy hyd x
  obtain ⟨hxc1, hxc2⟩ := mul_bounds_right hax hxb c
  obtain ⟨hxd1, hxd2⟩ := mul_bounds_right hax hxb d
  refine ⟨le_trans ?_ hxy1, le_trans hxy2 ?_⟩
  · exact le_min
      (le_trans (le_min (le_trans (min_le_left _ _) (min_le_left _ _))
        (le_trans (min_le_right _ _) (min_le_left _ _))) hxc1)
      (le_trans (le_min (le_trans (min_le_left _ _) (min_le_right _ _))
        (le_trans (min_le_right _ _) (min_le_right _ _))) hxd1)
  · exact max_le
      (le_trans hxc2 (max_le (le_trans (le_max_left _ _) (le_max_left _ _))
        (le_trans (le_max_left _ _) (le_max_right _ _))))
      (le_trans hxd2 (max_le (le_trans (le_max_right _ _) (le_max_left _ _))
        (le_trans (le_max_right _ _) (le_max_right _ _))))

/-- An interval with exact rational endpoints, used as an outer bridge for
base-200 certificates whose denominators need not be dyadic. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

namespace QInterval

/-- Real membership in the closed exact-rational interval. -/
def mem (I : QInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- A point interval. -/
def const (q : ℚ) : QInterval := ⟨q, q⟩

/-- Exact interval addition. -/
def add (I J : QInterval) : QInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Exact interval negation. -/
def neg (I : QInterval) : QInterval := ⟨-I.hi, -I.lo⟩

/-- Exact interval subtraction. -/
def sub (I J : QInterval) : QInterval := I.add J.neg

/-- Exact interval multiplication by all four corner products. -/
def mul (I J : QInterval) : QInterval where
  lo := min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
  hi := max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))

/-- Reciprocal endpoints.  Soundness is exported only away from zero. -/
def inv (I : QInterval) : QInterval where
  lo := min I.lo⁻¹ I.hi⁻¹
  hi := max I.lo⁻¹ I.hi⁻¹

/-- Scalar `q` times an interval, through a point interval. -/
def scale (q : ℚ) (I : QInterval) : QInterval := (const q).mul I

/-- HOL's scalar `iabs = max hi (-lo)`, an upper bound for absolute value. -/
def iabs (I : QInterval) : ℚ := max I.hi (-I.lo)

/-- `J` is an exact outer interval of `I`. -/
def Outer (I J : QInterval) : Prop := J.lo ≤ I.lo ∧ I.hi ≤ J.hi

/-- Right-associated interval sum, matching HOL `end_itlist`. -/
def sumRight : List QInterval → QInterval
  | [] => const 0
  | I :: Is => I.add (sumRight Is)

/-- Right-associated real sum consumed by `sumRight_sound`. -/
def sumRightReal : List ℝ → ℝ
  | [] => 0
  | x :: xs => x + sumRightReal xs

theorem mem_const {q : ℚ} : (const q).mem (q : ℝ) := by
  exact ⟨le_rfl, le_rfl⟩

theorem mem_add {I J : QInterval} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (I.add J).mem (x + y) := by
  exact ⟨by simpa only [add, Rat.cast_add] using add_le_add hx.1 hy.1,
    by simpa only [add, Rat.cast_add] using add_le_add hx.2 hy.2⟩

theorem mem_neg {I : QInterval} {x : ℝ} (hx : I.mem x) : I.neg.mem (-x) := by
  exact ⟨by simpa only [neg, Rat.cast_neg] using neg_le_neg hx.2,
    by simpa only [neg, Rat.cast_neg] using neg_le_neg hx.1⟩

theorem mem_sub {I J : QInterval} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (I.sub J).mem (x - y) := by
  rw [sub_eq_add_neg]
  exact mem_add hx (mem_neg hy)

theorem mem_mul {I J : QInterval} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (I.mul J).mem (x * y) := by
  obtain ⟨hlo, hhi⟩ := mul_mem_Icc hx.1 hx.2 hy.1 hy.2
  exact ⟨by simpa only [mul, Rat.cast_min, Rat.cast_mul] using hlo,
    by simpa only [mul, Rat.cast_max, Rat.cast_mul] using hhi⟩

theorem inv_bounds_of_pos {l u x : ℝ} (hl : 0 < l) (hlo : l ≤ x) (hxu : x ≤ u) :
    u⁻¹ ≤ x⁻¹ ∧ x⁻¹ ≤ l⁻¹ := by
  have hx : 0 < x := lt_of_lt_of_le hl hlo
  have hu : 0 < u := lt_of_lt_of_le hx hxu
  exact ⟨inv_anti₀ hx hxu, inv_anti₀ hl hlo⟩

theorem inv_bounds_of_neg {l u x : ℝ} (hu : u < 0) (hlo : l ≤ x) (hxu : x ≤ u) :
    u⁻¹ ≤ x⁻¹ ∧ x⁻¹ ≤ l⁻¹ := by
  have hx : x < 0 := lt_of_le_of_lt hxu hu
  have hl : l < 0 := lt_of_le_of_lt hlo hx
  have h1 := inv_anti₀ (show 0 < -u by linarith) (show -u ≤ -x by linarith)
  have h2 := inv_anti₀ (show 0 < -x by linarith) (show -x ≤ -l by linarith)
  simp only [inv_neg] at h1 h2
  constructor <;> linarith

theorem mem_inv {I : QInterval} {x : ℝ} (hx : I.mem x)
    (h : 0 < I.lo ∨ I.hi < 0) : I.inv.mem x⁻¹ := by
  have hb : (I.hi : ℝ)⁻¹ ≤ x⁻¹ ∧ x⁻¹ ≤ (I.lo : ℝ)⁻¹ := by
    cases h with
    | inl hl =>
        have hl' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hl
        exact inv_bounds_of_pos hl' hx.1 hx.2
    | inr hu =>
        have hu' : (I.hi : ℝ) < 0 := by exact_mod_cast hu
        exact inv_bounds_of_neg hu' hx.1 hx.2
  constructor
  · simp only [inv, Rat.cast_min, Rat.cast_inv]
    exact le_trans (min_le_right _ _) hb.1
  · simp only [inv, Rat.cast_max, Rat.cast_inv]
    exact le_trans hb.2 (le_max_left _ _)

theorem mem_scale {I : QInterval} {q : ℚ} {x : ℝ} (hx : I.mem x) :
    (scale q I).mem ((q : ℝ) * x) := by
  exact mem_mul (mem_const (q := q)) hx

theorem abs_le_iabs {I : QInterval} {x : ℝ} (hx : I.mem x) : |x| ≤ (I.iabs : ℝ) := by
  have h1 : (I.hi : ℝ) ≤ max (I.hi : ℝ) (-(I.lo : ℝ)) := le_max_left _ _
  have h2 : (-(I.lo : ℝ)) ≤ max (I.hi : ℝ) (-(I.lo : ℝ)) := le_max_right _ _
  rcases hx with ⟨hx1, hx2⟩
  rw [iabs, Rat.cast_max, Rat.cast_neg]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem mem_of_outer {I J : QInterval} {x : ℝ} (h : Outer I J) (hx : I.mem x) :
    J.mem x := by
  have hlo : (J.lo : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast h.1
  have hhi : (I.hi : ℝ) ≤ (J.hi : ℝ) := by exact_mod_cast h.2
  exact ⟨le_trans hlo hx.1, le_trans hx.2 hhi⟩

theorem lt_zero_of_upper_lt {I : QInterval} {x : ℝ} (hx : I.mem x)
    (h : I.hi < 0) : x < 0 := by
  have h' : (I.hi : ℝ) < 0 := by exact_mod_cast h
  exact lt_of_le_of_lt hx.2 h'

theorem neg_of_upper_nonpos_and_lt {I : QInterval} {x : ℝ} (hx : I.mem x)
    (h0 : I.hi ≤ 0) (h : I.hi < 0) : x ≤ (I.hi : ℝ) ∧ (I.hi : ℝ) < 0 := by
  exact ⟨hx.2, by exact_mod_cast h⟩

theorem sumRight_sound : ∀ {Is : List QInterval} {xs : List ℝ},
    List.Forall₂ (fun I x => I.mem x) Is xs → (sumRight Is).mem (sumRightReal xs)
  | [], [], _ => by
      exact ⟨by norm_num [sumRight, sumRightReal, mem, const],
        by norm_num [sumRight, sumRightReal, mem, const]⟩
  | I :: Is, x :: xs, h => by
      cases h with
      | cons hhead htail => exact mem_add hhead (sumRight_sound htail)

#print axioms mem_const
#print axioms mem_add
#print axioms mem_neg
#print axioms mem_sub
#print axioms mem_mul
#print axioms inv_bounds_of_pos
#print axioms inv_bounds_of_neg
#print axioms mem_inv
#print axioms mem_scale
#print axioms abs_le_iabs
#print axioms mem_of_outer
#print axioms lt_zero_of_upper_lt
#print axioms neg_of_upper_nonpos_and_lt
#print axioms sumRight_sound

end QInterval
end Kepler.Text.TaylorSecond
