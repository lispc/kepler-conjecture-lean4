import Kepler.Text.TaylorSecond.Arithmetic
import Kepler.Text.TaylorSecond.QInterval

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

variable {n : ℕ}

/-- Lower-triangular Hessian enclosure with exact rational endpoints. -/
def SecondBoundedQ (f : (Fin n → ℝ) → ℝ) (D : Set (Fin n → ℝ))
    (B : Fin n → Fin n → QInterval) : Prop :=
  ∀ x ∈ D, ∀ i j, j ≤ i → (B i j).mem (partial2 j i f x)

/-- A consumable whole-box second-order certificate: C², values, all first
partials, and all lower-triangular second partials on the same box. -/
structure WholeBoxJet (f : (Fin n → ℝ) → ℝ) (D : Set (Fin n → ℝ)) where
  value : QInterval
  first : Fin n → QInterval
  second : Fin n → Fin n → QInterval
  diff2c : Diff2CDomain D f
  value_mem : ∀ x ∈ D, value.mem (f x)
  first_mem : ∀ x ∈ D, ∀ i, (first i).mem (partial1 i f x)
  second_mem : SecondBoundedQ f D second

/-- A unary C² enclosure with explicit names for the first and second derivative. -/
structure UnaryBox (u : ℝ → ℝ) (I : QInterval) where
  firstFun : ℝ → ℝ
  secondFun : ℝ → ℝ
  value : QInterval
  first : QInterval
  second : QInterval
  smooth : ∀ t, I.mem t → ContDiffAt ℝ 2 u t
  first_eq : ∀ t, I.mem t → deriv u t = firstFun t
  second_eq : ∀ t, I.mem t → deriv (deriv u) t = secondFun t
  value_mem : ∀ t, I.mem t → value.mem (u t)
  first_mem : ∀ t, I.mem t → first.mem (firstFun t)
  second_mem : ∀ t, I.mem t → second.mem (secondFun t)

namespace WholeBoxJet

/-- Whole-box second-order addition. -/
noncomputable def add {f g : (Fin n → ℝ) → ℝ} {D : Set (Fin n → ℝ)}
    (F : WholeBoxJet f D) (G : WholeBoxJet g D) : WholeBoxJet (fun x => f x + g x) D where
  value := F.value.add G.value
  first := fun i => (F.first i).add (G.first i)
  second := fun i j => (F.second i j).add (G.second i j)
  diff2c := fun x hx => (F.diff2c x hx).add (G.diff2c x hx)
  value_mem := fun x hx => QInterval.mem_add (F.value_mem x hx) (G.value_mem x hx)
  first_mem := by
    intro x hx i
    have hf1 : ContDiffAt ℝ 1 f x := (F.diff2c x hx).of_le (by norm_num)
    have hg1 : ContDiffAt ℝ 1 g x := (G.diff2c x hx).of_le (by norm_num)
    rw [partial1_add hf1 hg1]
    exact QInterval.mem_add (F.first_mem x hx i) (G.first_mem x hx i)
  second_mem := by
    intro x hx i j hij
    rw [partial2_add (F.diff2c x hx) (G.diff2c x hx)]
    exact QInterval.mem_add (F.second_mem x hx i j hij) (G.second_mem x hx i j hij)

/-- Whole-box second-order subtraction. -/
noncomputable def sub {f g : (Fin n → ℝ) → ℝ} {D : Set (Fin n → ℝ)}
    (F : WholeBoxJet f D) (G : WholeBoxJet g D) : WholeBoxJet (fun x => f x - g x) D where
  value := F.value.sub G.value
  first := fun i => (F.first i).sub (G.first i)
  second := fun i j => (F.second i j).sub (G.second i j)
  diff2c := fun x hx => (F.diff2c x hx).sub (G.diff2c x hx)
  value_mem := fun x hx => QInterval.mem_sub (F.value_mem x hx) (G.value_mem x hx)
  first_mem := by
    intro x hx i
    have hf1 : ContDiffAt ℝ 1 f x := (F.diff2c x hx).of_le (by norm_num)
    have hg1 : ContDiffAt ℝ 1 g x := (G.diff2c x hx).of_le (by norm_num)
    rw [partial1_sub hf1 hg1]
    exact QInterval.mem_sub (F.first_mem x hx i) (G.first_mem x hx i)
  second_mem := by
    intro x hx i j hij
    rw [partial2_sub (F.diff2c x hx) (G.diff2c x hx)]
    exact QInterval.mem_sub (F.second_mem x hx i j hij) (G.second_mem x hx i j hij)

/-- Whole-box second-order multiplication, including both first-order cross terms. -/
noncomputable def mul {f g : (Fin n → ℝ) → ℝ} {D : Set (Fin n → ℝ)}
    (F : WholeBoxJet f D) (G : WholeBoxJet g D) : WholeBoxJet (fun x => f x * g x) D where
  value := F.value.mul G.value
  first := fun i => (F.value.mul (G.first i)).add (G.value.mul (F.first i))
  second := fun i j =>
    ((F.value.mul (G.second i j)).add ((G.first i).mul (F.first j))).add
      ((G.value.mul (F.second i j)).add ((F.first i).mul (G.first j)))
  diff2c := fun x hx => (F.diff2c x hx).mul (G.diff2c x hx)
  value_mem := fun x hx => QInterval.mem_mul (F.value_mem x hx) (G.value_mem x hx)
  first_mem := by
    intro x hx i
    have hf1 : ContDiffAt ℝ 1 f x := (F.diff2c x hx).of_le (by norm_num)
    have hg1 : ContDiffAt ℝ 1 g x := (G.diff2c x hx).of_le (by norm_num)
    rw [partial1_mul hf1 hg1]
    exact QInterval.mem_add
      (QInterval.mem_mul (F.value_mem x hx) (G.first_mem x hx i))
      (QInterval.mem_mul (G.value_mem x hx) (F.first_mem x hx i))
  second_mem := by
    intro x hx i j hij
    rw [partial2_mul (F.diff2c x hx) (G.diff2c x hx)]
    exact QInterval.mem_add
      (QInterval.mem_add
        (QInterval.mem_mul (F.value_mem x hx) (G.second_mem x hx i j hij))
        (QInterval.mem_mul (G.first_mem x hx i) (F.first_mem x hx j)))
      (QInterval.mem_add
        (QInterval.mem_mul (G.value_mem x hx) (F.second_mem x hx i j hij))
        (QInterval.mem_mul (F.first_mem x hx i) (G.first_mem x hx j)))

/-- Whole-box unary C² composition, retaining `u'' f' f' + u' f''`. -/
noncomputable def comp {u : ℝ → ℝ} {f : (Fin n → ℝ) → ℝ} {D : Set (Fin n → ℝ)}
    (F : WholeBoxJet f D) (U : UnaryBox u F.value) : WholeBoxJet (u ∘ f) D where
  value := U.value
  first := fun i => U.first.mul (F.first i)
  second := fun i j =>
    ((U.second.mul (F.first j)).mul (F.first i)).add (U.first.mul (F.second i j))
  diff2c := fun x hx => (U.smooth (f x) (F.value_mem x hx)).comp x (F.diff2c x hx)
  value_mem := fun x hx => U.value_mem (f x) (F.value_mem x hx)
  first_mem := by
    intro x hx i
    have hu1 : ContDiffAt ℝ 1 u (f x) := (U.smooth (f x) (F.value_mem x hx)).of_le (by norm_num)
    have hf1 : ContDiffAt ℝ 1 f x := (F.diff2c x hx).of_le (by norm_num)
    rw [partial1_comp hu1 hf1, U.first_eq (f x) (F.value_mem x hx)]
    exact QInterval.mem_mul (U.first_mem (f x) (F.value_mem x hx)) (F.first_mem x hx i)
  second_mem := by
    intro x hx i j hij
    rw [partial2_comp (U.smooth (f x) (F.value_mem x hx)) (F.diff2c x hx),
      U.first_eq (f x) (F.value_mem x hx), U.second_eq (f x) (F.value_mem x hx)]
    exact QInterval.mem_add
      (QInterval.mem_mul
        (QInterval.mem_mul (U.second_mem (f x) (F.value_mem x hx)) (F.first_mem x hx j))
        (F.first_mem x hx i))
      (QInterval.mem_mul (U.first_mem (f x) (F.value_mem x hx)) (F.second_mem x hx i j hij))

end WholeBoxJet

#print axioms WholeBoxJet.add
#print axioms WholeBoxJet.sub
#print axioms WholeBoxJet.mul
#print axioms WholeBoxJet.comp

end Kepler.Text.TaylorSecond
