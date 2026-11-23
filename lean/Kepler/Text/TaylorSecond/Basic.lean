import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Filter
open scoped Topology

variable {n : ℕ}

/-- The `i`-th coordinate vector in a finite real coordinate space. -/
noncomputable def coord (i : Fin n) : (Fin n → ℝ) := Pi.single i 1

/-- Coordinate partial1 derivative, in the same order as HOL `partial1 i f x`. -/
noncomputable def partial1 (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (coord i)

/-- Mixed coordinate partial1 `∂_j (∂_i f)`, in the same order as HOL `partial2 j i f`. -/
noncomputable def partial2 (j i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ (fun y => partial1 i f y) x (coord j)

/-- A closed coordinate box. -/
def Box (lo hi : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (lo i) (hi i)}

/-- Whole-box `C²`: every box point has a neighborhood on which `f` is twice
continuously differentiable.  This is the Lean counterpart of `diff2c_domain`. -/
def Diff2CDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (f : E → ℝ) : Prop :=
  ∀ x ∈ D, ContDiffAt ℝ 2 f x

/-- Whole-box lower-triangular Hessian enclosure.  Only `j ≤ i` is quantified,
so in dimension three this contains exactly the six HOL `second_bounded` facts. -/
def SecondBounded (f : (Fin n → ℝ) → ℝ) (D : Set (Fin n → ℝ))
    (B : Fin n → Fin n → ℝ × ℝ) : Prop :=
  ∀ x ∈ D, ∀ i j, j ≤ i → partial2 j i f x ∈ Set.Icc (B i j).1 (B i j).2

/-- A symmetric three-dimensional matrix assembled from its six lower-triangular entries. -/
def hessian3 (d00 d10 d11 d20 d21 d22 : ℝ × ℝ) : Fin 3 → Fin 3 → ℝ × ℝ :=
  ![![d00, d10, d20], ![d10, d11, d21], ![d20, d21, d22]]

/-- The derivative of `f` is `C¹` after evaluating it at a fixed coordinate. -/
theorem contDiffAt_partial1 {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (i : Fin n) :
    ContDiffAt ℝ 1 (fun y => partial1 i f y) x := by
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

/-- In particular every first coordinate partial1 is differentiable. -/
theorem differentiableAt_partial1 {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (i : Fin n) :
    DifferentiableAt ℝ (fun y => partial1 i f y) x :=
  (contDiffAt_partial1 hf i).differentiableAt one_ne_zero

/-- Identify the coordinate Hessian with the bundled second Fréchet derivative. -/
theorem partial2_eq_fderiv_fderiv {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (j i : Fin n) :
    partial2 j i f x = fderiv ℝ (fderiv ℝ f) x (coord j) (coord i) := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h := fderiv_clm_apply hc (differentiableAt_const (c := coord i))
  have happ := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (coord j)) h
  simpa only [partial2, partial1, fderiv_const_apply, Pi.zero_apply, zero_apply, map_zero,
    ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, zero_add] using happ

/-- C² gives continuity of every mixed coordinate second partial. -/
theorem continuousAt_partial2 {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (j i : Fin n) :
    ContinuousAt (fun y => partial2 j i f y) x := by
  have h := (contDiffAt_partial1 hf i).continuousAt_fderiv one_ne_zero
  exact h.clm_apply continuousAt_const

/-- C² mixed-partial1 symmetry, transported to the HOL coordinate order. -/
theorem partial2_comm {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (j i : Fin n) :
    partial2 j i f x = partial2 i j f x := by
  rw [partial2_eq_fderiv_fderiv hf, partial2_eq_fderiv_fderiv hf]
  exact hf.isSymmSndFDerivAt (by norm_num [minSmoothness]) (coord j) (coord i)

/-- The four fields of a whole-box second-order Taylor input. -/
structure MTaylorInterval (f : (Fin n → ℝ) → ℝ) (D : Set (Fin n → ℝ))
    (center width : Fin n → ℝ) (value : ℝ × ℝ)
    (first : Fin n → ℝ × ℝ) (second : Fin n → Fin n → ℝ × ℝ) where
  center_mem : center ∈ D
  width_bound : ∀ x ∈ D, ∀ i, |x i - center i| ≤ width i
  value_bound : f center ∈ Set.Icc value.1 value.2
  first_bound : ∀ i, partial1 i f center ∈ Set.Icc (first i).1 (first i).2
  diff2c : Diff2CDomain D f
  second : SecondBounded f D second

/-- Constructor for the six genuine lower-triangular bounds in dimension three. -/
theorem secondBounded3_intro {f : (Fin 3 → ℝ) → ℝ} {D : Set (Fin 3 → ℝ)}
    {d00 d10 d11 d20 d21 d22 : ℝ × ℝ}
    (h00 : ∀ x ∈ D, partial2 0 0 f x ∈ Set.Icc d00.1 d00.2)
    (h10 : ∀ x ∈ D, partial2 0 1 f x ∈ Set.Icc d10.1 d10.2)
    (h11 : ∀ x ∈ D, partial2 1 1 f x ∈ Set.Icc d11.1 d11.2)
    (h20 : ∀ x ∈ D, partial2 0 2 f x ∈ Set.Icc d20.1 d20.2)
    (h21 : ∀ x ∈ D, partial2 1 2 f x ∈ Set.Icc d21.1 d21.2)
    (h22 : ∀ x ∈ D, partial2 2 2 f x ∈ Set.Icc d22.1 d22.2) :
    SecondBounded f D (hessian3 d00 d10 d11 d20 d21 d22) := by
  intro x hx i j hij
  fin_cases i <;> fin_cases j
  · simpa [hessian3] using h00 x hx
  · norm_num at hij
  · norm_num at hij
  · simpa [hessian3] using h10 x hx
  · simpa [hessian3] using h11 x hx
  · exact ((by decide : ¬ (2 : Fin 3) ≤ 1) hij).elim
  · simpa [hessian3] using h20 x hx
  · simpa [hessian3] using h21 x hx
  · simpa [hessian3] using h22 x hx

#print axioms contDiffAt_partial1
#print axioms differentiableAt_partial1
#print axioms partial2_eq_fderiv_fderiv
#print axioms continuousAt_partial2
#print axioms partial2_comm
#print axioms secondBounded3_intro

end Kepler.Text.TaylorSecond
