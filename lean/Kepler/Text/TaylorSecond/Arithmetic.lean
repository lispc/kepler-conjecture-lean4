import Kepler.Text.TaylorSecond.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic.Ring

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Filter
open scoped Topology

variable {n : ℕ}

/-- First coordinate partial1 of an addition. -/
theorem partial1_add {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) (i : Fin n) :
    partial1 i (fun y => f y + g y) x = partial1 i f x + partial1 i g x := by
  unfold partial1
  rw [fderiv_fun_add (hf.differentiableAt one_ne_zero) (hg.differentiableAt one_ne_zero)]
  rfl

/-- First coordinate partial1 of a subtraction. -/
theorem partial1_sub {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) (i : Fin n) :
    partial1 i (fun y => f y - g y) x = partial1 i f x - partial1 i g x := by
  unfold partial1
  rw [fderiv_fun_sub (hf.differentiableAt one_ne_zero) (hg.differentiableAt one_ne_zero)]
  rfl

/-- First coordinate partial1 of a product. -/
theorem partial1_mul {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) (i : Fin n) :
    partial1 i (fun y => f y * g y) x = f x * partial1 i g x + g x * partial1 i f x := by
  unfold partial1
  rw [fderiv_fun_mul (hf.differentiableAt one_ne_zero) (hg.differentiableAt one_ne_zero)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- First coordinate partial1 of a scalar unary composition. -/
theorem partial1_comp {u : ℝ → ℝ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hu : ContDiffAt ℝ 1 u (f x)) (hf : ContDiffAt ℝ 1 f x) (i : Fin n) :
    partial1 i (u ∘ f) x = deriv u (f x) * partial1 i f x := by
  unfold partial1
  rw [fderiv_comp x (hu.differentiableAt one_ne_zero) (hf.differentiableAt one_ne_zero)]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]

/-- Addition of mixed coordinate second partials. -/
theorem partial2_add {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (j i : Fin n) :
    partial2 j i (fun y => f y + g y) x = partial2 j i f x + partial2 j i g x := by
  have he : (fun y => partial1 i (fun z => f z + g z) y) =ᶠ[𝓝 x]
      (fun y => partial1 i f y + partial1 i g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact partial1_add (hyf.of_le (by norm_num)) (hyg.of_le (by norm_num)) i
  unfold partial2
  rw [he.fderiv_eq, fderiv_fun_add (differentiableAt_partial1 hf i)
    (differentiableAt_partial1 hg i)]
  rfl

/-- Subtraction of mixed coordinate second partials. -/
theorem partial2_sub {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (j i : Fin n) :
    partial2 j i (fun y => f y - g y) x = partial2 j i f x - partial2 j i g x := by
  have he : (fun y => partial1 i (fun z => f z - g z) y) =ᶠ[𝓝 x]
      (fun y => partial1 i f y - partial1 i g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact partial1_sub (hyf.of_le (by norm_num)) (hyg.of_le (by norm_num)) i
  unfold partial2
  rw [he.fderiv_eq, fderiv_fun_sub (differentiableAt_partial1 hf i)
    (differentiableAt_partial1 hg i)]
  rfl

/-- Product rule for mixed coordinate second partials.  The last two summands
are the two first-order cross terms; neither is discarded. -/
theorem partial2_mul {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (j i : Fin n) :
    partial2 j i (fun y => f y * g y) x =
      (f x * partial2 j i g x + partial1 i g x * partial1 j f x) +
        (g x * partial2 j i f x + partial1 i f x * partial1 j g x) := by
  have he : (fun y => partial1 i (fun z => f z * g z) y) =ᶠ[𝓝 x]
      (fun y => f y * partial1 i g y + g y * partial1 i f y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact partial1_mul (hyf.of_le (by norm_num)) (hyg.of_le (by norm_num)) i
  have hdf : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hdfi : DifferentiableAt ℝ (fun y => partial1 i f y) x := differentiableAt_partial1 hf i
  have hdgi : DifferentiableAt ℝ (fun y => partial1 i g y) x := differentiableAt_partial1 hg i
  have hder := (hdf.hasFDerivAt.mul hdgi.hasFDerivAt).add
    (hdg.hasFDerivAt.mul hdfi.hasFDerivAt)
  change HasFDerivAt (fun y => f y * partial1 i g y + g y * partial1 i f y)
    (f x • fderiv ℝ (fun y => partial1 i g y) x + partial1 i g x • fderiv ℝ f x +
      (g x • fderiv ℝ (fun y => partial1 i f y) x + partial1 i f x • fderiv ℝ g x)) x at hder
  unfold partial2
  rw [he.fderiv_eq, hder.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

/-- A `C¹` derivative function is available from a `C²` unary function. -/
theorem contDiffAt_deriv {u : ℝ → ℝ} {t : ℝ} (hu : ContDiffAt ℝ 2 u t) :
    ContDiffAt ℝ 1 (deriv u) t :=
  hu.derivWithin (by norm_num)

/-- Full unary second chain rule `u'' f' f' + u' f''` in coordinate form. -/
theorem partial2_comp {u : ℝ → ℝ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hu : ContDiffAt ℝ 2 u (f x)) (hf : ContDiffAt ℝ 2 f x) (j i : Fin n) :
    partial2 j i (u ∘ f) x =
      (deriv (deriv u) (f x) * partial1 j f x) * partial1 i f x +
        deriv u (f x) * partial2 j i f x := by
  have he : (fun y => partial1 i (u ∘ f) y) =ᶠ[𝓝 x]
      (fun y => deriv u (f y) * partial1 i f y) := by
    filter_upwards [hf.continuousAt (hu.eventually (by norm_num)),
      hf.eventually (by norm_num)] with y hyu hyf
    change ContDiffAt ℝ 2 u (f y) at hyu
    exact partial1_comp (hyu.of_le (by norm_num)) (hyf.of_le (by norm_num)) i
  have hdu : DifferentiableAt ℝ (fun y => deriv u (f y)) x := by
    have h1 : DifferentiableAt ℝ (deriv u) (f x) :=
      (contDiffAt_deriv hu).differentiableAt one_ne_zero
    exact h1.comp x (hf.differentiableAt (by norm_num))
  have hdfi : DifferentiableAt ℝ (fun y => partial1 i f y) x := differentiableAt_partial1 hf i
  have he' : (fun y => deriv u (f y)) =ᶠ[𝓝 x] (deriv u ∘ f) := by
    exact Filter.Eventually.of_forall (fun _ => rfl)
  have hsecond : partial1 j (deriv u ∘ f) x =
      deriv (deriv u) (f x) * partial1 j f x :=
    partial1_comp (contDiffAt_deriv hu) (hf.of_le (by norm_num)) j
  unfold partial2
  rw [he.fderiv_eq, fderiv_fun_mul hdu hdfi]
  change deriv u (f x) * fderiv ℝ (fun y => partial1 i f y) x (coord j) +
    partial1 i f x * fderiv ℝ (fun y => deriv u (f y)) x (coord j) = _
  rw [show fderiv ℝ (fun y => deriv u (f y)) x (coord j) =
    deriv (deriv u) (f x) * partial1 j f x by
      rw [← hsecond]
      apply congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (coord j))
      exact he'.fderiv_eq]
  ring

#print axioms partial1_add
#print axioms partial1_sub
#print axioms partial1_mul
#print axioms partial1_comp
#print axioms partial2_add
#print axioms partial2_sub
#print axioms partial2_mul
#print axioms contDiffAt_deriv
#print axioms partial2_comp

end Kepler.Text.TaylorSecond
