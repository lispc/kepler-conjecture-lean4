/-
Kepler.NliBanks14 — lane `xspace-deriv-kit`, part 2: **x-space chain rule for
`solEulerXDivSqrtdelta`** (work order §2 item 2, the `solEuler` family).

`solEulerXDivSqrtdelta x = matan (Δ / (4 a²)) / a` with
`a = eulerAX x` the Euler `eulerA_x` body.  This file

* names `a` (`eulerAX`) and proves the definitional unfolding
  (`nb14_solEuler_eq`);
* gives the six partials `deltaXx1 … deltaXx6` of `deltaX`
  (`deltaX4` in `SphereKit` is *proved* to be `deltaXx4`, see
  `nb14_deltaXx4_eq_deltaX4`) and the six partials `eulerAXx1 … eulerAXx6`;
* proves `HasDerivAt` of the one-variable slices of `deltaX` (`deltaXxi`) and
  `eulerAX` (`eulerAXxi`) in all six coordinates;
* packages the reusable chain rule `nb14_hasDerivAt_matan_div` and uses it for
  the six `solEulerXDivSqrtdelta` slices, with derivative `solEulerDx`.

The *sign* of these derivatives on a box is a separate (interval) obligation and
is **not** claimed here.  The `dih`/`ldih` twins (`dihXDivSqrtdeltaPosbranch`,
`ldihXDivSqrtdeltaPosbranch`) follow the same pattern with
`u = 4x₁Δ/Δ₄²`, `v = Δ₄/√(4x₁)` and are *not* in this file.

No `axiom` / `sorry` / `admit` / `native_decide`; audit at the tail.
-/
import Kepler.NliBanks13

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.NliBanks14
open Kepler.Text
open Kepler.NliBanks12
open Kepler.NliBanks13
open Filter
open scoped Topology

/-! ## 1. `a` as a named def -/

/-- HOL `eulerA_x` (sphere.hl:830-833), the `a` of `sol_euler_x_div_sqrtdelta`. -/
noncomputable def eulerAX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
    Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2

/-- Unfolding: `solEulerXDivSqrtdelta = matan (Δ/(4a²))/a`. -/
theorem nb14_solEuler_eq (x1 x2 x3 x4 x5 x6 : ℝ) :
    solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 =
      matan (deltaX x1 x2 x3 x4 x5 x6 / (4 * eulerAX x1 x2 x3 x4 x5 x6 ^ 2)) /
        eulerAX x1 x2 x3 x4 x5 x6 := by
  simp only [solEulerXDivSqrtdelta, eulerAX]

/-! ## 2. Partial derivatives of `deltaX` (polynomial) -/

/-- `∂deltaX/∂x1`. -/
def deltaXx1 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x4 * (-x1 + x2 + x3 - x4 + x5 + x6) - x1 * x4 + x2 * x5 + x3 * x6 - x3 * x5 - x2 * x6

/-- `∂deltaX/∂x2`. -/
def deltaXx2 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 + x5 * (x1 - x2 + x3 + x4 - x5 + x6) - x2 * x5 + x3 * x6 - x3 * x4 - x1 * x6

/-- `∂deltaX/∂x3`. -/
def deltaXx3 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 + x2 * x5 + x6 * (x1 + x2 - x3 + x4 + x5 - x6) - x3 * x6 - x2 * x4 - x1 * x5

/-- `∂deltaX/∂x4`. -/
def deltaXx4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * (-x1 + x2 + x3 - x4 + x5 + x6) - x1 * x4 + x2 * x5 + x3 * x6 - x2 * x3 - x5 * x6

/-- `∂deltaX/∂x5`. -/
def deltaXx5 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 + x2 * (x1 - x2 + x3 + x4 - x5 + x6) - x2 * x5 + x3 * x6 - x1 * x3 - x4 * x6

/-- `∂deltaX/∂x6`. -/
def deltaXx6 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 + x2 * x5 + x3 * (x1 + x2 - x3 + x4 + x5 - x6) - x3 * x6 - x1 * x2 - x4 * x5

/-- Cross-check against `SphereKit`: `deltaX4` **is** `∂deltaX/∂x4`. -/
theorem nb14_deltaXx4_eq_deltaX4 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaXx4 x1 x2 x3 x4 x5 x6 = deltaX4 x1 x2 x3 x4 x5 x6 := by
  unfold deltaXx4 deltaX4; ring

/-! ## 3. Generic one-variable derivative shapes -/

/-- `A t² + B t + C` has derivative `2 A x + B`. -/
theorem nb14_hasDerivAt_quad {x A B C : ℝ} :
    HasDerivAt (fun t : ℝ => A * t ^ 2 + B * t + C) (2 * A * x + B) x := by
  have h1 : HasDerivAt (fun t : ℝ => A * t ^ 2) (A * (2 * x ^ 1)) x :=
    (hasDerivAt_pow 2 x).const_mul A
  have h2 : HasDerivAt (fun t : ℝ => B * t) B x := by
    simpa using (hasDerivAt_id x).const_mul B
  have h3 := (h1.add h2).add_const C
  refine h3.congr_deriv ?_
  ring

/-- Derivative of a function that agrees with a quadratic. -/
theorem nb14_hasDerivAt_of_quad {f : ℝ → ℝ} {x A B C : ℝ}
    (hfun : ∀ t, f t = A * t ^ 2 + B * t + C) :
    HasDerivAt f (2 * A * x + B) x := by
  have h := nb14_hasDerivAt_quad (x := x) (A := A) (B := B) (C := C)
  rw [show f = fun t => A * t ^ 2 + B * t + C from funext hfun]
  exact h

/-- `K √t + L t + C` has derivative `K/(2√x) + L` for `x > 0`. -/
theorem nb14_hasDerivAt_sqrtLin {x K L C : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => K * Real.sqrt t + L * t + C) (K / (2 * Real.sqrt x) + L) x := by
  have hs : HasDerivAt (fun t : ℝ => K * Real.sqrt t) (K * (1 / (2 * Real.sqrt x))) x :=
    (Real.hasDerivAt_sqrt (ne_of_gt hx)).const_mul K
  have hl : HasDerivAt (fun t : ℝ => L * t) L x := by
    simpa using (hasDerivAt_id x).const_mul L
  have h := (hs.add hl).add_const C
  refine h.congr_deriv ?_
  ring

/-- `L t + C` has derivative `L`. -/
theorem nb14_hasDerivAt_lin {x L C : ℝ} :
    HasDerivAt (fun t : ℝ => L * t + C) L x := by
  have h := ((hasDerivAt_id x).const_mul L).add_const C
  refine h.congr_deriv ?_
  ring

/-- Derivative of a function that agrees with an affine function. -/
theorem nb14_hasDerivAt_of_lin {f : ℝ → ℝ} {x L C : ℝ}
    (hfun : ∀ t, f t = L * t + C) : HasDerivAt f L x := by
  have h := nb14_hasDerivAt_lin (x := x) (L := L) (C := C)
  rw [show f = fun t => L * t + C from funext hfun]
  exact h

/-! ## 4. `HasDerivAt` for the six coordinate slices of `deltaX` -/

theorem nb14_hasDerivAt_deltaX1 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t : ℝ => deltaX t x2 x3 x4 x5 x6) (deltaXx1 x1 x2 x3 x4 x5 x6) x1 := by
  have h := nb14_hasDerivAt_of_quad (f := fun t : ℝ => deltaX t x2 x3 x4 x5 x6) (x := x1)
    (A := -x4)
    (B := x4 * (x2 + x3 - x4 + x5 + x6) + x2 * x5 + x3 * x6 - x3 * x5 - x2 * x6)
    (C := x2 * x5 * (-x2 + x3 + x4 - x5 + x6) + x3 * x6 * (x2 - x3 + x4 + x5 - x6) -
      x2 * x3 * x4 - x4 * x5 * x6)
    (fun t => by unfold deltaX; ring)
  refine h.congr_deriv ?_
  unfold deltaXx1; ring

theorem nb14_hasDerivAt_deltaX2 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t : ℝ => deltaX x1 t x3 x4 x5 x6) (deltaXx2 x1 x2 x3 x4 x5 x6) x2 := by
  have h := nb14_hasDerivAt_of_quad (f := fun t : ℝ => deltaX x1 t x3 x4 x5 x6) (x := x2)
    (A := -x5)
    (B := x5 * (x1 + x3 + x4 - x5 + x6) + x1 * x4 + x3 * x6 - x3 * x4 - x1 * x6)
    (C := x1 * x4 * (-x1 + x3 - x4 + x5 + x6) + x3 * x6 * (x1 - x3 + x4 + x5 - x6) -
      x1 * x3 * x5 - x4 * x5 * x6)
    (fun t => by unfold deltaX; ring)
  refine h.congr_deriv ?_
  unfold deltaXx2; ring

theorem nb14_hasDerivAt_deltaX3 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t : ℝ => deltaX x1 x2 t x4 x5 x6) (deltaXx3 x1 x2 x3 x4 x5 x6) x3 := by
  have h := nb14_hasDerivAt_of_quad (f := fun t : ℝ => deltaX x1 x2 t x4 x5 x6) (x := x3)
    (A := -x6)
    (B := x6 * (x1 + x2 + x4 + x5 - x6) + x1 * x4 + x2 * x5 - x2 * x4 - x1 * x5)
    (C := x1 * x4 * (-x1 + x2 - x4 + x5 + x6) + x2 * x5 * (x1 - x2 + x4 - x5 + x6) -
      x1 * x2 * x6 - x4 * x5 * x6)
    (fun t => by unfold deltaX; ring)
  refine h.congr_deriv ?_
  unfold deltaXx3; ring

theorem nb14_hasDerivAt_deltaX4 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t : ℝ => deltaX x1 x2 x3 t x5 x6) (deltaXx4 x1 x2 x3 x4 x5 x6) x4 := by
  have h := nb14_hasDerivAt_of_quad (f := fun t : ℝ => deltaX x1 x2 x3 t x5 x6) (x := x4)
    (A := -x1)
    (B := x1 * (-x1 + x2 + x3 + x5 + x6) + x2 * x5 + x3 * x6 - x2 * x3 - x5 * x6)
    (C := x2 * x5 * (x1 - x2 + x3 - x5 + x6) + x3 * x6 * (x1 + x2 - x3 + x5 - x6) -
      x1 * x3 * x5 - x1 * x2 * x6)
    (fun t => by unfold deltaX; ring)
  refine h.congr_deriv ?_
  unfold deltaXx4; ring

theorem nb14_hasDerivAt_deltaX5 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t : ℝ => deltaX x1 x2 x3 x4 t x6) (deltaXx5 x1 x2 x3 x4 x5 x6) x5 := by
  have h := nb14_hasDerivAt_of_quad (f := fun t : ℝ => deltaX x1 x2 x3 x4 t x6) (x := x5)
    (A := -x2)
    (B := x2 * (x1 - x2 + x3 + x4 + x6) + x1 * x4 + x3 * x6 - x1 * x3 - x4 * x6)
    (C := x1 * x4 * (-x1 + x2 + x3 - x4 + x6) + x3 * x6 * (x1 + x2 - x3 + x4 - x6) -
      x2 * x3 * x4 - x1 * x2 * x6)
    (fun t => by unfold deltaX; ring)
  refine h.congr_deriv ?_
  unfold deltaXx5; ring

theorem nb14_hasDerivAt_deltaX6 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t : ℝ => deltaX x1 x2 x3 x4 x5 t) (deltaXx6 x1 x2 x3 x4 x5 x6) x6 := by
  have h := nb14_hasDerivAt_of_quad (f := fun t : ℝ => deltaX x1 x2 x3 x4 x5 t) (x := x6)
    (A := -x3)
    (B := x3 * (x1 + x2 - x3 + x4 + x5) + x1 * x4 + x2 * x5 - x1 * x2 - x4 * x5)
    (C := x1 * x4 * (-x1 + x2 + x3 - x4 + x5) + x2 * x5 * (x1 - x2 + x3 + x4 - x5) -
      x2 * x3 * x4 - x1 * x3 * x5)
    (fun t => by unfold deltaX; ring)
  refine h.congr_deriv ?_
  unfold deltaXx6; ring

/-! ## 5. Partial derivatives of `eulerAX` -/

/-- `∂eulerAX/∂x1`. -/
noncomputable def eulerAXx1 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt (x2 * x3) / (2 * Real.sqrt x1) + (x2 + x3 - x4) / (4 * Real.sqrt x1) +
    Real.sqrt x2 / 2 + Real.sqrt x3 / 2

/-- `∂eulerAX/∂x2`. -/
noncomputable def eulerAXx2 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt (x1 * x3) / (2 * Real.sqrt x2) + Real.sqrt x1 / 2 +
    (x1 + x3 - x5) / (4 * Real.sqrt x2) + Real.sqrt x3 / 2

/-- `∂eulerAX/∂x3`. -/
noncomputable def eulerAXx3 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  Real.sqrt (x1 * x2) / (2 * Real.sqrt x3) + Real.sqrt x1 / 2 + Real.sqrt x2 / 2 +
    (x1 + x2 - x6) / (4 * Real.sqrt x3)

/-- `∂eulerAX/∂x4`. -/
noncomputable def eulerAXx4 (x1 _x2 _x3 _x4 _x5 _x6 : ℝ) : ℝ := -(Real.sqrt x1) / 2

/-- `∂eulerAX/∂x5`. -/
noncomputable def eulerAXx5 (_x1 x2 _x3 _x4 _x5 _x6 : ℝ) : ℝ := -(Real.sqrt x2) / 2

/-- `∂eulerAX/∂x6`. -/
noncomputable def eulerAXx6 (_x1 _x2 x3 _x4 _x5 _x6 : ℝ) : ℝ := -(Real.sqrt x3) / 2

/-! ## 6. `HasDerivAt` for the six coordinate slices of `eulerAX` -/

theorem nb14_hasDerivAt_eulerAX1 (x1 x2 x3 x4 x5 x6 : ℝ) (h1 : 0 < x1) :
    HasDerivAt (fun t : ℝ => eulerAX t x2 x3 x4 x5 x6) (eulerAXx1 x1 x2 x3 x4 x5 x6) x1 := by
  have h := nb14_hasDerivAt_sqrtLin (x := x1) h1
    (K := Real.sqrt (x2 * x3) + (x2 + x3 - x4) / 2)
    (L := Real.sqrt x2 / 2 + Real.sqrt x3 / 2)
    (C := Real.sqrt x2 * (x3 - x5) / 2 + Real.sqrt x3 * (x2 - x6) / 2)
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards [lt_mem_nhds h1] with t ht
    unfold eulerAX
    rw [show t * x2 * x3 = t * (x2 * x3) by ring, Real.sqrt_mul ht.le]
    ring
  · unfold eulerAXx1; field_simp; ring

theorem nb14_hasDerivAt_eulerAX2 (x1 x2 x3 x4 x5 x6 : ℝ) (h2 : 0 < x2) :
    HasDerivAt (fun t : ℝ => eulerAX x1 t x3 x4 x5 x6) (eulerAXx2 x1 x2 x3 x4 x5 x6) x2 := by
  have h := nb14_hasDerivAt_sqrtLin (x := x2) h2
    (K := Real.sqrt (x1 * x3) + (x1 + x3 - x5) / 2)
    (L := Real.sqrt x1 / 2 + Real.sqrt x3 / 2)
    (C := Real.sqrt x1 * (x3 - x4) / 2 + Real.sqrt x3 * (x1 - x6) / 2)
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards [lt_mem_nhds h2] with t ht
    unfold eulerAX
    rw [show x1 * t * x3 = t * (x1 * x3) by ring, Real.sqrt_mul ht.le]
    ring
  · unfold eulerAXx2; field_simp; ring

theorem nb14_hasDerivAt_eulerAX3 (x1 x2 x3 x4 x5 x6 : ℝ) (h3 : 0 < x3) :
    HasDerivAt (fun t : ℝ => eulerAX x1 x2 t x4 x5 x6) (eulerAXx3 x1 x2 x3 x4 x5 x6) x3 := by
  have h := nb14_hasDerivAt_sqrtLin (x := x3) h3
    (K := Real.sqrt (x1 * x2) + (x1 + x2 - x6) / 2)
    (L := Real.sqrt x1 / 2 + Real.sqrt x2 / 2)
    (C := Real.sqrt x1 * (x2 - x4) / 2 + Real.sqrt x2 * (x1 - x5) / 2)
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards [lt_mem_nhds h3] with t ht
    unfold eulerAX
    rw [show x1 * x2 * t = t * (x1 * x2) by ring, Real.sqrt_mul ht.le]
    ring
  · unfold eulerAXx3; field_simp; ring

theorem nb14_hasDerivAt_eulerAX4 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t : ℝ => eulerAX x1 x2 x3 t x5 x6) (eulerAXx4 x1 x2 x3 x4 x5 x6) x4 := by
  have h := nb14_hasDerivAt_of_lin (f := fun t : ℝ => eulerAX x1 x2 x3 t x5 x6) (x := x4)
    (L := -(Real.sqrt x1) / 2)
    (C := Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3) / 2 +
      Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2)
    (fun t => by unfold eulerAX; ring)
  simpa [eulerAXx4] using h

theorem nb14_hasDerivAt_eulerAX5 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t : ℝ => eulerAX x1 x2 x3 x4 t x6) (eulerAXx5 x1 x2 x3 x4 x5 x6) x5 := by
  have h := nb14_hasDerivAt_of_lin (f := fun t : ℝ => eulerAX x1 x2 x3 x4 t x6) (x := x5)
    (L := -(Real.sqrt x2) / 2)
    (C := Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
      Real.sqrt x2 * (x1 + x3) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2)
    (fun t => by unfold eulerAX; ring)
  simpa [eulerAXx5] using h

theorem nb14_hasDerivAt_eulerAX6 (x1 x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun t : ℝ => eulerAX x1 x2 x3 x4 x5 t) (eulerAXx6 x1 x2 x3 x4 x5 x6) x6 := by
  have h := nb14_hasDerivAt_of_lin (f := fun t : ℝ => eulerAX x1 x2 x3 x4 x5 t) (x := x6)
    (L := -(Real.sqrt x3) / 2)
    (C := Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
      Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2) / 2)
    (fun t => by unfold eulerAX; ring)
  simpa [eulerAXx6] using h

/-! ## 7. The reusable chain rule for `matan(u)/v` -/

/-- Chain rule: `matan (u t) / v t`.  This is the only place `matanDeriv`
enters a composite; every `sqrtdelta` slot is an instance. -/
theorem nb14_hasDerivAt_matan_div {u v : ℝ → ℝ} {x du dv : ℝ}
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x) (hvx : v x ≠ 0)
    (hu1 : -1 < u x) :
    HasDerivAt (fun t => matan (u t) / v t)
      ((matanDeriv (u x) * du * v x - matan (u x) * dv) / v x ^ 2) x := by
  have hm : HasDerivAt (fun t => matan (u t)) (matanDeriv (u x) * du) x :=
    HasDerivAt.comp (h := u) (x := x) (nb13_hasDerivAt_matan hu1) hu
  exact hm.div hv hvx

/-! ## 8. The six `solEulerXDivSqrtdelta` slices -/

/-- Partial of `solEulerXDivSqrtdelta` in one coordinate, given the partials
`dD = ∂Δ/∂xᵢ` and `da = ∂a/∂xᵢ`:
`∂/∂xᵢ [matan(u)/a] = (matanDeriv u · du · a − matan u · da) / a²` with
`u = Δ/(4a²)`, `du = dD/(4a²) − Δ·da/(2a³)`. -/
noncomputable def solEulerDx (dD da : ℝ) (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let a := eulerAX x1 x2 x3 x4 x5 x6
  let u := deltaX x1 x2 x3 x4 x5 x6 / (4 * a ^ 2)
  (matanDeriv u * (dD / (4 * a ^ 2) - deltaX x1 x2 x3 x4 x5 x6 * da / (2 * a ^ 3)) * a -
    matan u * da) / a ^ 2

/-- **Generic `solEuler` slice derivative.** -/
theorem nb14_hasDerivAt_solEulerSlice {D A : ℝ → ℝ} {x dD da : ℝ}
    (hD : HasDerivAt D dD x) (hA : HasDerivAt A da x)
    (ha : A x ≠ 0) (hu1 : -1 < D x / (4 * A x ^ 2)) :
    HasDerivAt (fun t => matan (D t / (4 * A t ^ 2)) / A t)
      (let a := A x
       let u := D x / (4 * a ^ 2)
       (matanDeriv u * (dD / (4 * a ^ 2) - D x * da / (2 * a ^ 3)) * a - matan u * da) / a ^ 2)
      x := by
  have h4 : HasDerivAt (fun t : ℝ => 4 * A t ^ 2) (4 * (2 * A x * da)) x := by
    have := (hA.pow 2).const_mul 4
    refine this.congr_deriv ?_
    ring
  have h4ne : 4 * A x ^ 2 ≠ 0 := by
    have h2 : A x ^ 2 ≠ 0 := pow_ne_zero 2 ha
    positivity
  have hu : HasDerivAt (fun t : ℝ => D t / (4 * A t ^ 2))
      ((dD * (4 * A x ^ 2) - D x * (4 * (2 * A x * da))) / (4 * A x ^ 2) ^ 2) x :=
    hD.div h4 h4ne
  have hmd := nb14_hasDerivAt_matan_div hu hA ha hu1
  refine hmd.congr_deriv ?_
  set a := A x
  set Dx := D x
  have ha' : a ≠ 0 := ha
  have h4ne' : 4 * a ^ 2 ≠ 0 := h4ne
  field_simp
  ring

/-- `solEulerXDivSqrtdelta` slice derivative in `x1`. -/
theorem nb14_hasDerivAt_solEuler1 (x1 x2 x3 x4 x5 x6 : ℝ) (h1 : 0 < x1)
    (ha : eulerAX x1 x2 x3 x4 x5 x6 ≠ 0)
    (hu1 : -1 < deltaX x1 x2 x3 x4 x5 x6 / (4 * eulerAX x1 x2 x3 x4 x5 x6 ^ 2)) :
    HasDerivAt (fun t : ℝ => solEulerXDivSqrtdelta t x2 x3 x4 x5 x6)
      (solEulerDx (deltaXx1 x1 x2 x3 x4 x5 x6) (eulerAXx1 x1 x2 x3 x4 x5 x6)
        x1 x2 x3 x4 x5 x6) x1 := by
  rw [show (fun t : ℝ => solEulerXDivSqrtdelta t x2 x3 x4 x5 x6) =
      (fun t => matan (deltaX t x2 x3 x4 x5 x6 / (4 * eulerAX t x2 x3 x4 x5 x6 ^ 2)) /
        eulerAX t x2 x3 x4 x5 x6) from funext fun t => nb14_solEuler_eq t x2 x3 x4 x5 x6]
  exact nb14_hasDerivAt_solEulerSlice (nb14_hasDerivAt_deltaX1 x1 x2 x3 x4 x5 x6)
    (nb14_hasDerivAt_eulerAX1 x1 x2 x3 x4 x5 x6 h1) ha hu1

/-- `solEulerXDivSqrtdelta` slice derivative in `x2`. -/
theorem nb14_hasDerivAt_solEuler2 (x1 x2 x3 x4 x5 x6 : ℝ) (h2 : 0 < x2)
    (ha : eulerAX x1 x2 x3 x4 x5 x6 ≠ 0)
    (hu1 : -1 < deltaX x1 x2 x3 x4 x5 x6 / (4 * eulerAX x1 x2 x3 x4 x5 x6 ^ 2)) :
    HasDerivAt (fun t : ℝ => solEulerXDivSqrtdelta x1 t x3 x4 x5 x6)
      (solEulerDx (deltaXx2 x1 x2 x3 x4 x5 x6) (eulerAXx2 x1 x2 x3 x4 x5 x6)
        x1 x2 x3 x4 x5 x6) x2 := by
  rw [show (fun t : ℝ => solEulerXDivSqrtdelta x1 t x3 x4 x5 x6) =
      (fun t => matan (deltaX x1 t x3 x4 x5 x6 / (4 * eulerAX x1 t x3 x4 x5 x6 ^ 2)) /
        eulerAX x1 t x3 x4 x5 x6) from funext fun t => nb14_solEuler_eq x1 t x3 x4 x5 x6]
  exact nb14_hasDerivAt_solEulerSlice (nb14_hasDerivAt_deltaX2 x1 x2 x3 x4 x5 x6)
    (nb14_hasDerivAt_eulerAX2 x1 x2 x3 x4 x5 x6 h2) ha hu1

/-- `solEulerXDivSqrtdelta` slice derivative in `x3`. -/
theorem nb14_hasDerivAt_solEuler3 (x1 x2 x3 x4 x5 x6 : ℝ) (h3 : 0 < x3)
    (ha : eulerAX x1 x2 x3 x4 x5 x6 ≠ 0)
    (hu1 : -1 < deltaX x1 x2 x3 x4 x5 x6 / (4 * eulerAX x1 x2 x3 x4 x5 x6 ^ 2)) :
    HasDerivAt (fun t : ℝ => solEulerXDivSqrtdelta x1 x2 t x4 x5 x6)
      (solEulerDx (deltaXx3 x1 x2 x3 x4 x5 x6) (eulerAXx3 x1 x2 x3 x4 x5 x6)
        x1 x2 x3 x4 x5 x6) x3 := by
  rw [show (fun t : ℝ => solEulerXDivSqrtdelta x1 x2 t x4 x5 x6) =
      (fun t => matan (deltaX x1 x2 t x4 x5 x6 / (4 * eulerAX x1 x2 t x4 x5 x6 ^ 2)) /
        eulerAX x1 x2 t x4 x5 x6) from funext fun t => nb14_solEuler_eq x1 x2 t x4 x5 x6]
  exact nb14_hasDerivAt_solEulerSlice (nb14_hasDerivAt_deltaX3 x1 x2 x3 x4 x5 x6)
    (nb14_hasDerivAt_eulerAX3 x1 x2 x3 x4 x5 x6 h3) ha hu1

/-- `solEulerXDivSqrtdelta` slice derivative in `x4`. -/
theorem nb14_hasDerivAt_solEuler4 (x1 x2 x3 x4 x5 x6 : ℝ)
    (ha : eulerAX x1 x2 x3 x4 x5 x6 ≠ 0)
    (hu1 : -1 < deltaX x1 x2 x3 x4 x5 x6 / (4 * eulerAX x1 x2 x3 x4 x5 x6 ^ 2)) :
    HasDerivAt (fun t : ℝ => solEulerXDivSqrtdelta x1 x2 x3 t x5 x6)
      (solEulerDx (deltaXx4 x1 x2 x3 x4 x5 x6) (eulerAXx4 x1 x2 x3 x4 x5 x6)
        x1 x2 x3 x4 x5 x6) x4 := by
  rw [show (fun t : ℝ => solEulerXDivSqrtdelta x1 x2 x3 t x5 x6) =
      (fun t => matan (deltaX x1 x2 x3 t x5 x6 / (4 * eulerAX x1 x2 x3 t x5 x6 ^ 2)) /
        eulerAX x1 x2 x3 t x5 x6) from funext fun t => nb14_solEuler_eq x1 x2 x3 t x5 x6]
  exact nb14_hasDerivAt_solEulerSlice (nb14_hasDerivAt_deltaX4 x1 x2 x3 x4 x5 x6)
    (nb14_hasDerivAt_eulerAX4 x1 x2 x3 x4 x5 x6) ha hu1

/-- `solEulerXDivSqrtdelta` slice derivative in `x5`. -/
theorem nb14_hasDerivAt_solEuler5 (x1 x2 x3 x4 x5 x6 : ℝ)
    (ha : eulerAX x1 x2 x3 x4 x5 x6 ≠ 0)
    (hu1 : -1 < deltaX x1 x2 x3 x4 x5 x6 / (4 * eulerAX x1 x2 x3 x4 x5 x6 ^ 2)) :
    HasDerivAt (fun t : ℝ => solEulerXDivSqrtdelta x1 x2 x3 x4 t x6)
      (solEulerDx (deltaXx5 x1 x2 x3 x4 x5 x6) (eulerAXx5 x1 x2 x3 x4 x5 x6)
        x1 x2 x3 x4 x5 x6) x5 := by
  rw [show (fun t : ℝ => solEulerXDivSqrtdelta x1 x2 x3 x4 t x6) =
      (fun t => matan (deltaX x1 x2 x3 x4 t x6 / (4 * eulerAX x1 x2 x3 x4 t x6 ^ 2)) /
        eulerAX x1 x2 x3 x4 t x6) from funext fun t => nb14_solEuler_eq x1 x2 x3 x4 t x6]
  exact nb14_hasDerivAt_solEulerSlice (nb14_hasDerivAt_deltaX5 x1 x2 x3 x4 x5 x6)
    (nb14_hasDerivAt_eulerAX5 x1 x2 x3 x4 x5 x6) ha hu1

/-- `solEulerXDivSqrtdelta` slice derivative in `x6`. -/
theorem nb14_hasDerivAt_solEuler6 (x1 x2 x3 x4 x5 x6 : ℝ)
    (ha : eulerAX x1 x2 x3 x4 x5 x6 ≠ 0)
    (hu1 : -1 < deltaX x1 x2 x3 x4 x5 x6 / (4 * eulerAX x1 x2 x3 x4 x5 x6 ^ 2)) :
    HasDerivAt (fun t : ℝ => solEulerXDivSqrtdelta x1 x2 x3 x4 x5 t)
      (solEulerDx (deltaXx6 x1 x2 x3 x4 x5 x6) (eulerAXx6 x1 x2 x3 x4 x5 x6)
        x1 x2 x3 x4 x5 x6) x6 := by
  rw [show (fun t : ℝ => solEulerXDivSqrtdelta x1 x2 x3 x4 x5 t) =
      (fun t => matan (deltaX x1 x2 x3 x4 x5 t / (4 * eulerAX x1 x2 x3 x4 x5 t ^ 2)) /
        eulerAX x1 x2 x3 x4 x5 t) from funext fun t => nb14_solEuler_eq x1 x2 x3 x4 x5 t]
  exact nb14_hasDerivAt_solEulerSlice (nb14_hasDerivAt_deltaX6 x1 x2 x3 x4 x5 x6)
    (nb14_hasDerivAt_eulerAX6 x1 x2 x3 x4 x5 x6) ha hu1

/-! ## 9. Axiom audit -/

#print axioms nb14_solEuler_eq
#print axioms nb14_deltaXx4_eq_deltaX4
#print axioms nb14_hasDerivAt_deltaX1
#print axioms nb14_hasDerivAt_eulerAX1
#print axioms nb14_hasDerivAt_matan_div
#print axioms nb14_hasDerivAt_solEulerSlice
#print axioms nb14_hasDerivAt_solEuler1
#print axioms nb14_hasDerivAt_solEuler6

end Kepler.NliBanks14
