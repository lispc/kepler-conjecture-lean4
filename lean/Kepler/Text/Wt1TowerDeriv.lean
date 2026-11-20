/-
Kepler.Text.Wt1TowerDeriv — lane `cell3-wt1-tower-build-w1` (2026-11-20),
phase 1 of the wt1 second-order tower (route A′), piece 3 of 3:
the y5-slice derivative chain of the wt1 kernel `w1aF`.

Structure:
* §1 slot data in pinned (sqrt-free) form: the symmetric Delta `w1Dlt`
  (SCOUT §1.1), the Euler areas `w1aA/B/C`, the dih denominators
  `w1d4A/B/C`, plus their y5-derivative functions;
* §2 base `HasDerivAt` facts (quadratic/quartic helpers; Delta and area
  derivatives);
* §3 the generic chain rules: `matan (T s)/A s` slots (level 1 = SCOUT
  §1.1's `dSE` and level 2 = its `d²SE`, both matan-linear in
  `matan/matanD/matanDD`) and `W s * matan (T s)` slots (`dD`, `d²D`),
  plus the abstract `t`, `g`, `W` rational machinery
  (`w1tOf/w1tDOf/w1tDDOf`, `w1gOf/w1gDOf/w1gDDOf`, `w1WOf/w1WDOf/w1WDDOf`);
* §4 slot instantiations (SE_A/B/C, dih_A/B/C) for D1 and D2;
* §5 assembly into `w1aF_hasDerivAt_y5` (D1) and
  `w1aF_hasDerivAt2_y5` (D2).

The D1/D2 statements carry, besides the wt1 box hypotheses, the explicit
differentiability-domain hypotheses `-1 < t` / `-1 < g` for the six `matan`
arguments; discharging these from the box bounds is certificate-layer work
(P1, phase 2; SCOUT §1.5 records the measured ranges
`t ∈ [-0.0056, 0.026]`, `g ∈ [-0.357, 8.22] ⊂ (-1, ∞)`).

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.NliBanks21
import Kepler.Text.Wt1TowerKit

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text
open Kepler.NliBanks21
open Filter
open scoped Topology

/-! ## 1. Slot data in pinned form -/

/-- Symmetric three-coordinate Delta of the wt1 slots
(`X = y4², y5², y6²`; equals `deltaX` at every slot permutation). -/
def w1Dlt (y4 y5 y6 : ℝ) : ℝ :=
  -2 * ((y4 * y4) ^ 2 + (y5 * y5) ^ 2 + (y6 * y6) ^ 2) +
    4 * ((y4 * y4) * (y5 * y5) + (y4 * y4) * (y6 * y6) + (y5 * y5) * (y6 * y6)) -
    (y4 * y4) * (y5 * y5) * (y6 * y6)

/-- `∂ w1Dlt / ∂ y5`. -/
def w1DltD (y4 y5 y6 : ℝ) : ℝ :=
  2 * y5 * (4 * (y4 * y4) + 4 * (y6 * y6) - 4 * (y5 * y5) - (y4 * y4) * (y6 * y6))

/-- `∂² w1Dlt / ∂ y5²`. -/
def w1DltDD (y4 y5 y6 : ℝ) : ℝ :=
  8 * (y4 * y4) + 8 * (y6 * y6) - 24 * (y5 * y5) - 2 * (y4 * y4) * (y6 * y6)

/-- Euler area `a` of the A-slot `solEuler (y5², 2, y4², 2, y6², 2)` (pinned). -/
noncomputable def w1aA (y4 y5 y6 : ℝ) : ℝ :=
  Real.sqrt 2 * y5 * y4 + y5 * (y4 * y4) / 2 +
    Real.sqrt 2 * ((y5 * y5) + (y4 * y4) - (y6 * y6)) / 2 + y4 * (y5 * y5) / 2

/-- Euler area of the B-slot `solEuler (y6², 2, y5², 2, y4², 2)` (pinned). -/
noncomputable def w1aB (y4 y5 y6 : ℝ) : ℝ :=
  Real.sqrt 2 * y6 * y5 + y6 * (y5 * y5) / 2 +
    Real.sqrt 2 * ((y6 * y6) + (y5 * y5) - (y4 * y4)) / 2 + y5 * (y6 * y6) / 2

/-- Euler area of the C-slot `solEuler (y4², 2, y6², 2, y5², 2)` (pinned). -/
noncomputable def w1aC (y4 y5 y6 : ℝ) : ℝ :=
  Real.sqrt 2 * y4 * y6 + y4 * (y6 * y6) / 2 +
    Real.sqrt 2 * ((y4 * y4) + (y6 * y6) - (y5 * y5)) / 2 + y6 * (y4 * y4) / 2

/-- `∂ w1aA / ∂ y5`. -/
noncomputable def w1aAD (y4 y5 y6 : ℝ) : ℝ :=
  (Real.sqrt 2 + y4) * y5 + (Real.sqrt 2 * y4 + y4 * y4 / 2)

/-- `∂ w1aB / ∂ y5`. -/
noncomputable def w1aBD (y4 y5 y6 : ℝ) : ℝ :=
  (Real.sqrt 2 + y6) * y5 + (Real.sqrt 2 * y6 + y6 * y6 / 2)

/-- `∂ w1aC / ∂ y5`. -/
noncomputable def w1aCD (y4 y5 y6 : ℝ) : ℝ :=
  -(Real.sqrt 2) * y5

/-- `∂² w1aA / ∂ y5²`. -/
noncomputable def w1aADD (y4 _y5 _y6 : ℝ) : ℝ := Real.sqrt 2 + y4

/-- `∂² w1aB / ∂ y5²`. -/
noncomputable def w1aBDD (_y4 _y5 y6 : ℝ) : ℝ := Real.sqrt 2 + y6

/-- `∂² w1aC / ∂ y5²`. -/
noncomputable def w1aCDD (_y4 _y5 _y6 : ℝ) : ℝ := -(Real.sqrt 2)

/-- `deltaX4` at the A-slot (`= y5² (y4² + y6² - y5²)`). -/
def w1d4A (y4 y5 y6 : ℝ) : ℝ := (y5 * y5) * ((y4 * y4) + (y6 * y6) - (y5 * y5))

/-- `deltaX4` at the B-slot. -/
def w1d4B (y4 y5 y6 : ℝ) : ℝ := (y6 * y6) * ((y5 * y5) + (y4 * y4) - (y6 * y6))

/-- `deltaX4` at the C-slot. -/
def w1d4C (y4 y5 y6 : ℝ) : ℝ := (y4 * y4) * ((y6 * y6) + (y5 * y5) - (y4 * y4))

/-- `∂ w1d4A / ∂ y5`. -/
def w1d4AD (y4 y5 y6 : ℝ) : ℝ :=
  2 * (y4 * y4 + y6 * y6) * y5 - 4 * y5 ^ 3

/-- `∂ w1d4B / ∂ y5`. -/
def w1d4BD (_y4 y5 y6 : ℝ) : ℝ := 2 * (y6 * y6) * y5

/-- `∂ w1d4C / ∂ y5`. -/
def w1d4CD (y4 y5 _y6 : ℝ) : ℝ := 2 * (y4 * y4) * y5

/-- `∂² w1d4A / ∂ y5²`. -/
def w1d4ADD (y4 y5 y6 : ℝ) : ℝ := 2 * (y4 * y4 + y6 * y6) - 12 * y5 ^ 2

/-- `∂² w1d4B / ∂ y5²`. -/
def w1d4BDD (_y4 _y5 y6 : ℝ) : ℝ := 2 * (y6 * y6)

/-- `∂² w1d4C / ∂ y5²`. -/
def w1d4CDD (y4 _y5 _y6 : ℝ) : ℝ := 2 * (y4 * y4)

/-- `deltaX` at the A-slot equals the symmetric Delta. -/
theorem w1_dltA (y4 y5 y6 : ℝ) :
    deltaX (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 = w1Dlt y4 y5 y6 := by
  unfold w1Dlt
  rw [deltaX]
  ring

/-- `deltaX` at the B-slot equals the symmetric Delta. -/
theorem w1_dltB (y4 y5 y6 : ℝ) :
    deltaX (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 = w1Dlt y4 y5 y6 := by
  unfold w1Dlt
  rw [deltaX]
  ring

/-- `deltaX` at the C-slot equals the symmetric Delta. -/
theorem w1_dltC (y4 y5 y6 : ℝ) :
    deltaX (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 = w1Dlt y4 y5 y6 := by
  unfold w1Dlt
  rw [deltaX]
  ring

/-- `deltaX4` at the A-slot. -/
theorem w1_d4A (y4 y5 y6 : ℝ) :
    deltaX4 (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 = w1d4A y4 y5 y6 := by
  unfold w1d4A
  rw [deltaX4]
  ring

/-- `deltaX4` at the B-slot. -/
theorem w1_d4B (y4 y5 y6 : ℝ) :
    deltaX4 (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 = w1d4B y4 y5 y6 := by
  unfold w1d4B
  rw [deltaX4]
  ring

/-- `deltaX4` at the C-slot. -/
theorem w1_d4C (y4 y5 y6 : ℝ) :
    deltaX4 (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 = w1d4C y4 y5 y6 := by
  unfold w1d4C
  rw [deltaX4]
  ring

/-! ## 2. Base `HasDerivAt` facts -/

/-- `HasDerivAt` of `s ↦ A (s s)² + B (s s) + C1 s + C0`. -/
theorem w1_quad4_deriv (A B C1 C0 y : ℝ) :
    HasDerivAt (fun s : ℝ => A * (s * s) ^ 2 + B * (s * s) + C1 * s + C0)
      (4 * A * y ^ 3 + 2 * B * y + C1) y := by
  have hss : HasDerivAt (fun s : ℝ => s * s) (2 * y) y := by
    have h0 := (hasDerivAt_id y).mul (hasDerivAt_id y)
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · simp only [id_eq]; ring
    · intro s; simp only [Pi.mul_apply, id_eq]; try ring
  have h4 : HasDerivAt (fun s : ℝ => (s * s) ^ 2) (4 * y ^ 3) y := by
    have h0 := hss.mul hss
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.mul_apply]; try ring
  have hA : HasDerivAt (fun s : ℝ => A * (s * s) ^ 2) (A * (4 * y ^ 3)) y := by
    have hc := hasDerivAt_const y A
    have h0 := hc.mul h4
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.mul_apply]; try ring
  have hB : HasDerivAt (fun s : ℝ => B * (s * s)) (B * (2 * y)) y := by
    have hc := hasDerivAt_const y B
    have h0 := hc.mul hss
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.mul_apply]; try ring
  have hC1 : HasDerivAt (fun s : ℝ => C1 * s) C1 y := by
    have h0 := (hasDerivAt_id y).const_mul C1
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.smul_apply, smul_eq_mul, id_eq]; try ring
  have h := ((hA.add hB).add hC1).add_const C0
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · ring
  · intro s; simp only [Pi.add_apply]; try ring

/-- `HasDerivAt` of `s ↦ 2 s (E - 4 s²)`. -/
theorem w1_cubic_deriv (E y : ℝ) :
    HasDerivAt (fun s : ℝ => 2 * s * (E - 4 * (s * s))) (2 * E - 24 * y ^ 2) y := by
  have hss : HasDerivAt (fun s : ℝ => s * s) (2 * y) y := by
    have h0 := (hasDerivAt_id y).mul (hasDerivAt_id y)
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · simp only [id_eq]; ring
    · intro s; simp only [Pi.mul_apply, id_eq]; try ring
  have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 y := by
    have h0 := (hasDerivAt_id y).const_mul 2
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.smul_apply, smul_eq_mul, id_eq]; try ring
  have h2 : HasDerivAt (fun s : ℝ => E - 4 * (s * s)) (-(8 * y)) y := by
    have h4 : HasDerivAt (fun s : ℝ => 4 * (s * s)) (4 * (2 * y)) y := by
      have hc := hasDerivAt_const y (4 : ℝ)
      have h0 := hc.mul hss
      refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · ring
      · intro s; simp only [Pi.mul_apply]; try ring
    have h0 := (hasDerivAt_const y E).sub h4
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.sub_apply]; try ring
  have h := h1.mul h2
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · ring
  · intro s; simp only [Pi.mul_apply]; try ring

/-- `HasDerivAt` of the symmetric Delta in the y5 slot. -/
theorem w1Dlt_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1Dlt y4 s y6) (w1DltD y4 y5 y6) y5 := by
  have h := w1_quad4_deriv (-2)
    (4 * (y4 * y4) + 4 * (y6 * y6) - (y4 * y4) * (y6 * y6)) 0
    (-2 * (y4 * y4) ^ 2 - 2 * (y6 * y6) ^ 2 + 4 * (y4 * y4) * (y6 * y6)) y5
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1DltD; ring
  · intro s; unfold w1Dlt; ring

/-- `HasDerivAt` of `∂Delta/∂y5` in the y5 slot. -/
theorem w1DltD_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1DltD y4 s y6) (w1DltDD y4 y5 y6) y5 := by
  have h := w1_cubic_deriv
    (4 * (y4 * y4) + 4 * (y6 * y6) - (y4 * y4) * (y6 * y6)) y5
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1DltDD; ring
  · intro s; unfold w1DltD; ring

/-- `HasDerivAt` of the A-slot Euler area. -/
theorem w1aA_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1aA y4 s y6) (w1aAD y4 y5 y6) y5 := by
  have h := w1_quad4_deriv 0 (Real.sqrt 2 / 2 + y4 / 2)
    (Real.sqrt 2 * y4 + y4 * y4 / 2)
    (Real.sqrt 2 * (y4 * y4 - y6 * y6) / 2) y5
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1aAD; ring
  · intro s; unfold w1aA; ring

/-- `HasDerivAt` of the B-slot Euler area. -/
theorem w1aB_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1aB y4 s y6) (w1aBD y4 y5 y6) y5 := by
  have h := w1_quad4_deriv 0 (Real.sqrt 2 / 2 + y6 / 2)
    (Real.sqrt 2 * y6 + y6 * y6 / 2)
    (Real.sqrt 2 * (y6 * y6 - y4 * y4) / 2) y5
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1aBD; ring
  · intro s; unfold w1aB; ring

/-- `HasDerivAt` of the C-slot Euler area. -/
theorem w1aC_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1aC y4 s y6) (w1aCD y4 y5 y6) y5 := by
  have h := w1_quad4_deriv 0 (-(Real.sqrt 2 / 2)) 0
    (Real.sqrt 2 * y4 * y6 + y4 * (y6 * y6) / 2 +
      Real.sqrt 2 * (y4 * y4 + y6 * y6) / 2 + y6 * (y4 * y4) / 2) y5
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1aCD; ring
  · intro s; unfold w1aC; ring

/-- `HasDerivAt` of the A-slot `deltaX4`. -/
theorem w1d4A_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1d4A y4 s y6) (w1d4AD y4 y5 y6) y5 := by
  have h := w1_quad4_deriv (-1) (y4 * y4 + y6 * y6) 0 0 y5
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1d4AD; ring
  · intro s; unfold w1d4A; ring

/-- `HasDerivAt` of the B-slot `deltaX4`. -/
theorem w1d4B_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1d4B y4 s y6) (w1d4BD y4 y5 y6) y5 := by
  have h := w1_quad4_deriv 0 (y6 * y6) 0 (y6 * y6 * (y4 * y4 - y6 * y6)) y5
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1d4BD; ring
  · intro s; unfold w1d4B; ring

/-- `HasDerivAt` of the C-slot `deltaX4`. -/
theorem w1d4C_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1d4C y4 s y6) (w1d4CD y4 y5 y6) y5 := by
  have h := w1_quad4_deriv 0 (y4 * y4) 0 (y4 * y4 * (y6 * y6 - y4 * y4)) y5
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1d4CD; ring
  · intro s; unfold w1d4C; ring

/-- `HasDerivAt` of `∂a_A/∂y5` in the y5 slot. -/
theorem w1aAD_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1aAD y4 s y6) (w1aADD y4 y5 y6) y5 := by
  have h0 := (hasDerivAt_id y5).const_mul (Real.sqrt 2 + y4)
  have h := h0.add_const (Real.sqrt 2 * y4 + y4 * y4 / 2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1aADD; ring
  · intro s; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq]; unfold w1aAD; ring

/-- `HasDerivAt` of `∂a_B/∂y5` in the y5 slot. -/
theorem w1aBD_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1aBD y4 s y6) (w1aBDD y4 y5 y6) y5 := by
  have h0 := (hasDerivAt_id y5).const_mul (Real.sqrt 2 + y6)
  have h := h0.add_const (Real.sqrt 2 * y6 + y6 * y6 / 2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1aBDD; ring
  · intro s; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq]; unfold w1aBD; ring

/-- `HasDerivAt` of `∂a_C/∂y5` in the y5 slot. -/
theorem w1aCD_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1aCD y4 s y6) (w1aCDD y4 y5 y6) y5 := by
  have h := (hasDerivAt_id y5).const_mul (-(Real.sqrt 2))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1aCDD; ring
  · intro s; simp only [Pi.smul_apply, smul_eq_mul, id_eq]; unfold w1aCD; ring

/-- `HasDerivAt` of `∂d4_A/∂y5` in the y5 slot. -/
theorem w1d4AD_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1d4AD y4 s y6) (w1d4ADD y4 y5 y6) y5 := by
  have hss : HasDerivAt (fun s : ℝ => s * s) (2 * y5) y5 := by
    have h0 := (hasDerivAt_id y5).mul (hasDerivAt_id y5)
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · simp only [id_eq]; ring
    · intro s; simp only [Pi.mul_apply, id_eq]; try ring
  have h1 : HasDerivAt (fun s : ℝ => 2 * (y4 * y4 + y6 * y6) * s)
      (2 * (y4 * y4 + y6 * y6)) y5 := by
    have hc := hasDerivAt_const y5 (2 * (y4 * y4 + y6 * y6))
    have h := hc.mul (hasDerivAt_id y5)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.mul_apply, id_eq]; try ring
  have h2 : HasDerivAt (fun s : ℝ => 4 * s ^ 3) (4 * (3 * y5 ^ 2)) y5 := by
    have hc := hasDerivAt_const y5 (4 : ℝ)
    have h3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * y5 ^ 2) y5 := by
      have h := hasDerivAt_pow 3 y5
      refine h.congr_deriv ?_
      norm_num
    have h := hc.mul h3
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.mul_apply]; try ring
  have h := h1.sub h2
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1d4ADD; ring
  · intro s; simp only [Pi.sub_apply]; unfold w1d4AD; ring

/-- `HasDerivAt` of `∂d4_B/∂y5` in the y5 slot. -/
theorem w1d4BD_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1d4BD y4 s y6) (w1d4BDD y4 y5 y6) y5 := by
  have h := (hasDerivAt_id y5).const_mul (2 * (y6 * y6))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1d4BDD; ring
  · intro s; simp only [Pi.smul_apply, smul_eq_mul, id_eq]; unfold w1d4BD; ring

/-- `HasDerivAt` of `∂d4_C/∂y5` in the y5 slot. -/
theorem w1d4CD_hasDerivAt (y4 y5 y6 : ℝ) :
    HasDerivAt (fun s => w1d4CD y4 s y6) (w1d4CDD y4 y5 y6) y5 := by
  have h := (hasDerivAt_id y5).const_mul (2 * (y4 * y4))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · unfold w1d4CDD; ring
  · intro s; simp only [Pi.smul_apply, smul_eq_mul, id_eq]; unfold w1d4CD; ring

/-! ## 3. Generic chain rules and slot machinery -/

/-- Level-1 chain rule for a `matan (T s) / A s` slot (SCOUT §1.1 `dSE`). -/
theorem w1_se_hasDerivAt {T A : ℝ → ℝ} {T' A' y : ℝ}
    (hT : HasDerivAt T T' y) (hA : HasDerivAt A A' y)
    (hA0 : A y ≠ 0) (ht : -1 < T y) :
    HasDerivAt (fun s => matan (T s) / A s)
      (matanD (T y) * T' / A y - matan (T y) * A' / A y ^ 2) y := by
  have hm : HasDerivAt (fun s => matan (T s)) (matanD (T y) * T') y :=
    (matan_hasDerivAt ht).comp y hT
  have h := hm.div hA hA0
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · field_simp
    try ring
  · intro s
    simp only [Pi.div_apply]

/-- Level-2 chain rule for the level-1 function of a `matan (T s) / A s` slot
(SCOUT §1.1 `d²SE`). -/
theorem w1_se_hasDerivAt2 {T T' A A' : ℝ → ℝ} {T'' A'' y : ℝ}
    (hT : HasDerivAt T (T' y) y) (hT' : HasDerivAt T' T'' y)
    (hA : HasDerivAt A (A' y) y) (hA' : HasDerivAt A' A'' y)
    (hA0 : A y ≠ 0) (ht : -1 < T y) :
    HasDerivAt
      (fun s => matanD (T s) * (T' s / A s) - matan (T s) * (A' s / A s ^ 2))
      (matanDD (T y) * (T' y) ^ 2 / A y
        + matanD (T y) * ((T'' * A y - 2 * T' y * A' y) / A y ^ 2)
        + matan (T y) * ((2 * (A' y) ^ 2 - A y * A'') / A y ^ 3)) y := by
  have h1 : HasDerivAt (fun s => matanD (T s)) (matanDD (T y) * T' y) y :=
    (matanD_hasDerivAt ht).comp y hT
  have h2 : HasDerivAt (fun s => T' s / A s) (T'' / A y - T' y * A' y / A y ^ 2) y := by
    have h := hT'.div hA hA0
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · field_simp
      try ring
    · intro s; simp only [Pi.div_apply]
  have hprod1 := h1.mul h2
  have h3 : HasDerivAt (fun s => matan (T s)) (matanD (T y) * T' y) y :=
    (matan_hasDerivAt ht).comp y hT
  have hpow : HasDerivAt (fun s => A s ^ 2) (2 * A y * A' y) y := by
    have h := hA.pow 2
    refine h.congr_deriv ?_
    ring
  have hA20 : A y ^ 2 ≠ 0 := pow_ne_zero 2 hA0
  have h4 : HasDerivAt (fun s => A' s / A s ^ 2)
      (A'' / A y ^ 2 - A' y * (2 * A y * A' y) / (A y ^ 2) ^ 2) y := by
    have h := hA'.div hpow hA20
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · field_simp
      try ring
    · intro s; simp only [Pi.div_apply]
  have hprod2 := h3.mul h4
  have h := hprod1.sub hprod2
  have hder : matanDD (T y) * T' y * (T' y / A y)
        + matanD (T y) * (T'' / A y - T' y * A' y / A y ^ 2)
        - (matanD (T y) * T' y * (A' y / A y ^ 2)
          + matan (T y) * (A'' / A y ^ 2 - A' y * (2 * A y * A' y) / (A y ^ 2) ^ 2))
      = matanDD (T y) * (T' y) ^ 2 / A y
        + matanD (T y) * ((T'' * A y - 2 * T' y * A' y) / A y ^ 2)
        + matan (T y) * ((2 * (A' y) ^ 2 - A y * A'') / A y ^ 3) := by
    field_simp
    ring
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply]
  try ring

/-- Level-1 chain rule for a `W s * matan (T s)` slot (SCOUT §1.1 `dD`). -/
theorem w1_dih_hasDerivAt {T W : ℝ → ℝ} {T' W' y : ℝ}
    (hT : HasDerivAt T T' y) (hW : HasDerivAt W W' y) (ht : -1 < T y) :
    HasDerivAt (fun s => W s * matan (T s))
      (W' * matan (T y) + W y * (matanD (T y) * T')) y := by
  have hm : HasDerivAt (fun s => matan (T s)) (matanD (T y) * T') y :=
    (matan_hasDerivAt ht).comp y hT
  have h := hW.mul hm
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · ring
  · intro s
    simp only [Pi.mul_apply]

/-- Level-2 chain rule for the level-1 function of a `W s * matan (T s)` slot
(SCOUT §1.1 `d²D`). -/
theorem w1_dih_hasDerivAt2 {T T' W W' : ℝ → ℝ} {T'' W'' y : ℝ}
    (hT : HasDerivAt T (T' y) y) (hT' : HasDerivAt T' T'' y)
    (hW : HasDerivAt W (W' y) y) (hW' : HasDerivAt W' W'' y)
    (ht : -1 < T y) :
    HasDerivAt
      (fun s => W' s * matan (T s) + W s * (matanD (T s) * T' s))
      (W'' * matan (T y) + 2 * W' y * T' y * matanD (T y)
        + W y * (matanDD (T y) * (T' y) ^ 2)
        + W y * (matanD (T y) * T'')) y := by
  have hm : HasDerivAt (fun s => matan (T s)) (matanD (T y) * T' y) y :=
    (matan_hasDerivAt ht).comp y hT
  have hmd : HasDerivAt (fun s => matanD (T s)) (matanDD (T y) * T' y) y :=
    (matanD_hasDerivAt ht).comp y hT
  have hA := hW'.mul hm
  have hinner : HasDerivAt (fun s => matanD (T s) * T' s)
      (matanDD (T y) * T' y * T' y + matanD (T y) * T'') y := by
    have h := hmd.mul hT'
    refine h.congr_deriv ?_
    ring
  have hB := hW.mul hinner
  have h := hA.add hB
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · ring
  · intro s
    simp only [Pi.add_apply, Pi.mul_apply]

/-! ### Abstract `t`, `g`, `W` machinery -/

/-- `t(s) = D s / (4 (A s)²)`. -/
noncomputable def w1tOf (D A : ℝ → ℝ) (s : ℝ) : ℝ :=
  D s / (4 * A s ^ 2)

/-- `t'(s)` in quotient-rule form. -/
noncomputable def w1tDfun (D D' A A' : ℝ → ℝ) (s : ℝ) : ℝ :=
  (D' s * (4 * A s ^ 2) - D s * (8 * A s * A' s)) / (4 * A s ^ 2) ^ 2

/-- `t''(y)` in raw quotient-rule form. -/
noncomputable def w1tDDOf (D D' A A' : ℝ → ℝ) (D'' A'' : ℝ) (y : ℝ) : ℝ :=
  (((D'' * (4 * A y ^ 2) - 8 * D y * (A' y) ^ 2 - 8 * D y * A y * A'')
      * (4 * A y ^ 2) ^ 2)
    - (D' y * (4 * A y ^ 2) - D y * (8 * A y * A' y))
        * (2 * (4 * A y ^ 2) * (8 * A y * A' y))) /
  ((4 * A y ^ 2) ^ 2) ^ 2

/-- `g(s) = K s * D s / (A s)²`. -/
noncomputable def w1gOf (K D A : ℝ → ℝ) (s : ℝ) : ℝ :=
  K s * D s / A s ^ 2

/-- `g'(s)` in quotient-rule form. -/
noncomputable def w1gDfun (K K' D D' A A' : ℝ → ℝ) (s : ℝ) : ℝ :=
  ((K' s * D s + K s * D' s) * A s ^ 2 - 2 * K s * D s * (A s * A' s)) /
    (A s ^ 2) ^ 2

/-- `g''(y)` in raw quotient-rule form. -/
noncomputable def w1gDDOf (K K' D D' A A' : ℝ → ℝ) (K'' D'' A'' : ℝ) (y : ℝ) : ℝ :=
  ((((K'' * D y + 2 * K' y * D' y + K y * D'') * A y ^ 2
        - 2 * K y * D y * ((A' y) ^ 2 + A y * A''))
      * (A y ^ 2) ^ 2)
    - ((K' y * D y + K y * D' y) * A y ^ 2 - 2 * K y * D y * (A y * A' y))
        * (2 * (A y ^ 2) * (2 * (A y * A' y)))) /
  ((A y ^ 2) ^ 2) ^ 2

/-- `W(s) = N s / A s`. -/
noncomputable def w1WOf (N A : ℝ → ℝ) (s : ℝ) : ℝ := N s / A s

/-- `W'(s)` in quotient-rule form. -/
noncomputable def w1WDfun (N N' A A' : ℝ → ℝ) (s : ℝ) : ℝ :=
  (N' s * A s - N s * A' s) / A s ^ 2

/-- `W''(y)` in raw quotient-rule form. -/
noncomputable def w1WDDOf (N N' A A' : ℝ → ℝ) (N'' A'' : ℝ) (y : ℝ) : ℝ :=
  (((N'' * A y - N y * A'') * (A y ^ 2))
    - ((N' y * A y - N y * A' y) * (2 * (A y * A' y)))) /
  (A y ^ 2) ^ 2

theorem w1t_hasDerivAt {D A : ℝ → ℝ} {D' A' y : ℝ}
    (hD : HasDerivAt D D' y) (hA : HasDerivAt A A' y) (hA0 : A y ≠ 0) :
    HasDerivAt (fun s => w1tOf D A s) (w1tDfun D (fun _ => D') A (fun _ => A') y) y := by
  have hQ : HasDerivAt (fun s => 4 * A s ^ 2) (8 * A y * A') y := by
    have h := hA.pow 2
    have h4 : HasDerivAt (fun s => 4 * A s ^ 2) (4 * (2 * A y * A')) y := by
      have hc := hasDerivAt_const y (4 : ℝ)
      have h0 := hc.mul h
      refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · ring
      · intro s; simp only [Pi.mul_apply, Pi.pow_apply]; try ring
    refine h4.congr_deriv ?_
    ring
  have hQ0 : 4 * A y ^ 2 ≠ 0 := by
    have h := pow_ne_zero 2 hA0
    exact mul_ne_zero (by norm_num) h
  have h := hD.div hQ hQ0
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · simp only [w1tDfun]
  · intro s
    simp only [Pi.div_apply, w1tOf]

theorem w1tD_hasDerivAt {D D' A A' : ℝ → ℝ} {D'' A'' y : ℝ}
    (hD : HasDerivAt D (D' y) y) (hD' : HasDerivAt D' D'' y)
    (hA : HasDerivAt A (A' y) y) (hA' : HasDerivAt A' A'' y) (hA0 : A y ≠ 0) :
    HasDerivAt (fun s => w1tDfun D D' A A' s) (w1tDDOf D D' A A' D'' A'' y) y := by
  have hQ : HasDerivAt (fun s => 4 * A s ^ 2) (8 * A y * A' y) y := by
    have h := hA.pow 2
    have h4 : HasDerivAt (fun s => 4 * A s ^ 2) (4 * (2 * A y * A' y)) y := by
      have hc := hasDerivAt_const y (4 : ℝ)
      have h0 := hc.mul h
      refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · ring
      · intro s; simp only [Pi.mul_apply, Pi.pow_apply]; try ring
    refine h4.congr_deriv ?_
    ring
  have hQ0 : 4 * A y ^ 2 ≠ 0 := by
    have h := pow_ne_zero 2 hA0
    exact mul_ne_zero (by norm_num) h
  have hDmulA : HasDerivAt (fun s => D s * (8 * A s * A' s))
      (D' y * (8 * A y * A' y) + D y * (8 * (A' y * A' y + A y * A''))) y := by
    have hAA : HasDerivAt (fun s => 8 * A s * A' s)
        (8 * (A' y * A' y + A y * A'')) y := by
      have h := hA.mul hA'
      have hc := hasDerivAt_const y (8 : ℝ)
      have h0 := hc.mul h
      refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · ring
      · intro s; simp only [Pi.mul_apply]; ring
    exact hD.mul hAA
  have hN : HasDerivAt
      (fun s => D' s * (4 * A s ^ 2) - D s * (8 * A s * A' s))
      (D'' * (4 * A y ^ 2) - 8 * D y * (A' y) ^ 2 - 8 * D y * A y * A'') y := by
    have h := (hD'.mul hQ).sub hDmulA
    refine h.congr_deriv ?_
    field_simp
    try ring
  have hQ2 : HasDerivAt (fun s => (4 * A s ^ 2) ^ 2)
      (2 * (4 * A y ^ 2) * (8 * A y * A' y)) y := by
    have h := hQ.pow 2
    refine h.congr_deriv ?_
    ring
  have hQ20 : (4 * A y ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hQ0
  have h := hN.div hQ2 hQ20
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [Pi.div_apply, Pi.sub_apply, w1tDfun]

theorem w1g_hasDerivAt {K D A : ℝ → ℝ} {K' D' A' y : ℝ}
    (hK : HasDerivAt K K' y) (hD : HasDerivAt D D' y) (hA : HasDerivAt A A' y)
    (hA0 : A y ≠ 0) :
    HasDerivAt (fun s => w1gOf K D A s)
      (w1gDfun K (fun _ => K') D (fun _ => D') A (fun _ => A') y) y := by
  have hKD : HasDerivAt (fun s => K s * D s) (K' * D y + K y * D') y := hK.mul hD
  have hQ : HasDerivAt (fun s => A s ^ 2) (2 * A y * A') y := by
    have h := hA.pow 2
    refine h.congr_deriv ?_
    ring
  have hQ0 : A y ^ 2 ≠ 0 := pow_ne_zero 2 hA0
  have h := hKD.div hQ hQ0
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · simp only [w1gDfun]
    field_simp
    try ring
  · intro s
    simp only [Pi.div_apply, Pi.mul_apply, w1gOf]

theorem w1gD_hasDerivAt {K K' D D' A A' : ℝ → ℝ} {K'' D'' A'' y : ℝ}
    (hK : HasDerivAt K (K' y) y) (hK' : HasDerivAt K' K'' y)
    (hD : HasDerivAt D (D' y) y) (hD' : HasDerivAt D' D'' y)
    (hA : HasDerivAt A (A' y) y) (hA' : HasDerivAt A' A'' y) (hA0 : A y ≠ 0) :
    HasDerivAt (fun s => w1gDfun K K' D D' A A' s) (w1gDDOf K K' D D' A A' K'' D'' A'' y) y := by
  have hQ : HasDerivAt (fun s => A s ^ 2) (2 * A y * A' y) y := by
    have h := hA.pow 2
    refine h.congr_deriv ?_
    ring
  have hQ0 : A y ^ 2 ≠ 0 := pow_ne_zero 2 hA0
  have h1 : HasDerivAt (fun s => K' s * D s) (K'' * D y + K' y * D' y) y := hK'.mul hD
  have h0 : HasDerivAt (fun s => K s * D' s) (K' y * D' y + K y * D'') y := hK.mul hD'
  have hS : HasDerivAt (fun s => K' s * D s + K s * D' s)
      (K'' * D y + K' y * D' y + (K' y * D' y + K y * D'')) y := h1.add h0
  have hSq : HasDerivAt (fun s => (K' s * D s + K s * D' s) * A s ^ 2)
      ((K'' * D y + K' y * D' y + (K' y * D' y + K y * D'')) * A y ^ 2
        + (K' y * D y + K y * D' y) * (2 * A y * A' y)) y := hS.mul hQ
  have hAA : HasDerivAt (fun s => A s * A' s) (A' y * A' y + A y * A'') y := hA.mul hA'
  have hKD : HasDerivAt (fun s => 2 * K s * D s)
      (2 * (K' y * D y + K y * D' y)) y := by
    have hc := hasDerivAt_const y (2 : ℝ)
    have h0 := hc.mul (hK.mul hD)
    refine (h0.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.mul_apply]; try ring
  have hT : HasDerivAt (fun s => 2 * K s * D s * (A s * A' s))
      (2 * (K' y * D y + K y * D' y) * (A y * A' y)
        + 2 * K y * D y * (A' y * A' y + A y * A'')) y := hKD.mul hAA
  have hNraw := hSq.sub hT
  have hN : HasDerivAt
      (fun s => (K' s * D s + K s * D' s) * A s ^ 2 - 2 * K s * D s * (A s * A' s))
      ((K'' * D y + 2 * K' y * D' y + K y * D'') * A y ^ 2
        - 2 * K y * D y * ((A' y) ^ 2 + A y * A'')) y := by
    have hder : (K'' * D y + K' y * D' y + (K' y * D' y + K y * D'')) * A y ^ 2
          + (K' y * D y + K y * D' y) * (2 * A y * A' y)
          - (2 * (K' y * D y + K y * D' y) * (A y * A' y)
            + 2 * K y * D y * (A' y * A' y + A y * A''))
        = (K'' * D y + 2 * K' y * D' y + K y * D'') * A y ^ 2
          - 2 * K y * D y * ((A' y) ^ 2 + A y * A'') := by
      ring
    refine (hNraw.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    intro s
    simp only [Pi.sub_apply, Pi.mul_apply]
    try ring
  have hQ2 : HasDerivAt (fun s => (A s ^ 2) ^ 2)
      (2 * (A y ^ 2) * (2 * A y * A' y)) y := by
    have h := hQ.pow 2
    refine h.congr_deriv ?_
    ring
  have hQ20 : (A y ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hQ0
  have h := hN.div hQ2 hQ20
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · simp only [w1gDDOf]
    field_simp
    try ring
  · intro s
    simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, w1gDfun]

theorem w1W_hasDerivAt {N A : ℝ → ℝ} {N' A' y : ℝ}
    (hN : HasDerivAt N N' y) (hA : HasDerivAt A A' y) (hA0 : A y ≠ 0) :
    HasDerivAt (fun s => w1WOf N A s) (w1WDfun N (fun _ => N') A (fun _ => A') y) y := by
  have h := hN.div hA hA0
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · simp only [w1WDfun]
  · intro s
    simp only [Pi.div_apply, w1WOf]

theorem w1WD_hasDerivAt {N N' A A' : ℝ → ℝ} {N'' A'' y : ℝ}
    (hN : HasDerivAt N (N' y) y) (hN' : HasDerivAt N' N'' y)
    (hA : HasDerivAt A (A' y) y) (hA' : HasDerivAt A' A'' y) (hA0 : A y ≠ 0) :
    HasDerivAt (fun s => w1WDfun N N' A A' s) (w1WDDOf N N' A A' N'' A'' y) y := by
  have hM : HasDerivAt (fun s => N' s * A s - N s * A' s)
      (N'' * A y - N y * A'') y := by
    have h := (hN'.mul hA).sub (hN.mul hA')
    refine h.congr_deriv ?_
    ring
  have hQ : HasDerivAt (fun s => A s ^ 2) (2 * A y * A' y) y := by
    have h := hA.pow 2
    refine h.congr_deriv ?_
    ring
  have hQ0 : A y ^ 2 ≠ 0 := pow_ne_zero 2 hA0
  have h := hM.div hQ hQ0
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · simp only [w1WDDOf]
    field_simp
    try ring
  · intro s
    simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply, w1WDfun]

/-! ## 4. Slot definitions and derivative facts -/

/-- A-slot `t = Delta / (4 a_A²)`. -/
noncomputable def w1tA (y4 y5 y6 : ℝ) : ℝ :=
  w1tOf (fun s => w1Dlt y4 s y6) (fun s => w1aA y4 s y6) y5

/-- B-slot `t`. -/
noncomputable def w1tB (y4 y5 y6 : ℝ) : ℝ :=
  w1tOf (fun s => w1Dlt y4 s y6) (fun s => w1aB y4 s y6) y5

/-- C-slot `t`. -/
noncomputable def w1tC (y4 y5 y6 : ℝ) : ℝ :=
  w1tOf (fun s => w1Dlt y4 s y6) (fun s => w1aC y4 s y6) y5

/-- A-slot `t'`. -/
noncomputable def w1tAD (y4 y5 y6 : ℝ) : ℝ :=
  w1tDfun (fun s => w1Dlt y4 s y6) (fun s => w1DltD y4 s y6)
    (fun s => w1aA y4 s y6) (fun s => w1aAD y4 s y6) y5

/-- B-slot `t'`. -/
noncomputable def w1tBD (y4 y5 y6 : ℝ) : ℝ :=
  w1tDfun (fun s => w1Dlt y4 s y6) (fun s => w1DltD y4 s y6)
    (fun s => w1aB y4 s y6) (fun s => w1aBD y4 s y6) y5

/-- C-slot `t'`. -/
noncomputable def w1tCD (y4 y5 y6 : ℝ) : ℝ :=
  w1tDfun (fun s => w1Dlt y4 s y6) (fun s => w1DltD y4 s y6)
    (fun s => w1aC y4 s y6) (fun s => w1aCD y4 s y6) y5

/-- A-slot `t''`. -/
noncomputable def w1tADD (y4 y5 y6 : ℝ) : ℝ :=
  w1tDDOf (fun s => w1Dlt y4 s y6) (fun s => w1DltD y4 s y6)
    (fun s => w1aA y4 s y6) (fun s => w1aAD y4 s y6)
    (w1DltDD y4 y5 y6) (w1aADD y4 y5 y6) y5

/-- B-slot `t''`. -/
noncomputable def w1tBDD (y4 y5 y6 : ℝ) : ℝ :=
  w1tDDOf (fun s => w1Dlt y4 s y6) (fun s => w1DltD y4 s y6)
    (fun s => w1aB y4 s y6) (fun s => w1aBD y4 s y6)
    (w1DltDD y4 y5 y6) (w1aBDD y4 y5 y6) y5

/-- C-slot `t''`. -/
noncomputable def w1tCDD (y4 y5 y6 : ℝ) : ℝ :=
  w1tDDOf (fun s => w1Dlt y4 s y6) (fun s => w1DltD y4 s y6)
    (fun s => w1aC y4 s y6) (fun s => w1aCD y4 s y6)
    (w1DltDD y4 y5 y6) (w1aCDD y4 y5 y6) y5

/-- A-slot `g = 4 y5² Delta / d4_A²`. -/
noncomputable def w1gA (y4 y5 y6 : ℝ) : ℝ :=
  w1gOf (fun s => 4 * (s * s)) (fun s => w1Dlt y4 s y6) (fun s => w1d4A y4 s y6) y5

/-- B-slot `g = 4 y6² Delta / d4_B²`. -/
noncomputable def w1gB (y4 y5 y6 : ℝ) : ℝ :=
  w1gOf (fun _ => 4 * (y6 * y6)) (fun s => w1Dlt y4 s y6) (fun s => w1d4B y4 s y6) y5

/-- C-slot `g = 4 y4² Delta / d4_C²`. -/
noncomputable def w1gC (y4 y5 y6 : ℝ) : ℝ :=
  w1gOf (fun _ => 4 * (y4 * y4)) (fun s => w1Dlt y4 s y6) (fun s => w1d4C y4 s y6) y5

/-- A-slot `g'`. -/
noncomputable def w1gAD (y4 y5 y6 : ℝ) : ℝ :=
  w1gDfun (fun s => 4 * (s * s)) (fun s => 8 * s) (fun s => w1Dlt y4 s y6)
    (fun s => w1DltD y4 s y6) (fun s => w1d4A y4 s y6) (fun s => w1d4AD y4 s y6) y5

/-- B-slot `g'`. -/
noncomputable def w1gBD (y4 y5 y6 : ℝ) : ℝ :=
  w1gDfun (fun _ => 4 * (y6 * y6)) (fun _ => 0) (fun s => w1Dlt y4 s y6)
    (fun s => w1DltD y4 s y6) (fun s => w1d4B y4 s y6) (fun s => w1d4BD y4 s y6) y5

/-- C-slot `g'`. -/
noncomputable def w1gCD (y4 y5 y6 : ℝ) : ℝ :=
  w1gDfun (fun _ => 4 * (y4 * y4)) (fun _ => 0) (fun s => w1Dlt y4 s y6)
    (fun s => w1DltD y4 s y6) (fun s => w1d4C y4 s y6) (fun s => w1d4CD y4 s y6) y5

/-- A-slot `g''`. -/
noncomputable def w1gADD (y4 y5 y6 : ℝ) : ℝ :=
  w1gDDOf (fun s => 4 * (s * s)) (fun s => 8 * s) (fun s => w1Dlt y4 s y6)
    (fun s => w1DltD y4 s y6) (fun s => w1d4A y4 s y6) (fun s => w1d4AD y4 s y6)
    (8) (w1DltDD y4 y5 y6) (w1d4ADD y4 y5 y6) y5

/-- B-slot `g''`. -/
noncomputable def w1gBDD (y4 y5 y6 : ℝ) : ℝ :=
  w1gDDOf (fun _ => 4 * (y6 * y6)) (fun _ => 0) (fun s => w1Dlt y4 s y6)
    (fun s => w1DltD y4 s y6) (fun s => w1d4B y4 s y6) (fun s => w1d4BD y4 s y6)
    (0) (w1DltDD y4 y5 y6) (w1d4BDD y4 y5 y6) y5

/-- C-slot `g''`. -/
noncomputable def w1gCDD (y4 y5 y6 : ℝ) : ℝ :=
  w1gDDOf (fun _ => 4 * (y4 * y4)) (fun _ => 0) (fun s => w1Dlt y4 s y6)
    (fun s => w1DltD y4 s y6) (fun s => w1d4C y4 s y6) (fun s => w1d4CD y4 s y6)
    (0) (w1DltDD y4 y5 y6) (w1d4CDD y4 y5 y6) y5

/-- A-slot `W = 2 y5 / d4_A`. -/
noncomputable def w1WA (y4 y5 y6 : ℝ) : ℝ :=
  w1WOf (fun s => 2 * s) (fun s => w1d4A y4 s y6) y5

/-- B-slot `W = 2 y6 / d4_B`. -/
noncomputable def w1WB (y4 y5 y6 : ℝ) : ℝ :=
  w1WOf (fun _ => 2 * y6) (fun s => w1d4B y4 s y6) y5

/-- C-slot `W = 2 y4 / d4_C`. -/
noncomputable def w1WC (y4 y5 y6 : ℝ) : ℝ :=
  w1WOf (fun _ => 2 * y4) (fun s => w1d4C y4 s y6) y5

/-- A-slot `W'`. -/
noncomputable def w1WAD (y4 y5 y6 : ℝ) : ℝ :=
  w1WDfun (fun s => 2 * s) (fun _ => 2) (fun s => w1d4A y4 s y6)
    (fun s => w1d4AD y4 s y6) y5

/-- B-slot `W'`. -/
noncomputable def w1WBD (y4 y5 y6 : ℝ) : ℝ :=
  w1WDfun (fun _ => 2 * y6) (fun _ => 0) (fun s => w1d4B y4 s y6)
    (fun s => w1d4BD y4 s y6) y5

/-- C-slot `W'`. -/
noncomputable def w1WCD (y4 y5 y6 : ℝ) : ℝ :=
  w1WDfun (fun _ => 2 * y4) (fun _ => 0) (fun s => w1d4C y4 s y6)
    (fun s => w1d4CD y4 s y6) y5

/-- A-slot `W''`. -/
noncomputable def w1WADD (y4 y5 y6 : ℝ) : ℝ :=
  w1WDDOf (fun s => 2 * s) (fun _ => 2) (fun s => w1d4A y4 s y6)
    (fun s => w1d4AD y4 s y6) (0) (w1d4ADD y4 y5 y6) y5

/-- B-slot `W''`. -/
noncomputable def w1WBDD (y4 y5 y6 : ℝ) : ℝ :=
  w1WDDOf (fun _ => 2 * y6) (fun _ => 0) (fun s => w1d4B y4 s y6)
    (fun s => w1d4BD y4 s y6) (0) (w1d4BDD y4 y5 y6) y5

/-- C-slot `W''`. -/
noncomputable def w1WCDD (y4 y5 y6 : ℝ) : ℝ :=
  w1WDDOf (fun _ => 2 * y4) (fun _ => 0) (fun s => w1d4C y4 s y6)
    (fun s => w1d4CD y4 s y6) (0) (w1d4CDD y4 y5 y6) y5

/-! ### Positivity / nonvanishing on the wt1 box -/

/-- `a_A > 0` on the box. -/
theorem w1aA_pos (y4 y5 y6 : ℝ) (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352) (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    0 < w1aA y4 y5 y6 := by
  have hy4 : (0 : ℝ) < y4 := by linarith
  have hy5 : (0 : ℝ) < y5 := by linarith
  have hT1 : (0 : ℝ) < Real.sqrt 2 * y5 * y4 := by positivity
  have hthird : (0 : ℝ) ≤ Real.sqrt 2 * ((y5 * y5) + (y4 * y4) - (y6 * y6)) / 2 := by
    have hsq4 : (6.068 : ℝ) ≤ y4 * y4 := by nlinarith
    have hsq5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith
    have hsq6 : y6 * y6 ≤ (6.07 : ℝ) := by nlinarith
    have hd : (0 : ℝ) ≤ (y5 * y5) + (y4 * y4) - (y6 * y6) := by nlinarith
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hd) (by norm_num)
  have h2t : (0 : ℝ) ≤ y5 * (y4 * y4) / 2 := by positivity
  have h4t : (0 : ℝ) ≤ y4 * (y5 * y5) / 2 := by positivity
  unfold w1aA
  linarith

/-- `a_B > 0` on the box. -/
theorem w1aB_pos (y4 y5 y6 : ℝ) (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352) (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    0 < w1aB y4 y5 y6 := by
  have hy5 : (0 : ℝ) < y5 := by linarith
  have hy6 : (0 : ℝ) < y6 := by linarith
  have hT1 : (0 : ℝ) < Real.sqrt 2 * y6 * y5 := by positivity
  have hthird : (0 : ℝ) ≤ Real.sqrt 2 * ((y6 * y6) + (y5 * y5) - (y4 * y4)) / 2 := by
    have hsq4 : y4 * y4 ≤ (7.03 : ℝ) := by nlinarith
    have hsq5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith
    have hsq6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith
    have hd : (0 : ℝ) ≤ (y6 * y6) + (y5 * y5) - (y4 * y4) := by nlinarith
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hd) (by norm_num)
  have h2t : (0 : ℝ) ≤ y6 * (y5 * y5) / 2 := by positivity
  have h4t : (0 : ℝ) ≤ y5 * (y6 * y6) / 2 := by positivity
  unfold w1aB
  linarith

/-- `a_C > 0` on the box. -/
theorem w1aC_pos (y4 y5 y6 : ℝ) (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352) (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    0 < w1aC y4 y5 y6 := by
  have hy4 : (0 : ℝ) < y4 := by linarith
  have hy6 : (0 : ℝ) < y6 := by linarith
  have hT1 : (0 : ℝ) < Real.sqrt 2 * y4 * y6 := by positivity
  have hthird : (0 : ℝ) ≤ Real.sqrt 2 * ((y4 * y4) + (y6 * y6) - (y5 * y5)) / 2 := by
    have hsq4 : (6.068 : ℝ) ≤ y4 * y4 := by nlinarith
    have hsq5 : y5 * y5 ≤ (6.07 : ℝ) := by nlinarith
    have hsq6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith
    have hd : (0 : ℝ) ≤ (y4 * y4) + (y6 * y6) - (y5 * y5) := by nlinarith
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hd) (by norm_num)
  have h2t : (0 : ℝ) ≤ y4 * (y6 * y6) / 2 := by positivity
  have h4t : (0 : ℝ) ≤ y6 * (y4 * y4) / 2 := by positivity
  unfold w1aC
  linarith

/-- `d4_A > 0` on the box. -/
theorem w1d4A_pos (y4 y5 y6 : ℝ) (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352) (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    0 < w1d4A y4 y5 y6 := by
  have hsq5 : (0 : ℝ) < y5 * y5 := by nlinarith
  have hE : (0 : ℝ) < (y4 * y4) + (y6 * y6) - (y5 * y5) := by
    have hsq4 : (6.068 : ℝ) ≤ y4 * y4 := by nlinarith
    have hsq5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith
    have hsq6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith
    have hsq5h : y5 * y5 ≤ (6.07 : ℝ) := by nlinarith
    nlinarith
  unfold w1d4A
  positivity

/-- `d4_B > 0` on the box. -/
theorem w1d4B_pos (y4 y5 y6 : ℝ) (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352) (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    0 < w1d4B y4 y5 y6 := by
  have hsq6 : (0 : ℝ) < y6 * y6 := by nlinarith
  have hE : (0 : ℝ) < (y5 * y5) + (y4 * y4) - (y6 * y6) := by
    have hsq4 : (6.068 : ℝ) ≤ y4 * y4 := by nlinarith
    have hsq5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith
    have hsq6h : y6 * y6 ≤ (6.07 : ℝ) := by nlinarith
    nlinarith
  unfold w1d4B
  positivity

/-- `d4_C > 0` on the box. -/
theorem w1d4C_pos (y4 y5 y6 : ℝ) (h4l : (2.4635 : ℝ) ≤ y4) (h4h : y4 ≤ 2.6508)
    (h5l : (2 : ℝ) ≤ y5) (h5h : y5 ≤ 2.46352) (h6l : (2 : ℝ) ≤ y6) (h6h : y6 ≤ 2.46352) :
    0 < w1d4C y4 y5 y6 := by
  have hsq4 : (0 : ℝ) < y4 * y4 := by nlinarith
  have hE : (0 : ℝ) < (y6 * y6) + (y5 * y5) - (y4 * y4) := by
    have hsq5 : (4 : ℝ) ≤ y5 * y5 := by nlinarith
    have hsq6 : (4 : ℝ) ≤ y6 * y6 := by nlinarith
    have hsq4h : y4 * y4 ≤ (7.03 : ℝ) := by nlinarith
    nlinarith
  unfold w1d4C
  positivity

/-! ### Slot derivative facts -/

theorem w1tA_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aA y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1tA y4 s y6) (w1tAD y4 y5 y6) y5 := by
  have h := w1t_hasDerivAt (D := fun s => w1Dlt y4 s y6) (A := fun s => w1aA y4 s y6)
      (w1Dlt_hasDerivAt y4 y5 y6) (w1aA_hasDerivAt y4 y5 y6) hA0
  have hder : w1tDfun (fun s => w1Dlt y4 s y6) (fun _ => w1DltD y4 y5 y6)
      (fun s => w1aA y4 s y6) (fun _ => w1aAD y4 y5 y6) y5 = w1tAD y4 y5 y6 := by
    simp only [w1tDfun, w1tAD]
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [w1tA]

theorem w1tB_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aB y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1tB y4 s y6) (w1tBD y4 y5 y6) y5 := by
  have h := w1t_hasDerivAt (D := fun s => w1Dlt y4 s y6) (A := fun s => w1aB y4 s y6)
      (w1Dlt_hasDerivAt y4 y5 y6) (w1aB_hasDerivAt y4 y5 y6) hA0
  have hder : w1tDfun (fun s => w1Dlt y4 s y6) (fun _ => w1DltD y4 y5 y6)
      (fun s => w1aB y4 s y6) (fun _ => w1aBD y4 y5 y6) y5 = w1tBD y4 y5 y6 := by
    simp only [w1tDfun, w1tBD]
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [w1tB]

theorem w1tC_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aC y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1tC y4 s y6) (w1tCD y4 y5 y6) y5 := by
  have h := w1t_hasDerivAt (D := fun s => w1Dlt y4 s y6) (A := fun s => w1aC y4 s y6)
      (w1Dlt_hasDerivAt y4 y5 y6) (w1aC_hasDerivAt y4 y5 y6) hA0
  have hder : w1tDfun (fun s => w1Dlt y4 s y6) (fun _ => w1DltD y4 y5 y6)
      (fun s => w1aC y4 s y6) (fun _ => w1aCD y4 y5 y6) y5 = w1tCD y4 y5 y6 := by
    simp only [w1tDfun, w1tCD]
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [w1tC]

theorem w1tAD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aA y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1tAD y4 s y6) (w1tADD y4 y5 y6) y5 := by
  simpa only [w1tAD, w1tADD] using
    w1tD_hasDerivAt (D := fun s => w1Dlt y4 s y6) (D' := fun s => w1DltD y4 s y6)
      (A := fun s => w1aA y4 s y6) (A' := fun s => w1aAD y4 s y6)
      (w1Dlt_hasDerivAt y4 y5 y6) (w1DltD_hasDerivAt y4 y5 y6)
      (w1aA_hasDerivAt y4 y5 y6) (w1aAD_hasDerivAt y4 y5 y6) hA0

theorem w1tBD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aB y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1tBD y4 s y6) (w1tBDD y4 y5 y6) y5 := by
  simpa only [w1tBD, w1tBDD] using
    w1tD_hasDerivAt (D := fun s => w1Dlt y4 s y6) (D' := fun s => w1DltD y4 s y6)
      (A := fun s => w1aB y4 s y6) (A' := fun s => w1aBD y4 s y6)
      (w1Dlt_hasDerivAt y4 y5 y6) (w1DltD_hasDerivAt y4 y5 y6)
      (w1aB_hasDerivAt y4 y5 y6) (w1aBD_hasDerivAt y4 y5 y6) hA0

theorem w1tCD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aC y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1tCD y4 s y6) (w1tCDD y4 y5 y6) y5 := by
  simpa only [w1tCD, w1tCDD] using
    w1tD_hasDerivAt (D := fun s => w1Dlt y4 s y6) (D' := fun s => w1DltD y4 s y6)
      (A := fun s => w1aC y4 s y6) (A' := fun s => w1aCD y4 s y6)
      (w1Dlt_hasDerivAt y4 y5 y6) (w1DltD_hasDerivAt y4 y5 y6)
      (w1aC_hasDerivAt y4 y5 y6) (w1aCD_hasDerivAt y4 y5 y6) hA0

theorem w1gA_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4A y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1gA y4 s y6) (w1gAD y4 y5 y6) y5 := by
  have hK : HasDerivAt (fun s : ℝ => 4 * (s * s)) (8 * y5) y5 := by
    have h := w1_quad4_deriv 0 4 0 0 y5
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; ring
  have h := w1g_hasDerivAt (K := fun s : ℝ => 4 * (s * s)) (D := fun s => w1Dlt y4 s y6)
      (A := fun s => w1d4A y4 s y6)
      hK (w1Dlt_hasDerivAt y4 y5 y6) (w1d4A_hasDerivAt y4 y5 y6) hA0
  have hder : w1gDfun (fun s : ℝ => 4 * (s * s)) (fun _ => 8 * y5)
      (fun s => w1Dlt y4 s y6) (fun _ => w1DltD y4 y5 y6)
      (fun s => w1d4A y4 s y6) (fun _ => w1d4AD y4 y5 y6) y5 = w1gAD y4 y5 y6 := by
    simp only [w1gDfun, w1gAD]
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [w1gA]

theorem w1gB_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4B y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1gB y4 s y6) (w1gBD y4 y5 y6) y5 := by
  have hK : HasDerivAt (fun _ : ℝ => 4 * (y6 * y6)) 0 y5 :=
    hasDerivAt_const y5 _
  have h := w1g_hasDerivAt (K := fun _ : ℝ => 4 * (y6 * y6)) (D := fun s => w1Dlt y4 s y6)
      (A := fun s => w1d4B y4 s y6)
      hK (w1Dlt_hasDerivAt y4 y5 y6) (w1d4B_hasDerivAt y4 y5 y6) hA0
  have hder : w1gDfun (fun _ : ℝ => 4 * (y6 * y6)) (fun _ => 0)
      (fun s => w1Dlt y4 s y6) (fun _ => w1DltD y4 y5 y6)
      (fun s => w1d4B y4 s y6) (fun _ => w1d4BD y4 y5 y6) y5 = w1gBD y4 y5 y6 := by
    simp only [w1gDfun, w1gBD]
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [w1gB]

theorem w1gC_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4C y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1gC y4 s y6) (w1gCD y4 y5 y6) y5 := by
  have hK : HasDerivAt (fun _ : ℝ => 4 * (y4 * y4)) 0 y5 :=
    hasDerivAt_const y5 _
  have h := w1g_hasDerivAt (K := fun _ : ℝ => 4 * (y4 * y4)) (D := fun s => w1Dlt y4 s y6)
      (A := fun s => w1d4C y4 s y6)
      hK (w1Dlt_hasDerivAt y4 y5 y6) (w1d4C_hasDerivAt y4 y5 y6) hA0
  have hder : w1gDfun (fun _ : ℝ => 4 * (y4 * y4)) (fun _ => 0)
      (fun s => w1Dlt y4 s y6) (fun _ => w1DltD y4 y5 y6)
      (fun s => w1d4C y4 s y6) (fun _ => w1d4CD y4 y5 y6) y5 = w1gCD y4 y5 y6 := by
    simp only [w1gDfun, w1gCD]
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [w1gC]

theorem w1gAD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4A y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1gAD y4 s y6) (w1gADD y4 y5 y6) y5 := by
  have hK : HasDerivAt (fun s : ℝ => 4 * (s * s)) (8 * y5) y5 := by
    have h := w1_quad4_deriv 0 4 0 0 y5
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; ring
  have hK' : HasDerivAt (fun s : ℝ => 8 * s) 8 y5 := by
    simpa using (hasDerivAt_id y5).const_mul 8
  simpa only [w1gAD, w1gADD] using
    w1gD_hasDerivAt (K := fun s : ℝ => 4 * (s * s)) (K' := fun s : ℝ => 8 * s)
      (D := fun s => w1Dlt y4 s y6) (D' := fun s => w1DltD y4 s y6)
      (A := fun s => w1d4A y4 s y6) (A' := fun s => w1d4AD y4 s y6)
      hK hK' (w1Dlt_hasDerivAt y4 y5 y6) (w1DltD_hasDerivAt y4 y5 y6)
      (w1d4A_hasDerivAt y4 y5 y6) (w1d4AD_hasDerivAt y4 y5 y6) hA0

theorem w1gBD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4B y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1gBD y4 s y6) (w1gBDD y4 y5 y6) y5 := by
  have hK : HasDerivAt (fun _ : ℝ => 4 * (y6 * y6)) 0 y5 := hasDerivAt_const y5 _
  have hK' : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 y5 := hasDerivAt_const y5 0
  simpa only [w1gBD, w1gBDD] using
    w1gD_hasDerivAt (K := fun _ : ℝ => 4 * (y6 * y6)) (K' := fun _ : ℝ => (0 : ℝ))
      (D := fun s => w1Dlt y4 s y6) (D' := fun s => w1DltD y4 s y6)
      (A := fun s => w1d4B y4 s y6) (A' := fun s => w1d4BD y4 s y6)
      hK hK' (w1Dlt_hasDerivAt y4 y5 y6) (w1DltD_hasDerivAt y4 y5 y6)
      (w1d4B_hasDerivAt y4 y5 y6) (w1d4BD_hasDerivAt y4 y5 y6) hA0

theorem w1gCD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4C y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1gCD y4 s y6) (w1gCDD y4 y5 y6) y5 := by
  have hK : HasDerivAt (fun _ : ℝ => 4 * (y4 * y4)) 0 y5 := hasDerivAt_const y5 _
  have hK' : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 y5 := hasDerivAt_const y5 0
  simpa only [w1gCD, w1gCDD] using
    w1gD_hasDerivAt (K := fun _ : ℝ => 4 * (y4 * y4)) (K' := fun _ : ℝ => (0 : ℝ))
      (D := fun s => w1Dlt y4 s y6) (D' := fun s => w1DltD y4 s y6)
      (A := fun s => w1d4C y4 s y6) (A' := fun s => w1d4CD y4 s y6)
      hK hK' (w1Dlt_hasDerivAt y4 y5 y6) (w1DltD_hasDerivAt y4 y5 y6)
      (w1d4C_hasDerivAt y4 y5 y6) (w1d4CD_hasDerivAt y4 y5 y6) hA0

theorem w1WA_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4A y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1WA y4 s y6) (w1WAD y4 y5 y6) y5 := by
  have hN : HasDerivAt (fun s : ℝ => 2 * s) 2 y5 := by
    simpa using (hasDerivAt_id y5).const_mul 2
  have h := w1W_hasDerivAt (N := fun s : ℝ => 2 * s) (A := fun s => w1d4A y4 s y6)
      hN (w1d4A_hasDerivAt y4 y5 y6) hA0
  have hder : w1WDfun (fun s : ℝ => 2 * s) (fun _ => 2)
      (fun s => w1d4A y4 s y6) (fun _ => w1d4AD y4 y5 y6) y5 = w1WAD y4 y5 y6 := by
    simp only [w1WDfun, w1WAD]
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [w1WA]

theorem w1WB_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4B y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1WB y4 s y6) (w1WBD y4 y5 y6) y5 := by
  have hN : HasDerivAt (fun _ : ℝ => 2 * y6) 0 y5 := hasDerivAt_const y5 _
  have h := w1W_hasDerivAt (N := fun _ : ℝ => 2 * y6) (A := fun s => w1d4B y4 s y6)
      hN (w1d4B_hasDerivAt y4 y5 y6) hA0
  have hder : w1WDfun (fun _ : ℝ => 2 * y6) (fun _ => 0)
      (fun s => w1d4B y4 s y6) (fun _ => w1d4BD y4 y5 y6) y5 = w1WBD y4 y5 y6 := by
    simp only [w1WDfun, w1WBD]
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [w1WB]

theorem w1WC_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4C y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1WC y4 s y6) (w1WCD y4 y5 y6) y5 := by
  have hN : HasDerivAt (fun _ : ℝ => 2 * y4) 0 y5 := hasDerivAt_const y5 _
  have h := w1W_hasDerivAt (N := fun _ : ℝ => 2 * y4) (A := fun s => w1d4C y4 s y6)
      hN (w1d4C_hasDerivAt y4 y5 y6) hA0
  have hder : w1WDfun (fun _ : ℝ => 2 * y4) (fun _ => 0)
      (fun s => w1d4C y4 s y6) (fun _ => w1d4CD y4 y5 y6) y5 = w1WCD y4 y5 y6 := by
    simp only [w1WDfun, w1WCD]
  refine (h.congr_deriv hder).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  simp only [w1WC]

theorem w1WAD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4A y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1WAD y4 s y6) (w1WADD y4 y5 y6) y5 := by
  have hN : HasDerivAt (fun s : ℝ => 2 * s) 2 y5 := by
    simpa using (hasDerivAt_id y5).const_mul 2
  have hN' : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 y5 := hasDerivAt_const y5 _
  simpa only [w1WAD, w1WADD] using
    w1WD_hasDerivAt (N := fun s : ℝ => 2 * s) (N' := fun _ : ℝ => (2 : ℝ))
      (A := fun s => w1d4A y4 s y6) (A' := fun s => w1d4AD y4 s y6)
      hN hN' (w1d4A_hasDerivAt y4 y5 y6) (w1d4AD_hasDerivAt y4 y5 y6) hA0

theorem w1WBD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4B y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1WBD y4 s y6) (w1WBDD y4 y5 y6) y5 := by
  have hN : HasDerivAt (fun _ : ℝ => 2 * y6) 0 y5 := hasDerivAt_const y5 _
  have hN' : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 y5 := hasDerivAt_const y5 0
  simpa only [w1WBD, w1WBDD] using
    w1WD_hasDerivAt (N := fun _ : ℝ => 2 * y6) (N' := fun _ : ℝ => (0 : ℝ))
      (A := fun s => w1d4B y4 s y6) (A' := fun s => w1d4BD y4 s y6)
      hN hN' (w1d4B_hasDerivAt y4 y5 y6) (w1d4BD_hasDerivAt y4 y5 y6) hA0

theorem w1WCD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4C y4 y5 y6 ≠ 0) :
    HasDerivAt (fun s => w1WCD y4 s y6) (w1WCDD y4 y5 y6) y5 := by
  have hN : HasDerivAt (fun _ : ℝ => 2 * y4) 0 y5 := hasDerivAt_const y5 _
  have hN' : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 y5 := hasDerivAt_const y5 0
  simpa only [w1WCD, w1WCDD] using
    w1WD_hasDerivAt (N := fun _ : ℝ => 2 * y4) (N' := fun _ : ℝ => (0 : ℝ))
      (A := fun s => w1d4C y4 s y6) (A' := fun s => w1d4CD y4 s y6)
      hN hN' (w1d4C_hasDerivAt y4 y5 y6) (w1d4CD_hasDerivAt y4 y5 y6) hA0

/-! ## 5. Slot values, unfoldings, and the w1aF derivative chain -/

/-! ### Unfolding of the `solEuler` / `dih` slots into pinned form -/

theorem w1_seA_unfold (y4 y5 y6 : ℝ) (h4 : 0 ≤ y4) (h5 : 0 ≤ y5) :
    solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 =
      matan (w1tA y4 y5 y6) / w1aA y4 y5 y6 := by
  simp only [solEulerXDivSqrtdelta]
  rw [w1_dltA]
  have ha : (Real.sqrt (y5 * y5 * 2 * (y4 * y4)) +
      Real.sqrt (y5 * y5) * (2 + y4 * y4 - 2) / 2 +
      Real.sqrt 2 * ((y5 * y5) + (y4 * y4) - (y6 * y6)) / 2 +
      Real.sqrt (y4 * y4) * ((y5 * y5) + 2 - 2) / 2) = w1aA y4 y5 y6 := by
    unfold w1aA
    rw [show Real.sqrt (y5 * y5 * 2 * (y4 * y4)) = Real.sqrt 2 * y5 * y4 by
      rw [show y5 * y5 * 2 * (y4 * y4) = 2 * (y5 * y4) ^ 2 by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by positivity)]
      ring,
      Real.sqrt_mul_self h5, Real.sqrt_mul_self h4]
    ring
  rw [ha]
  simp only [w1tA, w1tOf]

theorem w1_seB_unfold (y4 y5 y6 : ℝ) (h4 : 0 ≤ y4) (h5 : 0 ≤ y5) (h6 : 0 ≤ y6) :
    solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 =
      matan (w1tB y4 y5 y6) / w1aB y4 y5 y6 := by
  simp only [solEulerXDivSqrtdelta]
  rw [w1_dltB]
  have ha : (Real.sqrt (y6 * y6 * 2 * (y5 * y5)) +
      Real.sqrt (y6 * y6) * (2 + y5 * y5 - 2) / 2 +
      Real.sqrt 2 * ((y6 * y6) + (y5 * y5) - (y4 * y4)) / 2 +
      Real.sqrt (y5 * y5) * ((y6 * y6) + 2 - 2) / 2) = w1aB y4 y5 y6 := by
    unfold w1aB
    rw [show Real.sqrt (y6 * y6 * 2 * (y5 * y5)) = Real.sqrt 2 * y6 * y5 by
      rw [show y6 * y6 * 2 * (y5 * y5) = 2 * (y6 * y5) ^ 2 by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by positivity)]
      ring,
      Real.sqrt_mul_self h6, Real.sqrt_mul_self h5]
    ring
  rw [ha]
  simp only [w1tB, w1tOf]

theorem w1_seC_unfold (y4 y5 y6 : ℝ) (h4 : 0 ≤ y4) (h5 : 0 ≤ y5) (h6 : 0 ≤ y6) :
    solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 =
      matan (w1tC y4 y5 y6) / w1aC y4 y5 y6 := by
  simp only [solEulerXDivSqrtdelta]
  rw [w1_dltC]
  have ha : (Real.sqrt (y4 * y4 * 2 * (y6 * y6)) +
      Real.sqrt (y4 * y4) * (2 + y6 * y6 - 2) / 2 +
      Real.sqrt 2 * ((y4 * y4) + (y6 * y6) - (y5 * y5)) / 2 +
      Real.sqrt (y6 * y6) * ((y4 * y4) + 2 - 2) / 2) = w1aC y4 y5 y6 := by
    unfold w1aC
    rw [show Real.sqrt (y4 * y4 * 2 * (y6 * y6)) = Real.sqrt 2 * y4 * y6 by
      rw [show y4 * y4 * 2 * (y6 * y6) = 2 * (y4 * y6) ^ 2 by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by positivity)]
      ring,
      Real.sqrt_mul_self h4, Real.sqrt_mul_self h6]
    ring
  rw [ha]
  simp only [w1tC, w1tOf]

theorem w1_dihA_unfold (y4 y5 y6 : ℝ) (h5 : 0 ≤ y5) :
    dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 =
      w1WA y4 y5 y6 * matan (w1gA y4 y5 y6) := by
  simp only [dihXDivSqrtdeltaPosbranch]
  rw [w1_dltA, w1_d4A]
  have hs : Real.sqrt (4 * (y5 * y5)) = 2 * y5 := by
    rw [show 4 * (y5 * y5) = (2 * y5) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hs]
  simp only [w1WA, w1WOf, w1gA, w1gOf]

theorem w1_dihB_unfold (y4 y5 y6 : ℝ) (h6 : 0 ≤ y6) :
    dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 =
      w1WB y4 y5 y6 * matan (w1gB y4 y5 y6) := by
  simp only [dihXDivSqrtdeltaPosbranch]
  rw [w1_dltB, w1_d4B]
  have hs : Real.sqrt (4 * (y6 * y6)) = 2 * y6 := by
    rw [show 4 * (y6 * y6) = (2 * y6) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hs]
  simp only [w1WB, w1WOf, w1gB, w1gOf]

theorem w1_dihC_unfold (y4 y5 y6 : ℝ) (h4 : 0 ≤ y4) :
    dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 =
      w1WC y4 y5 y6 * matan (w1gC y4 y5 y6) := by
  simp only [dihXDivSqrtdeltaPosbranch]
  rw [w1_dltC, w1_d4C]
  have hs : Real.sqrt (4 * (y4 * y4)) = 2 * y4 := by
    rw [show 4 * (y4 * y4) = (2 * y4) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [hs]
  simp only [w1WC, w1WOf, w1gC, w1gOf]

/-! ### Slot D1/D2 values -/

/-- A-slot level-1 value. -/
noncomputable def w1SEAD (y4 y5 y6 : ℝ) : ℝ :=
  matanD (w1tA y4 y5 y6) * (w1tAD y4 y5 y6 / w1aA y4 y5 y6)
    - matan (w1tA y4 y5 y6) * (w1aAD y4 y5 y6 / (w1aA y4 y5 y6) ^ 2)

/-- B-slot level-1 value. -/
noncomputable def w1SEBD (y4 y5 y6 : ℝ) : ℝ :=
  matanD (w1tB y4 y5 y6) * (w1tBD y4 y5 y6 / w1aB y4 y5 y6)
    - matan (w1tB y4 y5 y6) * (w1aBD y4 y5 y6 / (w1aB y4 y5 y6) ^ 2)

/-- C-slot level-1 value. -/
noncomputable def w1SECD (y4 y5 y6 : ℝ) : ℝ :=
  matanD (w1tC y4 y5 y6) * (w1tCD y4 y5 y6 / w1aC y4 y5 y6)
    - matan (w1tC y4 y5 y6) * (w1aCD y4 y5 y6 / (w1aC y4 y5 y6) ^ 2)

/-- A-slot level-2 value. -/
noncomputable def w1SEADD (y4 y5 y6 : ℝ) : ℝ :=
  matanDD (w1tA y4 y5 y6) * (w1tAD y4 y5 y6) ^ 2 / w1aA y4 y5 y6
    + matanD (w1tA y4 y5 y6) *
        ((w1tADD y4 y5 y6 * w1aA y4 y5 y6 - 2 * w1tAD y4 y5 y6 * w1aAD y4 y5 y6) /
          (w1aA y4 y5 y6) ^ 2)
    + matan (w1tA y4 y5 y6) *
        ((2 * (w1aAD y4 y5 y6) ^ 2 - w1aA y4 y5 y6 * w1aADD y4 y5 y6) /
          (w1aA y4 y5 y6) ^ 3)

/-- B-slot level-2 value. -/
noncomputable def w1SEBDD (y4 y5 y6 : ℝ) : ℝ :=
  matanDD (w1tB y4 y5 y6) * (w1tBD y4 y5 y6) ^ 2 / w1aB y4 y5 y6
    + matanD (w1tB y4 y5 y6) *
        ((w1tBDD y4 y5 y6 * w1aB y4 y5 y6 - 2 * w1tBD y4 y5 y6 * w1aBD y4 y5 y6) /
          (w1aB y4 y5 y6) ^ 2)
    + matan (w1tB y4 y5 y6) *
        ((2 * (w1aBD y4 y5 y6) ^ 2 - w1aB y4 y5 y6 * w1aBDD y4 y5 y6) /
          (w1aB y4 y5 y6) ^ 3)

/-- C-slot level-2 value. -/
noncomputable def w1SECDD (y4 y5 y6 : ℝ) : ℝ :=
  matanDD (w1tC y4 y5 y6) * (w1tCD y4 y5 y6) ^ 2 / w1aC y4 y5 y6
    + matanD (w1tC y4 y5 y6) *
        ((w1tCDD y4 y5 y6 * w1aC y4 y5 y6 - 2 * w1tCD y4 y5 y6 * w1aCD y4 y5 y6) /
          (w1aC y4 y5 y6) ^ 2)
    + matan (w1tC y4 y5 y6) *
        ((2 * (w1aCD y4 y5 y6) ^ 2 - w1aC y4 y5 y6 * w1aCDD y4 y5 y6) /
          (w1aC y4 y5 y6) ^ 3)

/-- A-slot dih value. -/
noncomputable def w1DIHA (y4 y5 y6 : ℝ) : ℝ := w1WA y4 y5 y6 * matan (w1gA y4 y5 y6)

/-- B-slot dih value. -/
noncomputable def w1DIHB (y4 y5 y6 : ℝ) : ℝ := w1WB y4 y5 y6 * matan (w1gB y4 y5 y6)

/-- C-slot dih value. -/
noncomputable def w1DIHC (y4 y5 y6 : ℝ) : ℝ := w1WC y4 y5 y6 * matan (w1gC y4 y5 y6)

/-- A-slot dih level-1 value. -/
noncomputable def w1DIHAD (y4 y5 y6 : ℝ) : ℝ :=
  w1WAD y4 y5 y6 * matan (w1gA y4 y5 y6)
    + w1WA y4 y5 y6 * (matanD (w1gA y4 y5 y6) * w1gAD y4 y5 y6)

/-- B-slot dih level-1 value. -/
noncomputable def w1DIHBD (y4 y5 y6 : ℝ) : ℝ :=
  w1WBD y4 y5 y6 * matan (w1gB y4 y5 y6)
    + w1WB y4 y5 y6 * (matanD (w1gB y4 y5 y6) * w1gBD y4 y5 y6)

/-- C-slot dih level-1 value. -/
noncomputable def w1DIHCD (y4 y5 y6 : ℝ) : ℝ :=
  w1WCD y4 y5 y6 * matan (w1gC y4 y5 y6)
    + w1WC y4 y5 y6 * (matanD (w1gC y4 y5 y6) * w1gCD y4 y5 y6)

/-- A-slot dih level-2 value. -/
noncomputable def w1DIHADD (y4 y5 y6 : ℝ) : ℝ :=
  w1WADD y4 y5 y6 * matan (w1gA y4 y5 y6)
    + 2 * w1WAD y4 y5 y6 * w1gAD y4 y5 y6 * matanD (w1gA y4 y5 y6)
    + w1WA y4 y5 y6 * (matanDD (w1gA y4 y5 y6) * (w1gAD y4 y5 y6) ^ 2)
    + w1WA y4 y5 y6 * (matanD (w1gA y4 y5 y6) * w1gADD y4 y5 y6)

/-- B-slot dih level-2 value. -/
noncomputable def w1DIHBDD (y4 y5 y6 : ℝ) : ℝ :=
  w1WBDD y4 y5 y6 * matan (w1gB y4 y5 y6)
    + 2 * w1WBD y4 y5 y6 * w1gBD y4 y5 y6 * matanD (w1gB y4 y5 y6)
    + w1WB y4 y5 y6 * (matanDD (w1gB y4 y5 y6) * (w1gBD y4 y5 y6) ^ 2)
    + w1WB y4 y5 y6 * (matanD (w1gB y4 y5 y6) * w1gBDD y4 y5 y6)

/-- C-slot dih level-2 value. -/
noncomputable def w1DIHCDD (y4 y5 y6 : ℝ) : ℝ :=
  w1WCDD y4 y5 y6 * matan (w1gC y4 y5 y6)
    + 2 * w1WCD y4 y5 y6 * w1gCD y4 y5 y6 * matanD (w1gC y4 y5 y6)
    + w1WC y4 y5 y6 * (matanDD (w1gC y4 y5 y6) * (w1gCD y4 y5 y6) ^ 2)
    + w1WC y4 y5 y6 * (matanD (w1gC y4 y5 y6) * w1gCDD y4 y5 y6)

/-! ### Slot `HasDerivAt` facts -/

theorem w1SEA_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aA y4 y5 y6 ≠ 0)
    (ht : -1 < w1tA y4 y5 y6) :
    HasDerivAt (fun s => matan (w1tA y4 s y6) / w1aA y4 s y6)
      (w1SEAD y4 y5 y6) y5 := by
  have h := w1_se_hasDerivAt (w1tA_hasDerivAt y4 y5 y6 hA0)
    (w1aA_hasDerivAt y4 y5 y6) hA0 ht
  have hder : matanD (w1tA y4 y5 y6) * w1tAD y4 y5 y6 / w1aA y4 y5 y6
      - matan (w1tA y4 y5 y6) * w1aAD y4 y5 y6 / (w1aA y4 y5 y6) ^ 2
      = w1SEAD y4 y5 y6 := by
    simp only [w1SEAD]
    ring
  exact h.congr_deriv hder

theorem w1SEB_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aB y4 y5 y6 ≠ 0)
    (ht : -1 < w1tB y4 y5 y6) :
    HasDerivAt (fun s => matan (w1tB y4 s y6) / w1aB y4 s y6)
      (w1SEBD y4 y5 y6) y5 := by
  have h := w1_se_hasDerivAt (w1tB_hasDerivAt y4 y5 y6 hA0)
    (w1aB_hasDerivAt y4 y5 y6) hA0 ht
  have hder : matanD (w1tB y4 y5 y6) * w1tBD y4 y5 y6 / w1aB y4 y5 y6
      - matan (w1tB y4 y5 y6) * w1aBD y4 y5 y6 / (w1aB y4 y5 y6) ^ 2
      = w1SEBD y4 y5 y6 := by
    simp only [w1SEBD]
    ring
  exact h.congr_deriv hder

theorem w1SEC_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aC y4 y5 y6 ≠ 0)
    (ht : -1 < w1tC y4 y5 y6) :
    HasDerivAt (fun s => matan (w1tC y4 s y6) / w1aC y4 s y6)
      (w1SECD y4 y5 y6) y5 := by
  have h := w1_se_hasDerivAt (w1tC_hasDerivAt y4 y5 y6 hA0)
    (w1aC_hasDerivAt y4 y5 y6) hA0 ht
  have hder : matanD (w1tC y4 y5 y6) * w1tCD y4 y5 y6 / w1aC y4 y5 y6
      - matan (w1tC y4 y5 y6) * w1aCD y4 y5 y6 / (w1aC y4 y5 y6) ^ 2
      = w1SECD y4 y5 y6 := by
    simp only [w1SECD]
    ring
  exact h.congr_deriv hder

theorem w1DIHA_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4A y4 y5 y6 ≠ 0)
    (ht : -1 < w1gA y4 y5 y6) :
    HasDerivAt (fun s => w1WA y4 s y6 * matan (w1gA y4 s y6))
      (w1DIHAD y4 y5 y6) y5 := by
  have h := w1_dih_hasDerivAt (w1gA_hasDerivAt y4 y5 y6 hA0)
    (w1WA_hasDerivAt y4 y5 y6 hA0) ht
  have hder : w1WAD y4 y5 y6 * matan (w1gA y4 y5 y6)
      + w1WA y4 y5 y6 * (matanD (w1gA y4 y5 y6) * w1gAD y4 y5 y6)
      = w1DIHAD y4 y5 y6 := by
    simp only [w1DIHAD]
  exact h.congr_deriv hder

theorem w1DIHB_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4B y4 y5 y6 ≠ 0)
    (ht : -1 < w1gB y4 y5 y6) :
    HasDerivAt (fun s => w1WB y4 s y6 * matan (w1gB y4 s y6))
      (w1DIHBD y4 y5 y6) y5 := by
  have h := w1_dih_hasDerivAt (w1gB_hasDerivAt y4 y5 y6 hA0)
    (w1WB_hasDerivAt y4 y5 y6 hA0) ht
  have hder : w1WBD y4 y5 y6 * matan (w1gB y4 y5 y6)
      + w1WB y4 y5 y6 * (matanD (w1gB y4 y5 y6) * w1gBD y4 y5 y6)
      = w1DIHBD y4 y5 y6 := by
    simp only [w1DIHBD]
  exact h.congr_deriv hder

theorem w1DIHC_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4C y4 y5 y6 ≠ 0)
    (ht : -1 < w1gC y4 y5 y6) :
    HasDerivAt (fun s => w1WC y4 s y6 * matan (w1gC y4 s y6))
      (w1DIHCD y4 y5 y6) y5 := by
  have h := w1_dih_hasDerivAt (w1gC_hasDerivAt y4 y5 y6 hA0)
    (w1WC_hasDerivAt y4 y5 y6 hA0) ht
  have hder : w1WCD y4 y5 y6 * matan (w1gC y4 y5 y6)
      + w1WC y4 y5 y6 * (matanD (w1gC y4 y5 y6) * w1gCD y4 y5 y6)
      = w1DIHCD y4 y5 y6 := by
    simp only [w1DIHCD]
  exact h.congr_deriv hder

theorem w1SEAD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aA y4 y5 y6 ≠ 0)
    (ht : -1 < w1tA y4 y5 y6) :
    HasDerivAt (fun s => w1SEAD y4 s y6) (w1SEADD y4 y5 y6) y5 := by
  have h := w1_se_hasDerivAt2 (T := fun s => w1tA y4 s y6) (T' := fun s => w1tAD y4 s y6)
    (A := fun s => w1aA y4 s y6) (A' := fun s => w1aAD y4 s y6)
    (T'' := w1tADD y4 y5 y6) (A'' := w1aADD y4 y5 y6)
    (w1tA_hasDerivAt y4 y5 y6 hA0) (w1tAD_hasDerivAt y4 y5 y6 hA0)
    (w1aA_hasDerivAt y4 y5 y6) (w1aAD_hasDerivAt y4 y5 y6) hA0 ht
  simpa only [w1SEAD, w1SEADD] using h

theorem w1SEBD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aB y4 y5 y6 ≠ 0)
    (ht : -1 < w1tB y4 y5 y6) :
    HasDerivAt (fun s => w1SEBD y4 s y6) (w1SEBDD y4 y5 y6) y5 := by
  have h := w1_se_hasDerivAt2 (T := fun s => w1tB y4 s y6) (T' := fun s => w1tBD y4 s y6)
    (A := fun s => w1aB y4 s y6) (A' := fun s => w1aBD y4 s y6)
    (T'' := w1tBDD y4 y5 y6) (A'' := w1aBDD y4 y5 y6)
    (w1tB_hasDerivAt y4 y5 y6 hA0) (w1tBD_hasDerivAt y4 y5 y6 hA0)
    (w1aB_hasDerivAt y4 y5 y6) (w1aBD_hasDerivAt y4 y5 y6) hA0 ht
  simpa only [w1SEBD, w1SEBDD] using h

theorem w1SECD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1aC y4 y5 y6 ≠ 0)
    (ht : -1 < w1tC y4 y5 y6) :
    HasDerivAt (fun s => w1SECD y4 s y6) (w1SECDD y4 y5 y6) y5 := by
  have h := w1_se_hasDerivAt2 (T := fun s => w1tC y4 s y6) (T' := fun s => w1tCD y4 s y6)
    (A := fun s => w1aC y4 s y6) (A' := fun s => w1aCD y4 s y6)
    (T'' := w1tCDD y4 y5 y6) (A'' := w1aCDD y4 y5 y6)
    (w1tC_hasDerivAt y4 y5 y6 hA0) (w1tCD_hasDerivAt y4 y5 y6 hA0)
    (w1aC_hasDerivAt y4 y5 y6) (w1aCD_hasDerivAt y4 y5 y6) hA0 ht
  simpa only [w1SECD, w1SECDD] using h

theorem w1DIHAD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4A y4 y5 y6 ≠ 0)
    (ht : -1 < w1gA y4 y5 y6) :
    HasDerivAt (fun s => w1DIHAD y4 s y6) (w1DIHADD y4 y5 y6) y5 := by
  have h := w1_dih_hasDerivAt2 (T := fun s => w1gA y4 s y6) (T' := fun s => w1gAD y4 s y6)
    (W := fun s => w1WA y4 s y6) (W' := fun s => w1WAD y4 s y6)
    (T'' := w1gADD y4 y5 y6) (W'' := w1WADD y4 y5 y6)
    (w1gA_hasDerivAt y4 y5 y6 hA0) (w1gAD_hasDerivAt y4 y5 y6 hA0)
    (w1WA_hasDerivAt y4 y5 y6 hA0) (w1WAD_hasDerivAt y4 y5 y6 hA0) ht
  simpa only [w1DIHAD, w1DIHADD] using h

theorem w1DIHBD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4B y4 y5 y6 ≠ 0)
    (ht : -1 < w1gB y4 y5 y6) :
    HasDerivAt (fun s => w1DIHBD y4 s y6) (w1DIHBDD y4 y5 y6) y5 := by
  have h := w1_dih_hasDerivAt2 (T := fun s => w1gB y4 s y6) (T' := fun s => w1gBD y4 s y6)
    (W := fun s => w1WB y4 s y6) (W' := fun s => w1WBD y4 s y6)
    (T'' := w1gBDD y4 y5 y6) (W'' := w1WBDD y4 y5 y6)
    (w1gB_hasDerivAt y4 y5 y6 hA0) (w1gBD_hasDerivAt y4 y5 y6 hA0)
    (w1WB_hasDerivAt y4 y5 y6 hA0) (w1WBD_hasDerivAt y4 y5 y6 hA0) ht
  simpa only [w1DIHBD, w1DIHBDD] using h

theorem w1DIHCD_hasDerivAt (y4 y5 y6 : ℝ) (hA0 : w1d4C y4 y5 y6 ≠ 0)
    (ht : -1 < w1gC y4 y5 y6) :
    HasDerivAt (fun s => w1DIHCD y4 s y6) (w1DIHCDD y4 y5 y6) y5 := by
  have h := w1_dih_hasDerivAt2 (T := fun s => w1gC y4 s y6) (T' := fun s => w1gCD y4 s y6)
    (W := fun s => w1WC y4 s y6) (W' := fun s => w1WCD y4 s y6)
    (T'' := w1gCDD y4 y5 y6) (W'' := w1WCDD y4 y5 y6)
    (w1gC_hasDerivAt y4 y5 y6 hA0) (w1gCD_hasDerivAt y4 y5 y6 hA0)
    (w1WC_hasDerivAt y4 y5 y6 hA0) (w1WCD_hasDerivAt y4 y5 y6 hA0) ht
  simpa only [w1DIHCD, w1DIHCDD] using h

/-! ### The assembled y5-slice derivative chain -/

/-- The explicit y5-slice function of the left kernel (pinned form). -/
noncomputable def w1Fex (y4 y6 : ℝ) (s : ℝ) : ℝ :=
  1 / 12
    - (2 * mm1 / Real.pi) *
        (matan (w1tA y4 s y6) / w1aA y4 s y6
          + matan (w1tB y4 s y6) / w1aB y4 s y6
          + matan (w1tC y4 s y6) / w1aC y4 s y6)
    + (8 * mm2 / Real.pi) *
        (lfun (y4 * 0.5) * h0cut y4 * (w1WC y4 s y6 * matan (w1gC y4 s y6))
          + lfun (s * 0.5) * 1 * (w1WA y4 s y6 * matan (w1gA y4 s y6))
          + lfun (y6 * 0.5) * 1 * (w1WB y4 s y6 * matan (w1gB y4 s y6)))
    - 0.008 * (w1WC y4 s y6 * matan (w1gC y4 s y6))

/-- Level-1 derivative value of `w1aF` in the y5 slot (SCOUT §1.1 `D1`,
clean matan-linear form). -/
noncomputable def w1F1 (y4 y5 y6 : ℝ) : ℝ :=
  - (2 * mm1 / Real.pi) * (w1SEAD y4 y5 y6 + w1SEBD y4 y5 y6 + w1SECD y4 y5 y6)
    + (8 * mm2 / Real.pi) *
        (lfun (y4 * 0.5) * h0cut y4 * w1DIHCD y4 y5 y6
          + (-(25 / 13) * w1DIHA y4 y5 y6
            + lfun (y5 * 0.5) * w1DIHAD y4 y5 y6)
          + lfun (y6 * 0.5) * w1DIHBD y4 y5 y6)
    - 0.008 * w1DIHCD y4 y5 y6

/-- Level-2 derivative value of `w1aF` in the y5 slot (SCOUT §1.1 `D2`,
clean matan-linear form). -/
noncomputable def w1F2 (y4 y5 y6 : ℝ) : ℝ :=
  - (2 * mm1 / Real.pi) * (w1SEADD y4 y5 y6 + w1SEBDD y4 y5 y6 + w1SECDD y4 y5 y6)
    + (8 * mm2 / Real.pi) *
        (lfun (y4 * 0.5) * h0cut y4 * w1DIHCDD y4 y5 y6
          + (2 * (-(25 / 13)) * w1DIHAD y4 y5 y6
            + lfun (y5 * 0.5) * w1DIHADD y4 y5 y6)
          + lfun (y6 * 0.5) * w1DIHBDD y4 y5 y6)
    - 0.008 * w1DIHCDD y4 y5 y6

theorem w1_lfun_hasDerivAt (y : ℝ) :
    HasDerivAt (fun s : ℝ => lfun (s * 0.5)) (-(25 / 13)) y := by
  have hid : HasDerivAt (fun s : ℝ => s * 0.5) (1 * 0.5) y := by
    have h := (hasDerivAt_id y).const_mul (1 / 2)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s; simp only [Pi.smul_apply, smul_eq_mul, id_eq]; ring
  have hsub : HasDerivAt (fun s : ℝ => h0 - s * 0.5) (0 - 1 * 0.5) y :=
    (hasDerivAt_const y h0).sub hid
  have h := hsub.div_const (h0 - 1)
  have hval : (0 - 1 * 0.5) / (h0 - 1) = -(25 / 13) := by
    norm_num [h0]
  rw [hval] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  unfold lfun
  rfl

theorem w1aF_hasDerivAt_y5 (y4 y5 y6 : ℝ)
    (h4 : 0 ≤ y4) (h5 : 0 < y5) (h6 : 0 ≤ y6)
    (hA0 : w1aA y4 y5 y6 ≠ 0) (hB0 : w1aB y4 y5 y6 ≠ 0) (hC0 : w1aC y4 y5 y6 ≠ 0)
    (hdA0 : w1d4A y4 y5 y6 ≠ 0) (hdB0 : w1d4B y4 y5 y6 ≠ 0) (hdC0 : w1d4C y4 y5 y6 ≠ 0)
    (htA : -1 < w1tA y4 y5 y6) (htB : -1 < w1tB y4 y5 y6) (htC : -1 < w1tC y4 y5 y6)
    (hgA : -1 < w1gA y4 y5 y6) (hgB : -1 < w1gB y4 y5 y6) (hgC : -1 < w1gC y4 y5 y6) :
    HasDerivAt (fun s => w1aF y4 s y6) (w1F1 y4 y5 y6) y5 := by
  have hfun : (fun s => w1aF y4 s y6) =ᶠ[𝓝 y5] w1Fex y4 y6 := by
    filter_upwards [Ioo_mem_nhds h5 (show y5 < y5 + 1 by linarith)] with s hs
    unfold w1aF
    rw [nb21_w1aG_explicit y4 s y6 h4 hs.1.le h6,
      nb21_w1aD_explicit]
    rw [w1_seA_unfold y4 s y6 h4 hs.1.le, w1_seB_unfold y4 s y6 h4 hs.1.le h6,
      w1_seC_unfold y4 s y6 h4 hs.1.le h6,
      w1_dihA_unfold y4 s y6 hs.1.le, w1_dihB_unfold y4 s y6 h6,
      w1_dihC_unfold y4 s y6 h4]
    unfold w1Fex
    ring
  have hFex : HasDerivAt (w1Fex y4 y6) (w1F1 y4 y5 y6) y5 := by
    have hSEA := w1SEA_hasDerivAt y4 y5 y6 hA0 htA
    have hSEB := w1SEB_hasDerivAt y4 y5 y6 hB0 htB
    have hSEC := w1SEC_hasDerivAt y4 y5 y6 hC0 htC
    have hsum1 : HasDerivAt
        (fun s => matan (w1tA y4 s y6) / w1aA y4 s y6
          + matan (w1tB y4 s y6) / w1aB y4 s y6
          + matan (w1tC y4 s y6) / w1aC y4 s y6)
        (w1SEAD y4 y5 y6 + w1SEBD y4 y5 y6 + w1SECD y4 y5 y6) y5 :=
      (hSEA.add hSEB).add hSEC
    have hK1 : HasDerivAt
        (fun s => -(2 * mm1 / Real.pi) *
          (matan (w1tA y4 s y6) / w1aA y4 s y6
            + matan (w1tB y4 s y6) / w1aB y4 s y6
            + matan (w1tC y4 s y6) / w1aC y4 s y6))
        (-(2 * mm1 / Real.pi) * (w1SEAD y4 y5 y6 + w1SEBD y4 y5 y6 + w1SECD y4 y5 y6)) y5 := by
      have hc := hasDerivAt_const y5 (-(2 * mm1 / Real.pi))
      have h := hc.mul hsum1
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · try simp only [w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
        try ring
      · intro s; simp only [Pi.mul_apply]; try ring
    have hD4 := w1DIHC_hasDerivAt y4 y5 y6 hdC0 hgC
    have hterm4 : HasDerivAt
        (fun s => lfun (y4 * 0.5) * h0cut y4 * (w1WC y4 s y6 * matan (w1gC y4 s y6)))
        (lfun (y4 * 0.5) * h0cut y4 * w1DIHCD y4 y5 y6) y5 := by
      have hc := hasDerivAt_const y5 (lfun (y4 * 0.5) * h0cut y4)
      have h := hc.mul hD4
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · try simp only [w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
        try ring
      · intro s; simp only [Pi.mul_apply]; try ring
    have hD5 := w1DIHA_hasDerivAt y4 y5 y6 hdA0 hgA
    have hlf5 := w1_lfun_hasDerivAt y5
    have hterm5 : HasDerivAt
        (fun s => lfun (s * 0.5) * 1 * (w1WA y4 s y6 * matan (w1gA y4 s y6)))
        (-(25 / 13) * w1DIHA y4 y5 y6 + lfun (y5 * 0.5) * w1DIHAD y4 y5 y6) y5 := by
      have h := hlf5.mul hD5
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · try simp only [w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
        try ring
      · intro s; simp only [Pi.mul_apply]; try ring
    have hD6 := w1DIHB_hasDerivAt y4 y5 y6 hdB0 hgB
    have hterm6 : HasDerivAt
        (fun s => lfun (y6 * 0.5) * 1 * (w1WB y4 s y6 * matan (w1gB y4 s y6)))
        (lfun (y6 * 0.5) * w1DIHBD y4 y5 y6) y5 := by
      have hc := hasDerivAt_const y5 (lfun (y6 * 0.5))
      have h := hc.mul hD6
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · try simp only [w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
        try ring
      · intro s; simp only [Pi.mul_apply]; try ring
    have hsum2 : HasDerivAt
        (fun s => lfun (y4 * 0.5) * h0cut y4 * (w1WC y4 s y6 * matan (w1gC y4 s y6))
          + lfun (s * 0.5) * 1 * (w1WA y4 s y6 * matan (w1gA y4 s y6))
          + lfun (y6 * 0.5) * 1 * (w1WB y4 s y6 * matan (w1gB y4 s y6)))
        (lfun (y4 * 0.5) * h0cut y4 * w1DIHCD y4 y5 y6
          + (-(25 / 13) * w1DIHA y4 y5 y6 + lfun (y5 * 0.5) * w1DIHAD y4 y5 y6)
          + lfun (y6 * 0.5) * w1DIHBD y4 y5 y6) y5 := by
      have h := (hterm4.add hterm5).add hterm6
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · try simp only [w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
        try ring
      · intro s; simp only [Pi.add_apply]; try ring
    have hK2 : HasDerivAt
        (fun s => (8 * mm2 / Real.pi) *
          (lfun (y4 * 0.5) * h0cut y4 * (w1WC y4 s y6 * matan (w1gC y4 s y6))
            + lfun (s * 0.5) * 1 * (w1WA y4 s y6 * matan (w1gA y4 s y6))
            + lfun (y6 * 0.5) * 1 * (w1WB y4 s y6 * matan (w1gB y4 s y6))))
        ((8 * mm2 / Real.pi) *
          (lfun (y4 * 0.5) * h0cut y4 * w1DIHCD y4 y5 y6
            + (-(25 / 13) * w1DIHA y4 y5 y6 + lfun (y5 * 0.5) * w1DIHAD y4 y5 y6)
            + lfun (y6 * 0.5) * w1DIHBD y4 y5 y6)) y5 := by
      have hc := hasDerivAt_const y5 (8 * mm2 / Real.pi)
      have h := hc.mul hsum2
      refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      · try simp only [w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
        try ring
      · intro s; simp only [Pi.mul_apply]; try ring
    have hlog := hasDerivAt_const y5 (1 / 12 : ℝ)
    have h12 := (hlog.add hK1).add hK2
    have hc8 := hasDerivAt_const y5 (0.008 : ℝ)
    have h8 := hc8.mul hD4
    have h := h12.sub h8
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · try simp only [w1F1, w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
      simp only [show (0.5 : ℝ) = 1 / 2 by norm_num]
      ring
    · intro s
      unfold w1Fex
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
  exact hFex.congr_of_eventuallyEq hfun

theorem w1aF_hasDerivAt2_y5 (y4 y5 y6 : ℝ)
    (h4 : 0 ≤ y4) (h5 : 0 < y5) (h6 : 0 ≤ y6)
    (hA0 : w1aA y4 y5 y6 ≠ 0) (hB0 : w1aB y4 y5 y6 ≠ 0) (hC0 : w1aC y4 y5 y6 ≠ 0)
    (hdA0 : w1d4A y4 y5 y6 ≠ 0) (hdB0 : w1d4B y4 y5 y6 ≠ 0) (hdC0 : w1d4C y4 y5 y6 ≠ 0)
    (htA : -1 < w1tA y4 y5 y6) (htB : -1 < w1tB y4 y5 y6) (htC : -1 < w1tC y4 y5 y6)
    (hgA : -1 < w1gA y4 y5 y6) (hgB : -1 < w1gB y4 y5 y6) (hgC : -1 < w1gC y4 y5 y6) :
    HasDerivAt (fun s => w1F1 y4 s y6) (w1F2 y4 y5 y6) y5 := by
  have hSEA2 := w1SEAD_hasDerivAt y4 y5 y6 hA0 htA
  have hSEB2 := w1SEBD_hasDerivAt y4 y5 y6 hB0 htB
  have hSEC2 := w1SECD_hasDerivAt y4 y5 y6 hC0 htC
  have hsum1 : HasDerivAt
      (fun s => w1SEAD y4 s y6 + w1SEBD y4 s y6 + w1SECD y4 s y6)
      (w1SEADD y4 y5 y6 + w1SEBDD y4 y5 y6 + w1SECDD y4 y5 y6) y5 :=
    (hSEA2.add hSEB2).add hSEC2
  have hK1 : HasDerivAt
      (fun s => -(2 * mm1 / Real.pi) * (w1SEAD y4 s y6 + w1SEBD y4 s y6 + w1SECD y4 s y6))
      (-(2 * mm1 / Real.pi) *
        (w1SEADD y4 y5 y6 + w1SEBDD y4 y5 y6 + w1SECDD y4 y5 y6)) y5 := by
    have hc := hasDerivAt_const y5 (-(2 * mm1 / Real.pi))
    have h := hc.mul hsum1
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s
      simp only [Pi.mul_apply, w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
      try ring
  have hD4 := w1DIHCD_hasDerivAt y4 y5 y6 hdC0 hgC
  have hterm4 : HasDerivAt (fun s => lfun (y4 * 0.5) * h0cut y4 * w1DIHCD y4 s y6)
      (lfun (y4 * 0.5) * h0cut y4 * w1DIHCDD y4 y5 y6) y5 := by
    have hc := hasDerivAt_const y5 (lfun (y4 * 0.5) * h0cut y4)
    have h := hc.mul hD4
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s
      simp only [Pi.mul_apply, w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
      try ring
  have hD5a := w1DIHA_hasDerivAt y4 y5 y6 hdA0 hgA
  have hD5b := w1DIHAD_hasDerivAt y4 y5 y6 hdA0 hgA
  have hlf5 := w1_lfun_hasDerivAt y5
  have hA1 : HasDerivAt (fun s => -(25 / 13) * w1DIHA y4 s y6)
      (-(25 / 13) * w1DIHAD y4 y5 y6) y5 := by
    have hc := hasDerivAt_const y5 (-(25 / 13) : ℝ)
    have h := hc.mul hD5a
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s
      simp only [Pi.mul_apply, w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
      try ring
  have hA2 : HasDerivAt (fun s => lfun (s * 0.5) * w1DIHAD y4 s y6)
      (-(25 / 13) * w1DIHAD y4 y5 y6 + lfun (y5 * 0.5) * w1DIHADD y4 y5 y6) y5 := by
    have h := hlf5.mul hD5b
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s
      simp only [Pi.mul_apply, w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
      try ring
  have hA : HasDerivAt
      (fun s => -(25 / 13) * w1DIHA y4 s y6 + lfun (s * 0.5) * w1DIHAD y4 s y6)
      (-(25 / 13) * w1DIHAD y4 y5 y6
        + (-(25 / 13) * w1DIHAD y4 y5 y6 + lfun (y5 * 0.5) * w1DIHADD y4 y5 y6)) y5 :=
    hA1.add hA2
  have hD6 := w1DIHBD_hasDerivAt y4 y5 y6 hdB0 hgB
  have hterm6 : HasDerivAt (fun s => lfun (y6 * 0.5) * w1DIHBD y4 s y6)
      (lfun (y6 * 0.5) * w1DIHBDD y4 y5 y6) y5 := by
    have hc := hasDerivAt_const y5 (lfun (y6 * 0.5))
    have h := hc.mul hD6
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s
      simp only [Pi.mul_apply, w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
      try ring
  have hsum2 : HasDerivAt
      (fun s => lfun (y4 * 0.5) * h0cut y4 * w1DIHCD y4 s y6
        + (-(25 / 13) * w1DIHA y4 s y6 + lfun (s * 0.5) * w1DIHAD y4 s y6)
        + lfun (y6 * 0.5) * w1DIHBD y4 s y6)
      (lfun (y4 * 0.5) * h0cut y4 * w1DIHCDD y4 y5 y6
        + (-(25 / 13) * w1DIHAD y4 y5 y6
          + (-(25 / 13) * w1DIHAD y4 y5 y6 + lfun (y5 * 0.5) * w1DIHADD y4 y5 y6))
        + lfun (y6 * 0.5) * w1DIHBDD y4 y5 y6) y5 := by
    have h := (hterm4.add hA).add hterm6
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s
      simp only [Pi.add_apply, w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
      try ring
  have hK2 : HasDerivAt
      (fun s => (8 * mm2 / Real.pi) *
        (lfun (y4 * 0.5) * h0cut y4 * w1DIHCD y4 s y6
          + (-(25 / 13) * w1DIHA y4 s y6 + lfun (s * 0.5) * w1DIHAD y4 s y6)
          + lfun (y6 * 0.5) * w1DIHBD y4 s y6))
      ((8 * mm2 / Real.pi) *
        (lfun (y4 * 0.5) * h0cut y4 * w1DIHCDD y4 y5 y6
          + (-(25 / 13) * w1DIHAD y4 y5 y6
            + (-(25 / 13) * w1DIHAD y4 y5 y6 + lfun (y5 * 0.5) * w1DIHADD y4 y5 y6))
          + lfun (y6 * 0.5) * w1DIHBDD y4 y5 y6)) y5 := by
    have hc := hasDerivAt_const y5 (8 * mm2 / Real.pi)
    have h := hc.mul hsum2
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    · ring
    · intro s
      simp only [Pi.mul_apply, w1DIHA, w1DIHB, w1DIHC, w1DIHAD, w1DIHBD, w1DIHCD]
      try ring
  have h12 := hK1.add hK2
  have hc8 := hasDerivAt_const y5 (0.008 : ℝ)
  have h8 := hc8.mul hD4
  have h := h12.sub h8
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  · try simp only [w1F2, w1DIHAD, w1DIHBD, w1DIHCD]
    simp only [show (0.5 : ℝ) = 1 / 2 by norm_num]
    ring
  · intro s
    unfold w1F1
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    try ring

/-! ## 6. Axiom audit -/

#print axioms w1aF_hasDerivAt_y5
#print axioms w1aF_hasDerivAt2_y5
#print axioms w1_se_hasDerivAt
#print axioms w1_se_hasDerivAt2
#print axioms w1_dih_hasDerivAt
#print axioms w1_dih_hasDerivAt2
#print axioms w1_seA_unfold
#print axioms w1_seB_unfold
#print axioms w1_seC_unfold
#print axioms w1_dihA_unfold
#print axioms w1_dihB_unfold
#print axioms w1_dihC_unfold

end Kepler.Text
