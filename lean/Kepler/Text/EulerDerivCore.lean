/-
Kepler.Text.EulerDerivCore — Euler 泛型立体角工程 W3 波 (lane BB): the real
math core (the derivative identities) behind the Flyspeck EULER_TRIANGLE.

Provenance (HOL originals under `reference/flyspeck/text_formalization/`):
  * `ea3_derivative_wrt_c1`     : euler_multivariate.hl:109
                                  DERIVATIVE_WRT_C1_Euler_lemma — the
                                  one-variable identity
                                  `-π/2 - 2·atn(1 - c/2) + 2·atn((4-c)/c) = 0`
                                  on any real interval containing `2` and
                                  avoiding `0` and `4`.  HOL needs 242 lines of
                                  derivative-tactic bookkeeping; here the whole
                                  flow is `HasDerivAt` + `Real.deriv_arctan` +
                                  the MeanValue constant lemma.
  * `ea3_derivative_wrt_a`      : euler_multivariate.hl:351
                                  DERIVATIVE_WRT_A_Euler_lemma — the two-var
                                  unit-box angle-sum identity.  HOL spends
                                  2,889 lines (63% of the whole Euler closure)
                                  on the same statement; the math is: the
                                  rearranged left-hand side is constant in `a`
                                  on the convex set `{a | 0 < ups_x a b c - a·b·c}`
                                  (derivative 0 across four arctan slots), and
                                  its value at the special point
                                  `a0 = b + c - b·c/2` (where the first arctan
                                  argument vanishes) is `0`.
  * `ea3_euler_triangle_convex` : euler_complement.hl:685
                                  EULER_TRIANGLE_REAL_INTERVAL — HOL
                                  `is_realinterval` renders as `Convex ℝ`.
  * point value                 : HOL derives it from a second
                                  constant-derivative argument routed through
                                  DERIVATIVE_WRT_C1; here we evaluate directly
                                  at `a0`, rewriting `√d0 = r·s/2` with
                                  `r = √(b(4-b))`, `s = √(c(4-c))`, and proving
                                  `2·arctan γ = π/2 + arctan α + arctan β` via
                                  cosine injectivity on `(0, π)`
                                  (`Real.strictAntiOn_cos`) — no case analysis
                                  on arctan branches anywhere.  The two algebra
                                  engines (squared-cosine identity and the sign
                                  lemma `(1-γ²)(α+β) ≤ 0`) were verified
                                  symbolically (sympy, modulo `r² = b(4-b)`,
                                  `s² = c(4-c)`), and numerically at
                                  `(b,c) ∈ {(1,1), (2,3), (1,3)}`.

Method (per acceptance prescription): all derivative work is `HasDerivAt` +
`Real.deriv_arctan` (composed form `HasDerivAt.arctan`); "derivative 0 on a
convex interval ⇒ constant" is the glue
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` with bound `0`.
No incomplete-proof or kernel-shortcut tokens anywhere.  W3 does not import
PackingAuto18/21/25 and touches no existing file.
-/

import Kepler.Text.SphereKit
import Kepler.Text.EulerAtn2Kit
import Kepler.Text.EulerSimplexGeom
import Mathlib

namespace Kepler.Text

set_option maxRecDepth 40000

/-! ## Glue: derivative 0 on a convex interval implies constant -/

/-- HOL `HAS_REAL_DERIVATIVE_ZERO_CONSTANT2` (euler_multivariate.hl:56): a
function with derivative `0` at every point of a convex real interval is
constant on it.  Glue around the one-dimensional mean value theorem
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` with bound `0`. -/
private theorem ea3_const_of_derivWithin_zero {f : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s) (hf : ∀ y ∈ s, HasDerivWithinAt f 0 s y)
    {x z : ℝ} (hx : x ∈ s) (hz : z ∈ s) : f x = f z := by
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun _ => (0:ℝ)) (C := 0) hf (fun _ _ => by simp) hx hz
  have h0 : f z - f x = 0 := by simpa using h
  linarith

/-! ## Generic `HasDerivAt` atoms -/

/-- Derivative of an affine function. -/
private theorem ea3_hasDerivAt_lin (m k x : ℝ) :
    HasDerivAt (fun y : ℝ => m * y + k) m x := by
  have h := ((hasDerivAt_id x).const_mul m).add (hasDerivAt_const (c := k) (x := x))
  rwa [show ((m * 1 + 0 : ℝ) = m) from by ring] at h

/-- Derivative of the unit-box quadratic `y ↦ -y² + m·y + k`. -/
private theorem ea3_hasDerivAt_poly (m k x : ℝ) :
    HasDerivAt (fun y : ℝ => -y * y + m * y + k) (-2 * x + m) x := by
  have h1 : HasDerivAt (fun y : ℝ => y * y) (2 * x) x := by
    refine HasDerivAt.congr_deriv ((hasDerivAt_id x).mul (hasDerivAt_id x)) ?_
    simp only [id_eq, mul_one, one_mul]
    ring
  have h3 : HasDerivAt (fun y : ℝ => m * y) m x := by
    have h := (hasDerivAt_id x).const_mul m
    rwa [show ((m * 1 : ℝ) = m) from by ring] at h
  have hAsm := (h1.neg.add h3).add (hasDerivAt_const (c := k) (x := x))
  have h : HasDerivAt (fun y : ℝ => -y * y + m * y + k) ((-2 * x + m) + 0) x := by
    refine hAsm.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · filter_upwards with y
      simp only [Pi.add_apply, Pi.neg_apply]
      ring
    · linarith
  rwa [add_zero] at h

/-! ## The unit-box quadratic and the four-slot function -/

/-- The quadratic `a ↦ ups_x a b c - a·b·c` of DERIVATIVE_WRT_A, presented in
polynomial shape (`2·a0 = 2b+2c-bc`, `d(a0) - d(a) = (a - a0)²` etc. all read
off this form). -/
private def ea3_D (b c y : ℝ) : ℝ :=
  -y * y + (2 * b + 2 * c - b * c) * y + (2 * b * c - b * b - c * c)

private theorem ea3_D_eq (b c y : ℝ) :
    ea3_D b c y = upsX y b c - y * b * c := by
  simp only [ea3_D, upsX]
  ring

/-- Derivative of `ea3_D b c` at `x`. -/
private theorem ea3_hD (b c x : ℝ) :
    HasDerivAt (fun y : ℝ => ea3_D b c y) (-2 * x + (2 * b + 2 * c - b * c)) x :=
  (ea3_hasDerivAt_poly (2 * b + 2 * c - b * c) (2 * b * c - b * b - c * c) x).congr_of_eventuallyEq
    (by filter_upwards with y; rfl)

/-- Derivative of `y ↦ √(ea3_D b c y)` at `x` (with `ea3_D b c x ≠ 0`). -/
private theorem ea3_hsqrtD (b c x : ℝ) (hd : ea3_D b c x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.sqrt (ea3_D b c y))
      ((-2 * x + (2 * b + 2 * c - b * c)) / (2 * Real.sqrt (ea3_D b c x))) x :=
  (ea3_hD b c x).sqrt hd

/-- The FUNCTION of DERIVATIVE_WRT_A (euler_multivariate.hl:372-383): the
whole identity rearranged to `= 0`, as a function of `a` with `b, c` frozen.
The four arctan slots sit over the shared quadratic `ea3_D b c`. -/
private noncomputable def ea3_F (b c : ℝ) : ℝ → ℝ := fun y =>
  -Real.pi / 2
    - Real.arctan ((-2 * y + 2 * b + 2 * c - b * c)
        / (2 * Real.sqrt (ea3_D b c y)))
    - Real.arctan ((-2 * b + 2 * c + 2 * y - c * y)
        / (2 * Real.sqrt (ea3_D b c y)))
    - Real.arctan ((-2 * c + 2 * y + 2 * b - y * b)
        / (2 * Real.sqrt (ea3_D b c y)))
    + 2 * Real.arctan ((8 - y - b - c) / Real.sqrt (ea3_D b c y))

/-! ## Slot derivatives (values reduced at a point with `0 < ea3_D`) -/

/-- Slot 1: `d/dy arctan((-2y+2b+2c-bc)/(2√d))` reduces to `-1/√d` — the
cancellation HOL isolates in subgoal 3.8.4.3 (`M = -(4d+Da²)/√d`). -/
private theorem ea3_slot1_deriv (b c x : ℝ) (hd : 0 < ea3_D b c x) :
    HasDerivAt (fun y : ℝ => Real.arctan ((-2 * y + 2 * b + 2 * c - b * c)
        / (2 * Real.sqrt (ea3_D b c y))))
      (-1 / Real.sqrt (ea3_D b c x)) x := by
  have hs0 : Real.sqrt (ea3_D b c x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hs20 : (2:ℝ) * Real.sqrt (ea3_D b c x) ≠ 0 := mul_ne_zero two_ne_zero hs0
  have hL1 : HasDerivAt (fun y : ℝ => -2 * y + (2 * b + 2 * c - b * c)) (-2) x :=
    ea3_hasDerivAt_lin (-2) (2 * b + 2 * c - b * c) x
  have hG := (ea3_hsqrtD b c x (ne_of_gt hd)).const_mul 2
  have hq : HasDerivAt
      (fun y : ℝ => (-2 * y + (2 * b + 2 * c - b * c))
        / (2 * Real.sqrt (ea3_D b c y)))
      ((-2 * (2 * Real.sqrt (ea3_D b c x))
          - (-2 * x + (2 * b + 2 * c - b * c))
            * (2 * ((-2 * x + (2 * b + 2 * c - b * c))
              / (2 * Real.sqrt (ea3_D b c x)))))
        / (2 * Real.sqrt (ea3_D b c x)) ^ 2) x :=
    HasDerivAt.div hL1 hG hs20
  refine HasDerivAt.congr_deriv
    (HasDerivAt.congr_of_eventuallyEq hq.arctan
      (by filter_upwards with y; ring)) ?_
  set s : ℝ := Real.sqrt (ea3_D b c x) with hsd_eq
  have hs2 : ea3_D b c x = s ^ 2 := by rw [hsd_eq]; exact (Real.sq_sqrt hd.le).symm
  have hM : (0:ℝ) < 1 + ((-2 * x + 2 * b + 2 * c - b * c) / (2 * s)) ^ 2 := by
    linarith [sq_nonneg ((-2 * x + 2 * b + 2 * c - b * c) / (2 * s))]
  field_simp [hs0, show (1:ℝ) + ((-2 * x + 2 * b + 2 * c - b * c) / (2 * s)) ^ 2 ≠ 0 from
    ne_of_gt hM]
  ring

/-- Slot 2 (`arctan` with numerator `-2b+2c+2y-cy`): reduced value
`(2(2-c)·d - Db·Da)/(√d·(4d+Db²))`; note `4d + Db² = c(4-c)·a·(4-a)` — the
factorization behind the HOL subgoal-3.13 reductions. -/
private theorem ea3_slot2_deriv (b c x : ℝ) (hd : 0 < ea3_D b c x) :
    HasDerivAt (fun y : ℝ => Real.arctan ((-2 * b + 2 * c + 2 * y - c * y)
        / (2 * Real.sqrt (ea3_D b c y))))
      ((2 * (2 - c) * ea3_D b c x
          - (-2 * b + 2 * c + 2 * x - c * x) * (-2 * x + 2 * b + 2 * c - b * c))
        / (Real.sqrt (ea3_D b c x)
          * (4 * ea3_D b c x + (-2 * b + 2 * c + 2 * x - c * x) ^ 2))) x := by
  have hs0 : Real.sqrt (ea3_D b c x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hs20 : (2:ℝ) * Real.sqrt (ea3_D b c x) ≠ 0 := mul_ne_zero two_ne_zero hs0
  have hL2 : HasDerivAt (fun y : ℝ => -2 * b + 2 * c + 2 * y - c * y) (2 - c) x := by
    refine (ea3_hasDerivAt_lin (2 - c) (2 * c - 2 * b) x).congr_of_eventuallyEq ?_
    filter_upwards with y
    ring
  have hG := (ea3_hsqrtD b c x (ne_of_gt hd)).const_mul 2
  have hq : HasDerivAt
      (fun y : ℝ => (-2 * b + 2 * c + 2 * y - c * y)
        / (2 * Real.sqrt (ea3_D b c y)))
      (((2 - c) * (2 * Real.sqrt (ea3_D b c x))
          - (-2 * b + 2 * c + 2 * x - c * x)
            * (2 * ((-2 * x + (2 * b + 2 * c - b * c))
              / (2 * Real.sqrt (ea3_D b c x)))))
        / (2 * Real.sqrt (ea3_D b c x)) ^ 2) x :=
    HasDerivAt.div hL2 hG hs20
  refine HasDerivAt.congr_deriv
    (HasDerivAt.congr_of_eventuallyEq hq.arctan
      (by filter_upwards with y; ring)) ?_
  set s : ℝ := Real.sqrt (ea3_D b c x) with hsd_eq
  have hs2 : ea3_D b c x = s ^ 2 := by rw [hsd_eq]; exact (Real.sq_sqrt hd.le).symm
  rw [hs2]
  have hM : (0:ℝ) < 1 + ((-2 * b + 2 * c + 2 * x - c * x) / (2 * s)) ^ 2 := by
    linarith [sq_nonneg ((-2 * b + 2 * c + 2 * x - c * x) / (2 * s))]
  have hE2 : (0:ℝ) < 4 * s ^ 2 + (-2 * b + 2 * c + 2 * x - c * x) ^ 2 := by
    linarith [sq_nonneg (-2 * b + 2 * c + 2 * x - c * x)]
  field_simp [hs0,
    show (1:ℝ) + ((-2 * b + 2 * c + 2 * x - c * x) / (2 * s)) ^ 2 ≠ 0 from ne_of_gt hM,
    show (4:ℝ) * s ^ 2 + (-2 * b + 2 * c + 2 * x - c * x) ^ 2 ≠ 0 from ne_of_gt hE2]
  ring

/-- Slot 3 (`arctan` with numerator `-2c+2y+2b-yb`): reduced value
`(2(2-b)·d - Dc·Da)/(√d·(4d+Dc²))`. -/
private theorem ea3_slot3_deriv (b c x : ℝ) (hd : 0 < ea3_D b c x) :
    HasDerivAt (fun y : ℝ => Real.arctan ((-2 * c + 2 * y + 2 * b - y * b)
        / (2 * Real.sqrt (ea3_D b c y))))
      ((2 * (2 - b) * ea3_D b c x
          - (-2 * c + 2 * x + 2 * b - x * b) * (-2 * x + 2 * b + 2 * c - b * c))
        / (Real.sqrt (ea3_D b c x)
          * (4 * ea3_D b c x + (-2 * c + 2 * x + 2 * b - x * b) ^ 2))) x := by
  have hs0 : Real.sqrt (ea3_D b c x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hs20 : (2:ℝ) * Real.sqrt (ea3_D b c x) ≠ 0 := mul_ne_zero two_ne_zero hs0
  have hL3 : HasDerivAt (fun y : ℝ => -2 * c + 2 * y + 2 * b - y * b) (2 - b) x := by
    refine (ea3_hasDerivAt_lin (2 - b) (2 * b - 2 * c) x).congr_of_eventuallyEq ?_
    filter_upwards with y
    ring
  have hG := (ea3_hsqrtD b c x (ne_of_gt hd)).const_mul 2
  have hq : HasDerivAt
      (fun y : ℝ => (-2 * c + 2 * y + 2 * b - y * b)
        / (2 * Real.sqrt (ea3_D b c y)))
      (((2 - b) * (2 * Real.sqrt (ea3_D b c x))
          - (-2 * c + 2 * x + 2 * b - x * b)
            * (2 * ((-2 * x + (2 * b + 2 * c - b * c))
              / (2 * Real.sqrt (ea3_D b c x)))))
        / (2 * Real.sqrt (ea3_D b c x)) ^ 2) x :=
    HasDerivAt.div hL3 hG hs20
  refine HasDerivAt.congr_deriv
    (HasDerivAt.congr_of_eventuallyEq hq.arctan
      (by filter_upwards with y; ring)) ?_
  set s : ℝ := Real.sqrt (ea3_D b c x) with hsd_eq
  have hs2 : ea3_D b c x = s ^ 2 := by rw [hsd_eq]; exact (Real.sq_sqrt hd.le).symm
  rw [hs2]
  have hM : (0:ℝ) < 1 + ((-2 * c + 2 * x + 2 * b - x * b) / (2 * s)) ^ 2 := by
    linarith [sq_nonneg ((-2 * c + 2 * x + 2 * b - x * b) / (2 * s))]
  have hE3 : (0:ℝ) < 4 * s ^ 2 + (-2 * c + 2 * x + 2 * b - x * b) ^ 2 := by
    linarith [sq_nonneg (-2 * c + 2 * x + 2 * b - x * b)]
  field_simp [hs0,
    show (1:ℝ) + ((-2 * c + 2 * x + 2 * b - x * b) / (2 * s)) ^ 2 ≠ 0 from ne_of_gt hM,
    show (4:ℝ) * s ^ 2 + (-2 * c + 2 * x + 2 * b - x * b) ^ 2 ≠ 0 from ne_of_gt hE3]
  ring

/-- Slot 4 (`arctan((8-y-b-c)/√d)`): reduced value `(-2d - G·Da)/(2√d·(d+G²))`;
note `d + G² = (4-b)(4-c)(4-a)`. -/
private theorem ea3_slot4_deriv (b c x : ℝ) (hd : 0 < ea3_D b c x) :
    HasDerivAt (fun y : ℝ => Real.arctan ((8 - y - b - c)
        / Real.sqrt (ea3_D b c y)))
      ((-2 * ea3_D b c x
          - (8 - x - b - c) * (-2 * x + 2 * b + 2 * c - b * c))
        / (2 * Real.sqrt (ea3_D b c x)
          * (ea3_D b c x + (8 - x - b - c) ^ 2))) x := by
  have hs0 : Real.sqrt (ea3_D b c x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hL4 : HasDerivAt (fun y : ℝ => 8 - y - b - c) (-1) x := by
    refine (ea3_hasDerivAt_lin (-1) (8 - b - c) x).congr_of_eventuallyEq ?_
    filter_upwards with y
    ring
  have hG := ea3_hsqrtD b c x (ne_of_gt hd)
  have hq : HasDerivAt
      (fun y : ℝ => (8 - y - b - c) / Real.sqrt (ea3_D b c y))
      ((-1 * Real.sqrt (ea3_D b c x)
          - (8 - x - b - c)
            * ((-2 * x + (2 * b + 2 * c - b * c)) / (2 * Real.sqrt (ea3_D b c x))))
        / Real.sqrt (ea3_D b c x) ^ 2) x :=
    HasDerivAt.div hL4 hG hs0
  refine HasDerivAt.congr_deriv
    (HasDerivAt.congr_of_eventuallyEq hq.arctan
      (by filter_upwards with y; ring)) ?_
  set s : ℝ := Real.sqrt (ea3_D b c x) with hsd_eq
  have hs2 : ea3_D b c x = s ^ 2 := by rw [hsd_eq]; exact (Real.sq_sqrt hd.le).symm
  rw [hs2]
  have hM : (0:ℝ) < 1 + ((8 - x - b - c) / s) ^ 2 := by
    linarith [sq_nonneg ((8 - x - b - c) / s)]
  have hE4 : (0:ℝ) < s ^ 2 + (8 - x - b - c) ^ 2 := by
    linarith [sq_nonneg (8 - x - b - c)]
  field_simp [hs0,
    show (1:ℝ) + ((8 - x - b - c) / s) ^ 2 ≠ 0 from ne_of_gt hM,
    show s ^ 2 + (8 - x - b - c) ^ 2 ≠ 0 from ne_of_gt hE4]
  ring

set_option maxHeartbeats 1000000 in
/-- The derivative of `ea3_F b c` vanishes at every point with
`0 < ea3_D b c x`: the four reduced slot values collapse to the quartic
identity (see the `t`-facts and `hEqN` below; numerically exact at
`b=c=1, a=1` and `b=2, c=3, a=1.5`). -/
private theorem ea3_F_deriv (b c x : ℝ) (hd : 0 < ea3_D b c x) :
    HasDerivAt (ea3_F b c) 0 x := by
  have hslot1 := ea3_slot1_deriv b c x hd
  have hslot2 := ea3_slot2_deriv b c x hd
  have hslot3 := ea3_slot3_deriv b c x hd
  have hslot4 := ea3_slot4_deriv b c x hd
  have hAsm : HasDerivAt (ea3_F b c)
      ((((0 - (-1 / Real.sqrt (ea3_D b c x)))
        - (2 * (2 - c) * ea3_D b c x
          - (-2 * b + 2 * c + 2 * x - c * x) * (-2 * x + 2 * b + 2 * c - b * c))
          / (Real.sqrt (ea3_D b c x)
            * (4 * ea3_D b c x + (-2 * b + 2 * c + 2 * x - c * x) ^ 2)))
        - (2 * (2 - b) * ea3_D b c x
          - (-2 * c + 2 * x + 2 * b - x * b) * (-2 * x + 2 * b + 2 * c - b * c))
          / (Real.sqrt (ea3_D b c x)
            * (4 * ea3_D b c x + (-2 * c + 2 * x + 2 * b - x * b) ^ 2)))
        + 2 * ((-2 * ea3_D b c x
          - (8 - x - b - c) * (-2 * x + 2 * b + 2 * c - b * c))
          / (2 * Real.sqrt (ea3_D b c x)
            * (ea3_D b c x + (8 - x - b - c) ^ 2)))) x := by
    exact ((((hasDerivAt_const (c := -Real.pi / 2) (x := x)).sub hslot1).sub hslot2).sub
      hslot3).add (hslot4.const_mul 2)
  refine HasDerivAt.congr_deriv hAsm ?_
  set s : ℝ := Real.sqrt (ea3_D b c x) with hsd_eq
  have hs0 : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hs2 : ea3_D b c x = s ^ 2 := by
    rw [hsd_eq]; exact (Real.sq_sqrt hd.le).symm
  rw [hs2]
  -- abbreviate every linear/quadratic factor; the value goal and the quartic
  -- identity below then live entirely in the atom namespace
  set L1 : ℝ := -2 * x + 2 * b + 2 * c - b * c with hL1def
  set L2 : ℝ := -2 * b + 2 * c + 2 * x - c * x with hL2def
  set L3 : ℝ := -2 * c + 2 * x + 2 * b - x * b with hL3def
  set L4 : ℝ := 8 - x - b - c with hL4def
  set E2 : ℝ := (4:ℝ) * s ^ 2 + L2 ^ 2 with hE2def
  set E3 : ℝ := (4:ℝ) * s ^ 2 + L3 ^ 2 with hE3def
  set G2 : ℝ := s ^ 2 + L4 ^ 2 with hG2def
  set N2 : ℝ := 2 * (2 - c) * s ^ 2 - L2 * L1 with hN2def
  set N3 : ℝ := 2 * (2 - b) * s ^ 2 - L3 * L1 with hN3def
  set N4 : ℝ := -2 * s ^ 2 - L4 * L1 with hN4def
  set X : ℝ := E2 * E3 * G2 with hXdef
  have hs0pos : (0:ℝ) < s := Real.sqrt_pos.mpr hd
  have hs2pos : (0:ℝ) < s ^ 2 := by
    rw [pow_two]; exact mul_pos hs0pos hs0pos
  have hE2n : E2 ≠ 0 := by
    rw [hE2def]
    exact ne_of_gt (by linarith [hs2pos, sq_nonneg L2])
  have hE3n : E3 ≠ 0 := by
    rw [hE3def]
    exact ne_of_gt (by linarith [hs2pos, sq_nonneg L3])
  have hG2n : G2 ≠ 0 := by
    rw [hG2def]
    exact ne_of_gt (by linarith [hs2pos, sq_nonneg L4])
  have hXne : s * X ≠ 0 := by
    rw [hXdef]
    exact mul_ne_zero hs0 (mul_ne_zero (mul_ne_zero hE2n hE3n) hG2n)
  -- the cleared quartic identity (atoms only): X = N2·E3·G2 + N3·E2·G2 - N4·E2·E3
  have hEqN : X = N2 * (E3 * G2) + N3 * (E2 * G2) - N4 * (E2 * E3) := by
    simp only [hXdef, hN2def, hN3def, hN4def, hE2def, hE3def, hG2def]
    rw [show s ^ 2 = -x ^ 2 + (2 * b + 2 * c - b * c) * x - (b - c) ^ 2 from by
      rw [← hs2]; simp only [ea3_D]; ring]
    ring
  have t1 : ((1:ℝ) / s) * (s * X) = X := by
    rw [hXdef]
    field_simp [hs0]
  have t2 : (N2 / (s * E2)) * (s * X) = N2 * (E3 * G2) := by
    rw [hXdef, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hs0 hE2n)]
    ring
  have t3 : (N3 / (s * E3)) * (s * X) = N3 * (E2 * G2) := by
    rw [hXdef, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hs0 hE3n)]
    ring
  have t4 : (N4 / (2 * s * G2)) * (s * X) = N4 * (E2 * E3) / 2 := by
    rw [hXdef, div_mul_eq_mul_div, mul_assoc 2 s G2,
      div_eq_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) (mul_ne_zero hs0 hG2n))]
    ring
  have hW0 : ((((0:ℝ) - -1 / s) - N2 / (s * E2)) - N3 / (s * E3)
      + 2 * (N4 / (2 * s * G2))) * (s * X) = 0 := by
    linear_combination (norm := ring_nf) t1 - t2 - t3 + 2 * t4 + hEqN
  exact (mul_eq_zero.mp hW0).resolve_right hXne

/-! ## The point value at `a0 = b + c - b·c/2` -/
/-! ## The point value at `a0 = b + c - b·c/2` -/

/-- The branch-safe point-value identity: for `b, c ∈ (0,4)` and
`r² = b(4-b)`, `s² = c(4-c)`, `r, s ≥ 0`,
`π/2 + arctan α + arctan β = 2·arctan γ` where `α = (2-b)s/(2r)`,
`β = (2-c)r/(2s)`, `γ = (4-b)(4-c)/(rs)`.  Both sides lie in `(0, π)` (the
sum of the two arctans has positive cosine since `α·β < 1`), and their
cosines agree: the squared-cosine identity plus the sign lemma
`(1-γ²)·(α+β) ≤ 0` force `cos θ1 = cos θ2` (the tangent-equal branch
`θ1 = θ2 + π` is excluded because `(1-γ²)` and `(α+β)` have opposite signs);
`Real.strictAntiOn_cos` then closes. -/
private theorem ea3_point_value (b c r s : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hb4 : b < 4) (hc4 : c < 4) (hr : 0 ≤ r) (hsc : 0 ≤ s)
    (hr2 : r ^ 2 = b * (4 - b)) (hs2 : s ^ 2 = c * (4 - c)) :
    Real.pi / 2 + Real.arctan ((2 - b) * s / (2 * r))
        + Real.arctan ((2 - c) * r / (2 * s))
      = 2 * Real.arctan ((4 - b) * (4 - c) / (r * s)) := by
  have hr0 : 0 < r := by
    refine lt_of_le_of_ne hr (fun h0 => ?_)
    subst h0
    rw [zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hr2
    rcases mul_eq_zero.mp hr2.symm with h | h
    · linarith
    · linarith
  have hsc0 : 0 < s := by
    refine lt_of_le_of_ne hsc (fun h0 => ?_)
    subst h0
    rw [zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hs2
    rcases mul_eq_zero.mp hs2.symm with h | h
    · linarith
    · linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hsne : s ≠ 0 := ne_of_gt hsc0
  set α : ℝ := (2 - b) * s / (2 * r) with hα_def
  set β : ℝ := (2 - c) * r / (2 * s) with hβ_def
  set γ : ℝ := (4 - b) * (4 - c) / (r * s) with hγ_def
  have hγpos : (0:ℝ) < γ := by
    rw [hγ_def]
    exact div_pos (mul_pos (by linarith : (0:ℝ) < 4 - b)
      (by linarith : (0:ℝ) < 4 - c)) (mul_pos hr0 hsc0)
  -- ordering facts
  have hbc : (0:ℝ) ≤ 2 * b + 2 * c - b * c := by
    have h1 : (0:ℝ) ≤ b * (4 - c) := mul_nonneg hb.le (by linarith)
    have h2 : (0:ℝ) ≤ c * (4 - b) := mul_nonneg hc.le (by linarith)
    linarith
  have hbprod : (0:ℝ) < b * (4 - b) := mul_pos hb (by linarith)
  have hcprod : (0:ℝ) < c * (4 - c) := mul_pos hc (by linarith)
  have hsq1b : (2 - b) ^ 2 < 4 := by
    rw [show (2 - b) ^ 2 = 4 - b * (4 - b) from by ring]
    linarith
  have hsq1c : (2 - c) ^ 2 < 4 := by
    rw [show (2 - c) ^ 2 = 4 - c * (4 - c) from by ring]
    linarith
  have hablt : (2 - b) * (2 - c) < 4 := by
    have hex : (2 - b) ^ 2 - 2 * ((2 - b) * (2 - c)) + (2 - c) ^ 2
        = ((2 - b) - (2 - c)) ^ 2 := by ring
    have h2uv : 2 * ((2 - b) * (2 - c)) ≤ (2 - b) ^ 2 + (2 - c) ^ 2 := by
      linarith [hex, sq_nonneg ((2 - b) - (2 - c))]
    linarith
  have hαβ : α * β = (2 - b) * (2 - c) / 4 := by
    rw [hα_def, hβ_def]
    field_simp [hrne, hsne]
    ring
  have hαβ1 : α * β < 1 := by
    have h4 : (0:ℝ) < 4 := by norm_num
    have hx : (2 - b) * (2 - c) / 4 * 4 = (2 - b) * (2 - c) := by
      field_simp
    have h9 : α * β * 4 < 1 * 4 := by
      linarith [hαβ, hablt, hx]
    exact lt_of_mul_lt_mul_right h9 (le_of_lt h4)
  -- the sum of the two arctans stays inside (-π/2, π/2): its cosine is positive
  have hsumcos : 0 < Real.cos (Real.arctan α + Real.arctan β) := by
    rw [Real.cos_add, Real.cos_arctan, Real.sin_arctan, Real.cos_arctan,
      Real.sin_arctan]
    have hs1 : (0:ℝ) < Real.sqrt (1 + α ^ 2) :=
      Real.sqrt_pos.mpr (by linarith [sq_nonneg α])
    have hsc1 : (0:ℝ) < Real.sqrt (1 + β ^ 2) :=
      Real.sqrt_pos.mpr (by linarith [sq_nonneg β])
    field_simp
    linarith
  have hsumlt : Real.arctan α + Real.arctan β < Real.pi := by
    linarith [Real.arctan_lt_pi_div_two α, Real.arctan_lt_pi_div_two β]
  have hsumgt : -(Real.pi) < Real.arctan α + Real.arctan β := by
    linarith [Real.neg_pi_div_two_lt_arctan α, Real.neg_pi_div_two_lt_arctan β]
  have hmemPi2 : (Real.pi / 2 : ℝ) ∈ Set.Icc 0 Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsumub : Real.arctan α + Real.arctan β < Real.pi / 2 := by
    rcases lt_or_ge (Real.arctan α + Real.arctan β) (Real.pi / 2) with h | h
    · exact h
    · exfalso
      have hm1 : (Real.arctan α + Real.arctan β) ∈ Set.Icc 0 Real.pi :=
        ⟨by linarith, by linarith⟩
      rcases eq_or_lt_of_le h with he | hl
      · rw [← he, Real.cos_pi_div_two] at hsumcos
        linarith
      · have hanti := Real.strictAntiOn_cos hmemPi2 hm1 hl
        rw [Real.cos_pi_div_two] at hanti
        linarith
  have hsumlb : -(Real.pi / 2) < Real.arctan α + Real.arctan β := by
    rcases lt_or_ge (-(Real.pi / 2)) (Real.arctan α + Real.arctan β) with h | h
    · exact h
    · exfalso
      have hw0 : (0:ℝ) ≤ -(Real.arctan α + Real.arctan β) := by linarith
      have hw1 : -(Real.arctan α + Real.arctan β) ≤ Real.pi := by linarith
      have hw : (-(Real.arctan α + Real.arctan β)) ∈ Set.Icc 0 Real.pi := ⟨hw0, hw1⟩
      rcases eq_or_lt_of_le h with he | hl
      · rw [he, Real.cos_neg, Real.cos_pi_div_two] at hsumcos
        linarith
      · have hpi2 : (Real.pi / 2 : ℝ) < -(Real.arctan α + Real.arctan β) := by linarith
        have hanti := Real.strictAntiOn_cos hmemPi2 hw hpi2
        rw [Real.cos_neg, Real.cos_pi_div_two] at hanti
        linarith
  have hθ2mem : Real.pi / 2 + Real.arctan α + Real.arctan β ∈ Set.Icc 0 Real.pi :=
    ⟨by linarith, by linarith [hsumub, Real.pi_pos]⟩
  -- cosines
  have hDpos : (0:ℝ) < Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2)) :=
    Real.sqrt_pos.mpr (mul_pos (by linarith [sq_nonneg α]) (by linarith [sq_nonneg β]))
  have hBpos : (0:ℝ) < 1 + γ ^ 2 := by linarith [sq_nonneg γ]
  have hcos2 : Real.cos (Real.pi / 2 + Real.arctan α + Real.arctan β)
      = -((α + β) / Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))) := by
    have hsqmul : Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))
        = Real.sqrt (1 + α ^ 2) * Real.sqrt (1 + β ^ 2) :=
      Real.sqrt_mul (by linarith [sq_nonneg α]) (1 + β ^ 2)
    rw [Real.cos_add, Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Real.sin_arctan, Real.cos_arctan, Real.sin_arctan,
      Real.cos_arctan, hsqmul]
    field_simp
    ring
  -- squared-cosine identity, then the sign lemma pins the branch
  have hsqne : Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2)) ≠ 0 := ne_of_gt hDpos
  have hrr : r * r = b * (4 - b) := by rw [← pow_two]; exact hr2
  have hss : s * s = c * (4 - c) := by rw [← pow_two]; exact hs2
  have hsq1 : ((1 - γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))) ^ 2
      = ((α + β) * (1 + γ ^ 2)) ^ 2 := by
    rw [hα_def, hβ_def, hγ_def, mul_pow, mul_pow,
      Real.sq_sqrt (mul_nonneg (by linarith [sq_nonneg ((2 - b) * s / (2 * r))])
        (by linarith [sq_nonneg ((2 - c) * r / (2 * s))]))]
    field_simp [hrne, hsne]
    simp only [hr2, hs2, hrr, hss]
    ring
  have hsign : (1 - γ ^ 2) * (α + β)
      = -(2 * (4 - b) * (4 - c) * ((4 - b - c) ^ 2) * (2 * b + 2 * c - b * c))
        / (r ^ 3 * s ^ 3) := by
    rw [hα_def, hβ_def, hγ_def]
    field_simp [hrne, hsne]
    simp only [hr2, hs2, hrr, hss]
    ring
  have hsignle : (1 - γ ^ 2) * (α + β) ≤ 0 := by
    rw [hsign]
    have h4b : (0:ℝ) ≤ 4 - b := by linarith
    have h4c : (0:ℝ) ≤ 4 - c := by linarith
    have hnum : (0:ℝ) ≤ 2 * (4 - b) * (4 - c) * ((4 - b - c) ^ 2)
        * (2 * b + 2 * c - b * c) := by
      refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h4b) h4c)
        (sq_nonneg (4 - b - c))) hbc
    have hr3 : (0:ℝ) < r ^ 3 := by
      have h1 : (0:ℝ) < r ^ 2 := by rw [hr2]; exact hbprod
      calc r ^ 3 = r ^ 2 * r := by ring
        _ > 0 := mul_pos h1 hr0
    have hs3 : (0:ℝ) < s ^ 3 := by
      have h1 : (0:ℝ) < s ^ 2 := by rw [hs2]; exact hcprod
      calc s ^ 3 = s ^ 2 * s := by ring
        _ > 0 := mul_pos h1 hsc0
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (mul_nonneg hr3.le hs3.le)
  have hAD : (1 - γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))
      = -((α + β) * (1 + γ ^ 2)) := by
    rcases eq_or_ne (1 - γ ^ 2) 0 with hA0 | hAne
    · -- if γ = 1 then α + β = 0 and both sides vanish
      have hC0 : α + β = 0 := by
        have h1 := hsq1
        rw [hA0] at h1
        have h2 : ((α + β) * (1 + γ ^ 2)) ^ 2 = 0 := by rw [← h1]; ring
        have h3 : (α + β) * (1 + γ ^ 2) = 0 := sq_eq_zero_iff.mp h2
        exact (mul_eq_zero.mp h3).resolve_right hBpos.ne'
      rw [hA0, hC0]
      ring
    · have hC0 : α + β ≠ 0 := by
        intro hC
        apply hAne
        have h1 := hsq1
        rw [hC, zero_mul, zero_pow (two_ne_zero)] at h1
        exact mul_eq_zero.mp (sq_eq_zero_iff.mp h1) |>.resolve_right hsqne
      have hACneg : (1 - γ ^ 2) * (α + β) < 0 :=
        lt_of_le_of_ne hsignle
          fun h => hC0 (mul_eq_zero.mp h |>.resolve_left hAne)
      have hsum : (1 - γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))
          + (α + β) * (1 + γ ^ 2) = 0 := by
        have hprod : ((1 - γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))
              + (α + β) * (1 + γ ^ 2))
            * ((1 - γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))
              - (α + β) * (1 + γ ^ 2)) = 0 := by
          linear_combination hsq1
        rcases mul_eq_zero.mp hprod with h | h
        · exact h
        · exfalso
          have hADCB : (1 - γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))
              = (α + β) * (1 + γ ^ 2) := by linarith
          have hstep : ((1 - γ ^ 2) * (α + β))
              * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))
              = (α + β) * (α + β) * (1 + γ ^ 2) := by
            linear_combination (α + β) * hADCB
          have hlhs : ((1:ℝ) - γ ^ 2) * (α + β)
              * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2)) < 0 :=
            mul_neg_of_neg_of_pos hACneg hDpos
          have hB2 : (0:ℝ) < (α + β) * (α + β) * (1 + γ ^ 2) :=
            mul_pos (mul_self_pos.mpr hC0) hBpos
          linarith
      linarith
  have hcos_eq : Real.cos (2 * Real.arctan γ)
      = Real.cos (Real.pi / 2 + Real.arctan α + Real.arctan β) := by
    have hsqmul : Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))
        = Real.sqrt (1 + α ^ 2) * Real.sqrt (1 + β ^ 2) :=
      Real.sqrt_mul (by linarith [sq_nonneg α]) (1 + β ^ 2)
    -- cleared (multiplicative) forms of the two cosines
    have h1m : Real.cos (2 * Real.arctan γ) * (1 + γ ^ 2) = 1 - γ ^ 2 := by
      rw [Real.cos_two_mul, Real.cos_arctan]
      field_simp
      rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 + γ ^ 2)]
      ring
    have hsqmul' : Real.sqrt (1 + α ^ 2 + α ^ 2 * β ^ 2 + β ^ 2)
        = Real.sqrt (1 + α ^ 2) * Real.sqrt (1 + β ^ 2) := by
      rw [show (1:ℝ) + α ^ 2 + α ^ 2 * β ^ 2 + β ^ 2 = (1 + α ^ 2) * (1 + β ^ 2) from by ring]
      exact Real.sqrt_mul (by linarith [sq_nonneg α]) (1 + β ^ 2)
    have h2m : Real.cos (Real.pi / 2 + Real.arctan α + Real.arctan β)
        * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2)) = -(α + β) := by
      have h2c : Real.cos (Real.pi / 2 + Real.arctan α + Real.arctan β)
          = -((α + β) / Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))) := by
        rw [Real.cos_add, Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
          Real.sin_pi_div_two, Real.sin_arctan, Real.cos_arctan, Real.sin_arctan,
          Real.cos_arctan, hsqmul]
        field_simp [hsqmul']
        ring
      have hdm : ((α + β) / Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2)))
          * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2)) = (α + β) := by
        field_simp [hsqne]
      rw [h2c, neg_mul, hdm]
    have hBDne : ((1:ℝ) + γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2)) ≠ 0 :=
      mul_ne_zero hBpos.ne' hsqne
    have heq : Real.cos (2 * Real.arctan γ)
        * ((1 + γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2)))
        = Real.cos (Real.pi / 2 + Real.arctan α + Real.arctan β)
          * ((1 + γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))) := by
      rw [show (Real.cos (2 * Real.arctan γ)
          * ((1 + γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))))
        = (Real.cos (2 * Real.arctan γ) * (1 + γ ^ 2))
          * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2)) from by ring, h1m,
        show (Real.cos (Real.pi / 2 + Real.arctan α + Real.arctan β)
          * ((1 + γ ^ 2) * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))))
        = (Real.cos (Real.pi / 2 + Real.arctan α + Real.arctan β)
          * Real.sqrt ((1 + α ^ 2) * (1 + β ^ 2))) * (1 + γ ^ 2) from by ring, h2m,
        hAD]
      ring
    exact mul_right_cancel₀ hBDne heq
  have hθ1mem : 2 * Real.arctan γ ∈ Set.Icc 0 Real.pi :=
    ⟨by linarith [Real.arctan_pos.mpr hγpos],
      by linarith [Real.arctan_lt_pi_div_two γ]⟩
  exact (Real.strictAntiOn_cos.injOn hθ1mem hθ2mem hcos_eq).symm

/-! ## The one-variable identity (HOL DERIVATIVE_WRT_C1) -/

/-- Derivative of the C1 combination is identically `0` (chain rule through
`Real.deriv_arctan`; `x ≠ 0` keeps the second argument defined). -/
private theorem ea3_c1_deriv (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -Real.pi / 2 - 2 * Real.arctan (1 - y / 2)
        + 2 * Real.arctan ((4 - y) / y)) 0 x := by
  have hhalf : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have hg1 : HasDerivAt (fun y : ℝ => 1 - y / 2) ((0:ℝ) - 1 / 2) x :=
    (hasDerivAt_const (c := 1) (x := x)).sub hhalf
  have hA1 := hg1.arctan
  have hsub4 : HasDerivAt (fun y : ℝ => 4 - y) ((0:ℝ) - 1) x :=
    (hasDerivAt_const (c := 4) (x := x)).sub (hasDerivAt_id x)
  have hg2 : HasDerivAt (fun y : ℝ => (4 - y) / y)
      ((((0:ℝ) - 1) * x - (4 - x) * 1) / x ^ 2) x :=
    HasDerivAt.div hsub4 (hasDerivAt_id x) hx
  have hA2 := hg2.arctan
  refine HasDerivAt.congr_deriv
    (((hasDerivAt_const (c := -Real.pi / 2) (x := x)).sub (hA1.const_mul 2)).add
      (hA2.const_mul 2)) ?_
  have hM1 : (0:ℝ) < 1 + (1 - x / 2) ^ 2 := by linarith [sq_nonneg (1 - x / 2)]
  have hM2 : (0:ℝ) < 1 + ((4 - x) / x) ^ 2 := by linarith [sq_nonneg ((4 - x) / x)]
  field_simp [hx, show (1:ℝ) + (1 - x / 2) ^ 2 ≠ 0 from ne_of_gt hM1,
    show (1:ℝ) + ((4 - x) / x) ^ 2 ≠ 0 from ne_of_gt hM2]
  ring

/-- HOL `DERIVATIVE_WRT_C1_Euler_lemma` (euler_multivariate.hl:109).  For any
real interval `P` containing `2` on which `x ≠ 0` and `4 - x ≠ 0`, the
one-variable arctan identity
`-π/2 - 2·arctan(1 - c/2) + 2·arctan((4 - c)/c) = 0` holds. -/
theorem ea3_derivative_wrt_c1 (P : Set ℝ) (hP : Convex ℝ P) (h2 : (2:ℝ) ∈ P)
    (hne : ∀ x ∈ P, x ≠ 0 ∧ 4 - x ≠ 0) (c : ℝ) (hc : c ∈ P) :
    -Real.pi / 2 - 2 * Real.arctan (1 - c / 2)
        + 2 * Real.arctan ((4 - c) / c) = 0 := by
  have hstep : -Real.pi / 2 - 2 * Real.arctan (1 - c / 2)
      + 2 * Real.arctan ((4 - c) / c)
      = -Real.pi / 2 - 2 * Real.arctan (1 - 2 / 2)
        + 2 * Real.arctan ((4 - 2) / 2) :=
    ea3_const_of_derivWithin_zero hP
      (fun y hy => (ea3_c1_deriv y (hne y hy).1).hasDerivWithinAt) hc h2
  have h2v : -Real.pi / 2 - 2 * Real.arctan (1 - 2 / 2)
      + 2 * Real.arctan ((4 - 2) / 2) = 0 := by
    norm_num [Real.arctan_zero, Real.arctan_one]
    ring
  rw [hstep]
  exact h2v

/-! ## The interval (HOL EULER_TRIANGLE_REAL_INTERVAL) -/

/-- HOL `EULER_TRIANGLE_REAL_INTERVAL` (euler_complement.hl:685): the set of
points `x` with `0 < ups_x x b c - x·b·c` is a real interval, rendered here as
`Convex ℝ`.  (The HOL statement's `a`-premise is not needed for convexity:
concavity of the quadratic gives
`D(px+qy) = p·D x + q·D y + pq(x-y)²`.) -/
theorem ea3_euler_triangle_convex (b c : ℝ) :
    Convex ℝ {x : ℝ | 0 < upsX x b c - x * b * c} := by
  refine convex_iff_add_mem.mpr fun x hx y hy u v hu hv huv => ?_
  by_cases hu0 : u = 0
  · have hv1 : v = 1 := by linarith
    rw [hu0, hv1]
    simpa using hy
  · have hup : (0:ℝ) < u := lt_of_le_of_ne hu (fun hh => hu0 hh.symm)
    have hv1 : v = 1 - u := by linarith
    rw [hv1]
    simp only [smul_eq_mul]
    show 0 < upsX (u * x + (1 - u) * y) b c - (u * x + (1 - u) * y) * b * c
    have hkey : upsX (u * x + (1 - u) * y) b c - (u * x + (1 - u) * y) * b * c
        = u * (upsX x b c - x * b * c) + (1 - u) * (upsX y b c - y * b * c)
          + u * (1 - u) * (x - y) ^ 2 := by
      simp only [upsX]
      ring
    rw [hkey]
    have h1 : (0:ℝ) < u * (upsX x b c - x * b * c) := mul_pos hup hx
    have h2 : (0:ℝ) ≤ (1 - u) * (upsX y b c - y * b * c) :=
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - u) (le_of_lt hy)
    have h3 : (0:ℝ) ≤ u * (1 - u) * (x - y) ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt hup) (by linarith : (0:ℝ) ≤ 1 - u))
        (sq_nonneg _)
    linarith

/-! ## The two-variable identity (HOL DERIVATIVE_WRT_A) -/

/-- The value of `ea3_F b c` at the special point `a0 = b + c - b·c/2` is `0`:
there the first arctan argument vanishes (`-2·a0 + 2b + 2c - bc = 0`), and
with `r = √(b(4-b))`, `s = √(c(4-c))`, `√(ea3_D b c a0) = r·s/2`, the
remaining three slots have arguments `α = (2-b)s/(2r)`, `β = (2-c)r/(2s)`,
`γ = (4-b)(4-c)/(rs)`, so `ea3_point_value` applies. -/
private theorem ea3_point_zero (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (hb4 : b < 4)
    (hc4 : c < 4) : ea3_F b c (b + c - b * c / 2) = 0 := by
  have hr : (0:ℝ) ≤ Real.sqrt (b * (4 - b)) := Real.sqrt_nonneg _
  have hsc : (0:ℝ) ≤ Real.sqrt (c * (4 - c)) := Real.sqrt_nonneg _
  have hr0 : 0 < Real.sqrt (b * (4 - b)) :=
    Real.sqrt_pos.mpr (mul_pos hb (by linarith))
  have hsc0 : 0 < Real.sqrt (c * (4 - c)) :=
    Real.sqrt_pos.mpr (mul_pos hc (by linarith))
  have hrne : Real.sqrt (b * (4 - b)) ≠ 0 := ne_of_gt hr0
  have hsne : Real.sqrt (c * (4 - c)) ≠ 0 := ne_of_gt hsc0
  have hr2 : Real.sqrt (b * (4 - b)) ^ 2 = b * (4 - b) :=
    Real.sq_sqrt (mul_nonneg hb.le (by linarith))
  have hs2 : Real.sqrt (c * (4 - c)) ^ 2 = c * (4 - c) :=
    Real.sq_sqrt (mul_nonneg hc.le (by linarith))
  set R : ℝ := Real.sqrt (b * (4 - b)) with hR_eq
  set S : ℝ := Real.sqrt (c * (4 - c)) with hS_eq
  have hSS' : S * S = c * (4 - c) := by rw [← pow_two]; exact hs2
  have hRR' : R * R = b * (4 - b) := by rw [← pow_two]; exact hr2
  have hsqrtD : Real.sqrt (ea3_D b c (b + c - b * c / 2)) = R * S / 2 := by
    have hd0sq : ea3_D b c (b + c - b * c / 2) = (R * S / 2) ^ 2 := by
      rw [show (R * S / 2) ^ 2 = R ^ 2 * S ^ 2 / 4 from by ring, hr2, hs2]
      simp only [ea3_D]
      ring
    rw [hd0sq, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (div_nonneg (mul_nonneg hr hsc) (by norm_num))]
  have hL1a0 : -2 * (b + c - b * c / 2) + 2 * b + 2 * c - b * c = 0 := by ring
  have hL2a0 : -2 * b + 2 * c + 2 * (b + c - b * c / 2)
      - c * (b + c - b * c / 2) = c * (2 - b) * (4 - c) / 2 := by ring
  have hL3a0 : -2 * c + 2 * (b + c - b * c / 2) + 2 * b
      - (b + c - b * c / 2) * b = b * (2 - c) * (4 - b) / 2 := by ring
  have hL4a0 : 8 - (b + c - b * c / 2) - b - c = (4 - b) * (4 - c) / 2 := by ring
  have hden : (2:ℝ) * (R * S / 2) = R * S := by ring
  have hα : (c * (2 - b) * (4 - c) / 2) / (R * S)
      = (2 - b) * S / (2 * R) := by
    field_simp [hrne, hsne, hSS', hRR']
    rw [hs2]
    ring
  have hβ : (b * (2 - c) * (4 - b) / 2) / (R * S)
      = (2 - c) * R / (2 * S) := by
    field_simp [hrne, hsne, hSS', hRR']
    rw [hr2]
    ring
  have hγ : ((4 - b) * (4 - c) / 2) / (R * S / 2)
      = (4 - b) * (4 - c) / (R * S) := by
    field_simp [hrne, hsne]
  have hident := ea3_point_value b c R S hb hc hb4 hc4 hr hsc hr2 hs2
  simp only [ea3_F]
  rw [hsqrtD, hden, hL2a0, hL3a0, hL4a0, hL1a0]
  simp only [zero_div, Real.arctan_zero, hα, hβ, hγ]
  linarith

/-- DERIVATIVE_WRT_A core (euler_multivariate.hl:372-383): `ea3_F b c` is
identically `0` on the convex set `{y | 0 < ups_x y b c - y·b·c}` — it has
vanishing derivative there (`ea3_F_deriv`) and vanishes at the special point
`a0 = b + c - b·c/2`, which lies in the set because
`ea3_D b c a0 = ea3_D b c a + (a - a0)²`. -/
private theorem ea3_core (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) (hb4 : b < 4)
    (hc4 : c < 4) (hda : 0 < upsX a b c - a * b * c) : ea3_F b c a = 0 := by
  have hconv : Convex ℝ {y : ℝ | 0 < upsX y b c - y * b * c} :=
    ea3_euler_triangle_convex b c
  have hFS : ∀ y ∈ {y : ℝ | 0 < upsX y b c - y * b * c},
      HasDerivWithinAt (ea3_F b c) 0 {y : ℝ | 0 < upsX y b c - y * b * c} y := by
    intro y hy
    exact (ea3_F_deriv b c y (by rw [ea3_D_eq]; exact hy)).hasDerivWithinAt
  have hdd : ea3_D b c (b + c - b * c / 2)
      = ea3_D b c a + (a - (b + c - b * c / 2)) ^ 2 := by
    simp only [ea3_D]
    ring
  have hdaD : 0 < ea3_D b c a := by
    rw [ea3_D_eq]; exact hda
  have ha0mem : 0 < upsX (b + c - b * c / 2) b c
      - (b + c - b * c / 2) * b * c := by
    rw [← ea3_D_eq, hdd]
    linarith [sq_nonneg (a - (b + c - b * c / 2)), hdaD]
  have hEq : ea3_F b c a = ea3_F b c (b + c - b * c / 2) :=
    ea3_const_of_derivWithin_zero hconv hFS hda ha0mem
  rw [hEq, ea3_point_zero b c hb hc hb4 hc4]

/-- HOL `DERIVATIVE_WRT_A_Euler_lemma` (euler_multivariate.hl:351), stated
premise-for-premise.  With `d = ups_x a b c - a·b·c > 0`, `0 < a, b, c < 4`:

`π/2 - atn((-2a+2b+2c-bc)/(2√d)) + π/2 - atn((-2b+2c+2a-ca)/(2√d))
+ π/2 - atn((-2c+2a+2b-ab)/(2√d)) - π = π - 2·atn((8-a-b-c)/√d)`.

(The premises `0 < a` and `a < 4` are HOL-faithful but not consumed by the
proof — the identity only needs `b, c ∈ (0, 4)` and `0 < d`.) -/
theorem ea3_derivative_wrt_a (a b c : ℝ)
    (hd : 0 < upsX a b c - a * b * c)
    (hpos : 0 < a ∧ 0 < b ∧ 0 < c) (hlt : a < 4 ∧ b < 4 ∧ c < 4) :
    Real.pi / 2
        - Real.arctan ((-2 * a + 2 * b + 2 * c - b * c)
          / (2 * Real.sqrt (upsX a b c - a * b * c)))
      + Real.pi / 2
        - Real.arctan ((-2 * b + 2 * c + 2 * a - c * a)
          / (2 * Real.sqrt (upsX a b c - a * b * c)))
      + Real.pi / 2
        - Real.arctan ((-2 * c + 2 * a + 2 * b - a * b)
          / (2 * Real.sqrt (upsX a b c - a * b * c)))
      - Real.pi
      = Real.pi - 2 * Real.arctan ((8 - a - b - c)
        / Real.sqrt (upsX a b c - a * b * c)) := by
  have h := ea3_core a b c hpos.2.1 hpos.2.2 hlt.2.1 hlt.2.2 hd
  simp only [ea3_F] at h
  rw [ea3_D_eq] at h
  linarith

end Kepler.Text
