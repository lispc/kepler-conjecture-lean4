/-
Kepler.NliBanksZTGIJCF4Dih - lane `ztgmain-w2`, part 2: the `dihY` lower
bounds for the four decoupled ZTGIJCF4 debts (`1_1_0_0` / `0_1_1_0` /
`0_1_0_1` at `s = 8/5`, `0_0_1_1` at `s = 6/5`), consuming
`Kepler.Text.ZTGDihKit` (part 1, frozen).

For each debt box this module certifies the polynomial inequality

  0 <= 4*y1^2*deltaX - s^2*delta4^2        on the whole squared box,

which by `ztg_dihY_ge_arctan` yields `arctan s <= dihY`, i.e.
`1.008 <= dihY` (trio) and `0.875 <= dihY` (`0011`).

Box provenance (all corners derivable from the bank hypotheses):
  y1   in [2*hminus, 2*hplus]        -> x1 = y1^2 in [3793/625, 43917129/6250000]
      via hminus >= 1.23175 (Kepler.NliBanks7.hminus_ge_123175) and
      sq_le_hplus;
  regular slots (i = 0): y in [2, 2*hminus] -> y^2 in [4, 3969/625]
      via sq_ge_4 and hminus < 1.26 (Kepler.Text.mi_hminus_lt_h0, h0 = 1.26);
  critical slots (i = 1): y in [2*hminus, sqrt 8] -> y^2 in [3793/625, 8]
      via the same hminus lower bound and sq_le_8.

Box reduction (`ztgG_box5`, private): g = 4*x1*deltaX - q*delta4^2 is a
quadratic in each of x2..x6 with nonpositive leading coefficient
(-alpha_j: j=2,3 affine parts; j=4,5,6 the terms -x1x4^2, -x2x5^2, -x3x6^2),
verified symbolically once per coordinate by `ztdih_quad2..6` (exact
`ring`).  The one-coordinate step `ztdih_step2..6` is pure linear
arithmetic, so the 31-step Jensen chain inside `ztgG_box5` is fully
explicit (no Bool-ite, no conjunction projections, no defeq unfolding).

Per-line certificates (`ztgline_*`, 32 per debt): exact Taylor expansion
of the quartic at one interval end plus a Bernstein (order-3) certificate
on the residual cubic over the x1-increment interval; all coefficients
and feasibility checks computed with exact rational arithmetic by the
lane's `b/gen2.py` (lo end: 94 lines, hi end: 6 lines, of 128).

Consumed by the Assembly wiring for `nliRestZTGIJCF4_*` (with the
gamma4 >= G side still open).

No `sorry`/`axiom`/`native_decide`; every declaration axiom-audited.
-/
import Kepler.Text.ZTGDihKit
import Kepler.NliBanks5

set_option maxHeartbeats 8000000

namespace Kepler.NliBanksZTGIJCF4Dih
open Kepler.Text

/-! ## 1. Concavity machinery: per-coordinate interpolation identities -/
/-- Interpolation identity for `g` in coordinate 2 (quadratic with
leading coefficient `-(4 * x1 * u5 + q * (x1 - u3 + u5) ^ 2)`): the value between `a` and `b`
dominates the linear interpolation plus the (nonnegative) curvature term.
Exact by `ring` after unfolding `deltaX`/`deltaX4`. -/
private theorem ztdih_quad2 (x1 q u3 u4 u5 u6 t a b : ℝ) :
    (b - a) * (4 * x1 * deltaX x1 t u3 u4 u5 u6 - q * (deltaX4 x1 t u3 u4 u5 u6) ^ 2)
      = (b - t) * (4 * x1 * deltaX x1 a u3 u4 u5 u6 - q * (deltaX4 x1 a u3 u4 u5 u6) ^ 2) + (t - a) * (4 * x1 * deltaX x1 b u3 u4 u5 u6 - q * (deltaX4 x1 b u3 u4 u5 u6) ^ 2)
        + (4 * x1 * u5 + q * (x1 - u3 + u5) ^ 2) * (t - a) * (b - t) * (b - a) := by
  unfold deltaX deltaX4
  ring
/-- Interpolation identity for `g` in coordinate 3 (quadratic with
leading coefficient `-(4 * x1 * u6 + q * (x1 - u2 + u6) ^ 2)`): the value between `a` and `b`
dominates the linear interpolation plus the (nonnegative) curvature term.
Exact by `ring` after unfolding `deltaX`/`deltaX4`. -/
private theorem ztdih_quad3 (x1 q u2 u4 u5 u6 t a b : ℝ) :
    (b - a) * (4 * x1 * deltaX x1 u2 t u4 u5 u6 - q * (deltaX4 x1 u2 t u4 u5 u6) ^ 2)
      = (b - t) * (4 * x1 * deltaX x1 u2 a u4 u5 u6 - q * (deltaX4 x1 u2 a u4 u5 u6) ^ 2) + (t - a) * (4 * x1 * deltaX x1 u2 b u4 u5 u6 - q * (deltaX4 x1 u2 b u4 u5 u6) ^ 2)
        + (4 * x1 * u6 + q * (x1 - u2 + u6) ^ 2) * (t - a) * (b - t) * (b - a) := by
  unfold deltaX deltaX4
  ring
/-- Interpolation identity for `g` in coordinate 4 (quadratic with
leading coefficient `-(4 * x1 ^ 2 * (1 + q)`): the value between `a` and `b`
dominates the linear interpolation plus the (nonnegative) curvature term.
Exact by `ring` after unfolding `deltaX`/`deltaX4`. -/
private theorem ztdih_quad4 (x1 q u2 u3 u5 u6 t a b : ℝ) :
    (b - a) * (4 * x1 * deltaX x1 u2 u3 t u5 u6 - q * (deltaX4 x1 u2 u3 t u5 u6) ^ 2)
      = (b - t) * (4 * x1 * deltaX x1 u2 u3 a u5 u6 - q * (deltaX4 x1 u2 u3 a u5 u6) ^ 2) + (t - a) * (4 * x1 * deltaX x1 u2 u3 b u5 u6 - q * (deltaX4 x1 u2 u3 b u5 u6) ^ 2)
        + (4 * x1 ^ 2 * (1 + q)) * (t - a) * (b - t) * (b - a) := by
  unfold deltaX deltaX4
  ring
/-- Interpolation identity for `g` in coordinate 5 (quadratic with
leading coefficient `-(4 * x1 * u2 + q * (x1 + u2 - u6) ^ 2)`): the value between `a` and `b`
dominates the linear interpolation plus the (nonnegative) curvature term.
Exact by `ring` after unfolding `deltaX`/`deltaX4`. -/
private theorem ztdih_quad5 (x1 q u2 u3 u4 u6 t a b : ℝ) :
    (b - a) * (4 * x1 * deltaX x1 u2 u3 u4 t u6 - q * (deltaX4 x1 u2 u3 u4 t u6) ^ 2)
      = (b - t) * (4 * x1 * deltaX x1 u2 u3 u4 a u6 - q * (deltaX4 x1 u2 u3 u4 a u6) ^ 2) + (t - a) * (4 * x1 * deltaX x1 u2 u3 u4 b u6 - q * (deltaX4 x1 u2 u3 u4 b u6) ^ 2)
        + (4 * x1 * u2 + q * (x1 + u2 - u6) ^ 2) * (t - a) * (b - t) * (b - a) := by
  unfold deltaX deltaX4
  ring
/-- Interpolation identity for `g` in coordinate 6 (quadratic with
leading coefficient `-(4 * x1 * u3 + q * (x1 + u3 - u5) ^ 2)`): the value between `a` and `b`
dominates the linear interpolation plus the (nonnegative) curvature term.
Exact by `ring` after unfolding `deltaX`/`deltaX4`. -/
private theorem ztdih_quad6 (x1 q u2 u3 u4 u5 t a b : ℝ) :
    (b - a) * (4 * x1 * deltaX x1 u2 u3 u4 u5 t - q * (deltaX4 x1 u2 u3 u4 u5 t) ^ 2)
      = (b - t) * (4 * x1 * deltaX x1 u2 u3 u4 u5 a - q * (deltaX4 x1 u2 u3 u4 u5 a) ^ 2) + (t - a) * (4 * x1 * deltaX x1 u2 u3 u4 u5 b - q * (deltaX4 x1 u2 u3 u4 u5 b) ^ 2)
        + (4 * x1 * u3 + q * (x1 + u3 - u5) ^ 2) * (t - a) * (b - t) * (b - a) := by
  unfold deltaX deltaX4
  ring

/-! ## 2. One-coordinate concavity steps -/
/-- One-coordinate concavity step: if `g` is nonnegative at both box ends
`a`, `b` and interpolates linearly up to a nonnegative curvature term
(exactly the identity `ztdih_quad2` establishes), then `g` is nonnegative
at every `t` in the box.  Pure linear arithmetic. -/
private theorem ztdih_step2 (x1 q u3 u4 u5 u6 t a b w : ℝ)
    (ha : a ≤ t) (hb : t ≤ b) (hab : a < b) (hw : 0 ≤ w)
    (hid : (b - a) * (4 * x1 * deltaX x1 t u3 u4 u5 u6 - q * (deltaX4 x1 t u3 u4 u5 u6) ^ 2)
        = (b - t) * (4 * x1 * deltaX x1 a u3 u4 u5 u6 - q * (deltaX4 x1 a u3 u4 u5 u6) ^ 2) + (t - a) * (4 * x1 * deltaX x1 b u3 u4 u5 u6 - q * (deltaX4 x1 b u3 u4 u5 u6) ^ 2)
          + w * (t - a) * (b - t) * (b - a))
    (hga : 0 ≤ 4 * x1 * deltaX x1 a u3 u4 u5 u6 - q * (deltaX4 x1 a u3 u4 u5 u6) ^ 2) (hgb : 0 ≤ 4 * x1 * deltaX x1 b u3 u4 u5 u6 - q * (deltaX4 x1 b u3 u4 u5 u6) ^ 2) :
    0 ≤ 4 * x1 * deltaX x1 t u3 u4 u5 u6 - q * (deltaX4 x1 t u3 u4 u5 u6) ^ 2 := by
  have h5 : (0:ℝ) < b - a := by linarith
  have h1 : (0:ℝ) ≤ (b - t) * (4 * x1 * deltaX x1 a u3 u4 u5 u6 - q * (deltaX4 x1 a u3 u4 u5 u6) ^ 2) := mul_nonneg (by linarith) hga
  have h2 : (0:ℝ) ≤ (t - a) * (4 * x1 * deltaX x1 b u3 u4 u5 u6 - q * (deltaX4 x1 b u3 u4 u5 u6) ^ 2) := mul_nonneg (by linarith) hgb
  have h3 : (0:ℝ) ≤ w * (t - a) * (b - t) * (b - a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hw (by linarith)) (by linarith)) (by linarith)
  have h4 : (b - a) * (0:ℝ) ≤ (b - a) * (4 * x1 * deltaX x1 t u3 u4 u5 u6 - q * (deltaX4 x1 t u3 u4 u5 u6) ^ 2) := by
    rw [mul_zero, hid]
    linarith
  exact le_of_mul_le_mul_left h4 h5
/-- One-coordinate concavity step: if `g` is nonnegative at both box ends
`a`, `b` and interpolates linearly up to a nonnegative curvature term
(exactly the identity `ztdih_quad3` establishes), then `g` is nonnegative
at every `t` in the box.  Pure linear arithmetic. -/
private theorem ztdih_step3 (x1 q u2 u4 u5 u6 t a b w : ℝ)
    (ha : a ≤ t) (hb : t ≤ b) (hab : a < b) (hw : 0 ≤ w)
    (hid : (b - a) * (4 * x1 * deltaX x1 u2 t u4 u5 u6 - q * (deltaX4 x1 u2 t u4 u5 u6) ^ 2)
        = (b - t) * (4 * x1 * deltaX x1 u2 a u4 u5 u6 - q * (deltaX4 x1 u2 a u4 u5 u6) ^ 2) + (t - a) * (4 * x1 * deltaX x1 u2 b u4 u5 u6 - q * (deltaX4 x1 u2 b u4 u5 u6) ^ 2)
          + w * (t - a) * (b - t) * (b - a))
    (hga : 0 ≤ 4 * x1 * deltaX x1 u2 a u4 u5 u6 - q * (deltaX4 x1 u2 a u4 u5 u6) ^ 2) (hgb : 0 ≤ 4 * x1 * deltaX x1 u2 b u4 u5 u6 - q * (deltaX4 x1 u2 b u4 u5 u6) ^ 2) :
    0 ≤ 4 * x1 * deltaX x1 u2 t u4 u5 u6 - q * (deltaX4 x1 u2 t u4 u5 u6) ^ 2 := by
  have h5 : (0:ℝ) < b - a := by linarith
  have h1 : (0:ℝ) ≤ (b - t) * (4 * x1 * deltaX x1 u2 a u4 u5 u6 - q * (deltaX4 x1 u2 a u4 u5 u6) ^ 2) := mul_nonneg (by linarith) hga
  have h2 : (0:ℝ) ≤ (t - a) * (4 * x1 * deltaX x1 u2 b u4 u5 u6 - q * (deltaX4 x1 u2 b u4 u5 u6) ^ 2) := mul_nonneg (by linarith) hgb
  have h3 : (0:ℝ) ≤ w * (t - a) * (b - t) * (b - a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hw (by linarith)) (by linarith)) (by linarith)
  have h4 : (b - a) * (0:ℝ) ≤ (b - a) * (4 * x1 * deltaX x1 u2 t u4 u5 u6 - q * (deltaX4 x1 u2 t u4 u5 u6) ^ 2) := by
    rw [mul_zero, hid]
    linarith
  exact le_of_mul_le_mul_left h4 h5
/-- One-coordinate concavity step: if `g` is nonnegative at both box ends
`a`, `b` and interpolates linearly up to a nonnegative curvature term
(exactly the identity `ztdih_quad4` establishes), then `g` is nonnegative
at every `t` in the box.  Pure linear arithmetic. -/
private theorem ztdih_step4 (x1 q u2 u3 u5 u6 t a b w : ℝ)
    (ha : a ≤ t) (hb : t ≤ b) (hab : a < b) (hw : 0 ≤ w)
    (hid : (b - a) * (4 * x1 * deltaX x1 u2 u3 t u5 u6 - q * (deltaX4 x1 u2 u3 t u5 u6) ^ 2)
        = (b - t) * (4 * x1 * deltaX x1 u2 u3 a u5 u6 - q * (deltaX4 x1 u2 u3 a u5 u6) ^ 2) + (t - a) * (4 * x1 * deltaX x1 u2 u3 b u5 u6 - q * (deltaX4 x1 u2 u3 b u5 u6) ^ 2)
          + w * (t - a) * (b - t) * (b - a))
    (hga : 0 ≤ 4 * x1 * deltaX x1 u2 u3 a u5 u6 - q * (deltaX4 x1 u2 u3 a u5 u6) ^ 2) (hgb : 0 ≤ 4 * x1 * deltaX x1 u2 u3 b u5 u6 - q * (deltaX4 x1 u2 u3 b u5 u6) ^ 2) :
    0 ≤ 4 * x1 * deltaX x1 u2 u3 t u5 u6 - q * (deltaX4 x1 u2 u3 t u5 u6) ^ 2 := by
  have h5 : (0:ℝ) < b - a := by linarith
  have h1 : (0:ℝ) ≤ (b - t) * (4 * x1 * deltaX x1 u2 u3 a u5 u6 - q * (deltaX4 x1 u2 u3 a u5 u6) ^ 2) := mul_nonneg (by linarith) hga
  have h2 : (0:ℝ) ≤ (t - a) * (4 * x1 * deltaX x1 u2 u3 b u5 u6 - q * (deltaX4 x1 u2 u3 b u5 u6) ^ 2) := mul_nonneg (by linarith) hgb
  have h3 : (0:ℝ) ≤ w * (t - a) * (b - t) * (b - a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hw (by linarith)) (by linarith)) (by linarith)
  have h4 : (b - a) * (0:ℝ) ≤ (b - a) * (4 * x1 * deltaX x1 u2 u3 t u5 u6 - q * (deltaX4 x1 u2 u3 t u5 u6) ^ 2) := by
    rw [mul_zero, hid]
    linarith
  exact le_of_mul_le_mul_left h4 h5
/-- One-coordinate concavity step: if `g` is nonnegative at both box ends
`a`, `b` and interpolates linearly up to a nonnegative curvature term
(exactly the identity `ztdih_quad5` establishes), then `g` is nonnegative
at every `t` in the box.  Pure linear arithmetic. -/
private theorem ztdih_step5 (x1 q u2 u3 u4 u6 t a b w : ℝ)
    (ha : a ≤ t) (hb : t ≤ b) (hab : a < b) (hw : 0 ≤ w)
    (hid : (b - a) * (4 * x1 * deltaX x1 u2 u3 u4 t u6 - q * (deltaX4 x1 u2 u3 u4 t u6) ^ 2)
        = (b - t) * (4 * x1 * deltaX x1 u2 u3 u4 a u6 - q * (deltaX4 x1 u2 u3 u4 a u6) ^ 2) + (t - a) * (4 * x1 * deltaX x1 u2 u3 u4 b u6 - q * (deltaX4 x1 u2 u3 u4 b u6) ^ 2)
          + w * (t - a) * (b - t) * (b - a))
    (hga : 0 ≤ 4 * x1 * deltaX x1 u2 u3 u4 a u6 - q * (deltaX4 x1 u2 u3 u4 a u6) ^ 2) (hgb : 0 ≤ 4 * x1 * deltaX x1 u2 u3 u4 b u6 - q * (deltaX4 x1 u2 u3 u4 b u6) ^ 2) :
    0 ≤ 4 * x1 * deltaX x1 u2 u3 u4 t u6 - q * (deltaX4 x1 u2 u3 u4 t u6) ^ 2 := by
  have h5 : (0:ℝ) < b - a := by linarith
  have h1 : (0:ℝ) ≤ (b - t) * (4 * x1 * deltaX x1 u2 u3 u4 a u6 - q * (deltaX4 x1 u2 u3 u4 a u6) ^ 2) := mul_nonneg (by linarith) hga
  have h2 : (0:ℝ) ≤ (t - a) * (4 * x1 * deltaX x1 u2 u3 u4 b u6 - q * (deltaX4 x1 u2 u3 u4 b u6) ^ 2) := mul_nonneg (by linarith) hgb
  have h3 : (0:ℝ) ≤ w * (t - a) * (b - t) * (b - a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hw (by linarith)) (by linarith)) (by linarith)
  have h4 : (b - a) * (0:ℝ) ≤ (b - a) * (4 * x1 * deltaX x1 u2 u3 u4 t u6 - q * (deltaX4 x1 u2 u3 u4 t u6) ^ 2) := by
    rw [mul_zero, hid]
    linarith
  exact le_of_mul_le_mul_left h4 h5
/-- One-coordinate concavity step: if `g` is nonnegative at both box ends
`a`, `b` and interpolates linearly up to a nonnegative curvature term
(exactly the identity `ztdih_quad6` establishes), then `g` is nonnegative
at every `t` in the box.  Pure linear arithmetic. -/
private theorem ztdih_step6 (x1 q u2 u3 u4 u5 t a b w : ℝ)
    (ha : a ≤ t) (hb : t ≤ b) (hab : a < b) (hw : 0 ≤ w)
    (hid : (b - a) * (4 * x1 * deltaX x1 u2 u3 u4 u5 t - q * (deltaX4 x1 u2 u3 u4 u5 t) ^ 2)
        = (b - t) * (4 * x1 * deltaX x1 u2 u3 u4 u5 a - q * (deltaX4 x1 u2 u3 u4 u5 a) ^ 2) + (t - a) * (4 * x1 * deltaX x1 u2 u3 u4 u5 b - q * (deltaX4 x1 u2 u3 u4 u5 b) ^ 2)
          + w * (t - a) * (b - t) * (b - a))
    (hga : 0 ≤ 4 * x1 * deltaX x1 u2 u3 u4 u5 a - q * (deltaX4 x1 u2 u3 u4 u5 a) ^ 2) (hgb : 0 ≤ 4 * x1 * deltaX x1 u2 u3 u4 u5 b - q * (deltaX4 x1 u2 u3 u4 u5 b) ^ 2) :
    0 ≤ 4 * x1 * deltaX x1 u2 u3 u4 u5 t - q * (deltaX4 x1 u2 u3 u4 u5 t) ^ 2 := by
  have h5 : (0:ℝ) < b - a := by linarith
  have h1 : (0:ℝ) ≤ (b - t) * (4 * x1 * deltaX x1 u2 u3 u4 u5 a - q * (deltaX4 x1 u2 u3 u4 u5 a) ^ 2) := mul_nonneg (by linarith) hga
  have h2 : (0:ℝ) ≤ (t - a) * (4 * x1 * deltaX x1 u2 u3 u4 u5 b - q * (deltaX4 x1 u2 u3 u4 u5 b) ^ 2) := mul_nonneg (by linarith) hgb
  have h3 : (0:ℝ) ≤ w * (t - a) * (b - t) * (b - a) :=
    mul_nonneg (mul_nonneg (mul_nonneg hw (by linarith)) (by linarith)) (by linarith)
  have h4 : (b - a) * (0:ℝ) ≤ (b - a) * (4 * x1 * deltaX x1 u2 u3 u4 u5 t - q * (deltaX4 x1 u2 u3 u4 u5 t) ^ 2) := by
    rw [mul_zero, hid]
    linarith
  exact le_of_mul_le_mul_left h4 h5

/-! ## 3. The box-level corner reduction `ztgG_box5`

32 corner hypotheses spelled out positionally (zero unification risk); the
proof is the explicit 31-step Jensen chain: level 5 frees `x6` (16 haves),
level 4 `x5` (8), level 3 `x4` (4), level 2 `x3` (2), and the last step
frees `x2`. -/
private theorem ztgG_box5 (x1 x2 x3 x4 x5 x6 q : ℝ)
    (hq : 0 ≤ q) (hx1 : 0 ≤ x1)
    (a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : ℝ)
    (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4) (ha5 : 0 ≤ a5) (ha6 : 0 ≤ a6)
    (hab2 : a2 < b2) (hab3 : a3 < b3) (hab4 : a4 < b4) (hab5 : a5 < b5) (hab6 : a6 < b6)
    (hm2 : a2 ≤ x2) (hM2 : x2 ≤ b2) (hm3 : a3 ≤ x3) (hM3 : x3 ≤ b3)
    (hm4 : a4 ≤ x4) (hM4 : x4 ≤ b4) (hm5 : a5 ≤ x5) (hM5 : x5 ≤ b5)
    (hm6 : a6 ≤ x6) (hM6 : x6 ≤ b6)
    (h_lllll : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 a4 a5 a6 - q * (deltaX4 x1 a2 a3 a4 a5 a6) ^ 2)
    (h_llllh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 a4 a5 b6 - q * (deltaX4 x1 a2 a3 a4 a5 b6) ^ 2)
    (h_lllhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 a4 b5 a6 - q * (deltaX4 x1 a2 a3 a4 b5 a6) ^ 2)
    (h_lllhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 a4 b5 b6 - q * (deltaX4 x1 a2 a3 a4 b5 b6) ^ 2)
    (h_llhll : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 b4 a5 a6 - q * (deltaX4 x1 a2 a3 b4 a5 a6) ^ 2)
    (h_llhlh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 b4 a5 b6 - q * (deltaX4 x1 a2 a3 b4 a5 b6) ^ 2)
    (h_llhhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 b4 b5 a6 - q * (deltaX4 x1 a2 a3 b4 b5 a6) ^ 2)
    (h_llhhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 b4 b5 b6 - q * (deltaX4 x1 a2 a3 b4 b5 b6) ^ 2)
    (h_lhlll : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 a4 a5 a6 - q * (deltaX4 x1 a2 b3 a4 a5 a6) ^ 2)
    (h_lhllh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 a4 a5 b6 - q * (deltaX4 x1 a2 b3 a4 a5 b6) ^ 2)
    (h_lhlhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 a4 b5 a6 - q * (deltaX4 x1 a2 b3 a4 b5 a6) ^ 2)
    (h_lhlhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 a4 b5 b6 - q * (deltaX4 x1 a2 b3 a4 b5 b6) ^ 2)
    (h_lhhll : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 b4 a5 a6 - q * (deltaX4 x1 a2 b3 b4 a5 a6) ^ 2)
    (h_lhhlh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 b4 a5 b6 - q * (deltaX4 x1 a2 b3 b4 a5 b6) ^ 2)
    (h_lhhhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 b4 b5 a6 - q * (deltaX4 x1 a2 b3 b4 b5 a6) ^ 2)
    (h_lhhhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 b4 b5 b6 - q * (deltaX4 x1 a2 b3 b4 b5 b6) ^ 2)
    (h_hllll : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 a4 a5 a6 - q * (deltaX4 x1 b2 a3 a4 a5 a6) ^ 2)
    (h_hlllh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 a4 a5 b6 - q * (deltaX4 x1 b2 a3 a4 a5 b6) ^ 2)
    (h_hllhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 a4 b5 a6 - q * (deltaX4 x1 b2 a3 a4 b5 a6) ^ 2)
    (h_hllhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 a4 b5 b6 - q * (deltaX4 x1 b2 a3 a4 b5 b6) ^ 2)
    (h_hlhll : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 b4 a5 a6 - q * (deltaX4 x1 b2 a3 b4 a5 a6) ^ 2)
    (h_hlhlh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 b4 a5 b6 - q * (deltaX4 x1 b2 a3 b4 a5 b6) ^ 2)
    (h_hlhhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 b4 b5 a6 - q * (deltaX4 x1 b2 a3 b4 b5 a6) ^ 2)
    (h_hlhhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 b4 b5 b6 - q * (deltaX4 x1 b2 a3 b4 b5 b6) ^ 2)
    (h_hhlll : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 a4 a5 a6 - q * (deltaX4 x1 b2 b3 a4 a5 a6) ^ 2)
    (h_hhllh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 a4 a5 b6 - q * (deltaX4 x1 b2 b3 a4 a5 b6) ^ 2)
    (h_hhlhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 a4 b5 a6 - q * (deltaX4 x1 b2 b3 a4 b5 a6) ^ 2)
    (h_hhlhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 a4 b5 b6 - q * (deltaX4 x1 b2 b3 a4 b5 b6) ^ 2)
    (h_hhhll : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 b4 a5 a6 - q * (deltaX4 x1 b2 b3 b4 a5 a6) ^ 2)
    (h_hhhlh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 b4 a5 b6 - q * (deltaX4 x1 b2 b3 b4 a5 b6) ^ 2)
    (h_hhhhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 b4 b5 a6 - q * (deltaX4 x1 b2 b3 b4 b5 a6) ^ 2)
    (h_hhhhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 b4 b5 b6 - q * (deltaX4 x1 b2 b3 b4 b5 b6) ^ 2)
    : (0:ℝ) ≤ 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 - q * (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2 := by
  have e5_llll : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 a4 a5 x6 - q * (deltaX4 x1 a2 a3 a4 a5 x6) ^ 2 :=
    ztdih_step6 x1 q a2 a3 a4 a5 x6 a6 b6 (4 * x1 * a3 + q * (x1 + a3 - a5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha3) (mul_nonneg hq (sq_nonneg (x1 + a3 - a5))))
      (ztdih_quad6 x1 q a2 a3 a4 a5 x6 a6 b6)
      h_lllll h_llllh
  have e5_lllh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 a4 b5 x6 - q * (deltaX4 x1 a2 a3 a4 b5 x6) ^ 2 :=
    ztdih_step6 x1 q a2 a3 a4 b5 x6 a6 b6 (4 * x1 * a3 + q * (x1 + a3 - b5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha3) (mul_nonneg hq (sq_nonneg (x1 + a3 - b5))))
      (ztdih_quad6 x1 q a2 a3 a4 b5 x6 a6 b6)
      h_lllhl h_lllhh
  have e5_llhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 b4 a5 x6 - q * (deltaX4 x1 a2 a3 b4 a5 x6) ^ 2 :=
    ztdih_step6 x1 q a2 a3 b4 a5 x6 a6 b6 (4 * x1 * a3 + q * (x1 + a3 - a5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha3) (mul_nonneg hq (sq_nonneg (x1 + a3 - a5))))
      (ztdih_quad6 x1 q a2 a3 b4 a5 x6 a6 b6)
      h_llhll h_llhlh
  have e5_llhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 b4 b5 x6 - q * (deltaX4 x1 a2 a3 b4 b5 x6) ^ 2 :=
    ztdih_step6 x1 q a2 a3 b4 b5 x6 a6 b6 (4 * x1 * a3 + q * (x1 + a3 - b5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha3) (mul_nonneg hq (sq_nonneg (x1 + a3 - b5))))
      (ztdih_quad6 x1 q a2 a3 b4 b5 x6 a6 b6)
      h_llhhl h_llhhh
  have e5_lhll : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 a4 a5 x6 - q * (deltaX4 x1 a2 b3 a4 a5 x6) ^ 2 :=
    ztdih_step6 x1 q a2 b3 a4 a5 x6 a6 b6 (4 * x1 * b3 + q * (x1 + b3 - a5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha3 (le_of_lt hab3))) (mul_nonneg hq (sq_nonneg (x1 + b3 - a5))))
      (ztdih_quad6 x1 q a2 b3 a4 a5 x6 a6 b6)
      h_lhlll h_lhllh
  have e5_lhlh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 a4 b5 x6 - q * (deltaX4 x1 a2 b3 a4 b5 x6) ^ 2 :=
    ztdih_step6 x1 q a2 b3 a4 b5 x6 a6 b6 (4 * x1 * b3 + q * (x1 + b3 - b5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha3 (le_of_lt hab3))) (mul_nonneg hq (sq_nonneg (x1 + b3 - b5))))
      (ztdih_quad6 x1 q a2 b3 a4 b5 x6 a6 b6)
      h_lhlhl h_lhlhh
  have e5_lhhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 b4 a5 x6 - q * (deltaX4 x1 a2 b3 b4 a5 x6) ^ 2 :=
    ztdih_step6 x1 q a2 b3 b4 a5 x6 a6 b6 (4 * x1 * b3 + q * (x1 + b3 - a5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha3 (le_of_lt hab3))) (mul_nonneg hq (sq_nonneg (x1 + b3 - a5))))
      (ztdih_quad6 x1 q a2 b3 b4 a5 x6 a6 b6)
      h_lhhll h_lhhlh
  have e5_lhhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 b4 b5 x6 - q * (deltaX4 x1 a2 b3 b4 b5 x6) ^ 2 :=
    ztdih_step6 x1 q a2 b3 b4 b5 x6 a6 b6 (4 * x1 * b3 + q * (x1 + b3 - b5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha3 (le_of_lt hab3))) (mul_nonneg hq (sq_nonneg (x1 + b3 - b5))))
      (ztdih_quad6 x1 q a2 b3 b4 b5 x6 a6 b6)
      h_lhhhl h_lhhhh
  have e5_hlll : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 a4 a5 x6 - q * (deltaX4 x1 b2 a3 a4 a5 x6) ^ 2 :=
    ztdih_step6 x1 q b2 a3 a4 a5 x6 a6 b6 (4 * x1 * a3 + q * (x1 + a3 - a5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha3) (mul_nonneg hq (sq_nonneg (x1 + a3 - a5))))
      (ztdih_quad6 x1 q b2 a3 a4 a5 x6 a6 b6)
      h_hllll h_hlllh
  have e5_hllh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 a4 b5 x6 - q * (deltaX4 x1 b2 a3 a4 b5 x6) ^ 2 :=
    ztdih_step6 x1 q b2 a3 a4 b5 x6 a6 b6 (4 * x1 * a3 + q * (x1 + a3 - b5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha3) (mul_nonneg hq (sq_nonneg (x1 + a3 - b5))))
      (ztdih_quad6 x1 q b2 a3 a4 b5 x6 a6 b6)
      h_hllhl h_hllhh
  have e5_hlhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 b4 a5 x6 - q * (deltaX4 x1 b2 a3 b4 a5 x6) ^ 2 :=
    ztdih_step6 x1 q b2 a3 b4 a5 x6 a6 b6 (4 * x1 * a3 + q * (x1 + a3 - a5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha3) (mul_nonneg hq (sq_nonneg (x1 + a3 - a5))))
      (ztdih_quad6 x1 q b2 a3 b4 a5 x6 a6 b6)
      h_hlhll h_hlhlh
  have e5_hlhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 b4 b5 x6 - q * (deltaX4 x1 b2 a3 b4 b5 x6) ^ 2 :=
    ztdih_step6 x1 q b2 a3 b4 b5 x6 a6 b6 (4 * x1 * a3 + q * (x1 + a3 - b5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha3) (mul_nonneg hq (sq_nonneg (x1 + a3 - b5))))
      (ztdih_quad6 x1 q b2 a3 b4 b5 x6 a6 b6)
      h_hlhhl h_hlhhh
  have e5_hhll : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 a4 a5 x6 - q * (deltaX4 x1 b2 b3 a4 a5 x6) ^ 2 :=
    ztdih_step6 x1 q b2 b3 a4 a5 x6 a6 b6 (4 * x1 * b3 + q * (x1 + b3 - a5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha3 (le_of_lt hab3))) (mul_nonneg hq (sq_nonneg (x1 + b3 - a5))))
      (ztdih_quad6 x1 q b2 b3 a4 a5 x6 a6 b6)
      h_hhlll h_hhllh
  have e5_hhlh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 a4 b5 x6 - q * (deltaX4 x1 b2 b3 a4 b5 x6) ^ 2 :=
    ztdih_step6 x1 q b2 b3 a4 b5 x6 a6 b6 (4 * x1 * b3 + q * (x1 + b3 - b5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha3 (le_of_lt hab3))) (mul_nonneg hq (sq_nonneg (x1 + b3 - b5))))
      (ztdih_quad6 x1 q b2 b3 a4 b5 x6 a6 b6)
      h_hhlhl h_hhlhh
  have e5_hhhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 b4 a5 x6 - q * (deltaX4 x1 b2 b3 b4 a5 x6) ^ 2 :=
    ztdih_step6 x1 q b2 b3 b4 a5 x6 a6 b6 (4 * x1 * b3 + q * (x1 + b3 - a5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha3 (le_of_lt hab3))) (mul_nonneg hq (sq_nonneg (x1 + b3 - a5))))
      (ztdih_quad6 x1 q b2 b3 b4 a5 x6 a6 b6)
      h_hhhll h_hhhlh
  have e5_hhhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 b4 b5 x6 - q * (deltaX4 x1 b2 b3 b4 b5 x6) ^ 2 :=
    ztdih_step6 x1 q b2 b3 b4 b5 x6 a6 b6 (4 * x1 * b3 + q * (x1 + b3 - b5) ^ 2)
      hm6 hM6 hab6 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha3 (le_of_lt hab3))) (mul_nonneg hq (sq_nonneg (x1 + b3 - b5))))
      (ztdih_quad6 x1 q b2 b3 b4 b5 x6 a6 b6)
      h_hhhhl h_hhhhh
  have e4_lll : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 a4 x5 x6 - q * (deltaX4 x1 a2 a3 a4 x5 x6) ^ 2 :=
    ztdih_step5 x1 q a2 a3 a4 x6 x5 a5 b5 (4 * x1 * a2 + q * (x1 + a2 - x6) ^ 2)
      hm5 hM5 hab5 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha2) (mul_nonneg hq (sq_nonneg (x1 + a2 - x6))))
      (ztdih_quad5 x1 q a2 a3 a4 x6 x5 a5 b5)
      e5_llll e5_lllh
  have e4_llh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 b4 x5 x6 - q * (deltaX4 x1 a2 a3 b4 x5 x6) ^ 2 :=
    ztdih_step5 x1 q a2 a3 b4 x6 x5 a5 b5 (4 * x1 * a2 + q * (x1 + a2 - x6) ^ 2)
      hm5 hM5 hab5 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha2) (mul_nonneg hq (sq_nonneg (x1 + a2 - x6))))
      (ztdih_quad5 x1 q a2 a3 b4 x6 x5 a5 b5)
      e5_llhl e5_llhh
  have e4_lhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 a4 x5 x6 - q * (deltaX4 x1 a2 b3 a4 x5 x6) ^ 2 :=
    ztdih_step5 x1 q a2 b3 a4 x6 x5 a5 b5 (4 * x1 * a2 + q * (x1 + a2 - x6) ^ 2)
      hm5 hM5 hab5 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha2) (mul_nonneg hq (sq_nonneg (x1 + a2 - x6))))
      (ztdih_quad5 x1 q a2 b3 a4 x6 x5 a5 b5)
      e5_lhll e5_lhlh
  have e4_lhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 b4 x5 x6 - q * (deltaX4 x1 a2 b3 b4 x5 x6) ^ 2 :=
    ztdih_step5 x1 q a2 b3 b4 x6 x5 a5 b5 (4 * x1 * a2 + q * (x1 + a2 - x6) ^ 2)
      hm5 hM5 hab5 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ha2) (mul_nonneg hq (sq_nonneg (x1 + a2 - x6))))
      (ztdih_quad5 x1 q a2 b3 b4 x6 x5 a5 b5)
      e5_lhhl e5_lhhh
  have e4_hll : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 a4 x5 x6 - q * (deltaX4 x1 b2 a3 a4 x5 x6) ^ 2 :=
    ztdih_step5 x1 q b2 a3 a4 x6 x5 a5 b5 (4 * x1 * b2 + q * (x1 + b2 - x6) ^ 2)
      hm5 hM5 hab5 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha2 (le_of_lt hab2))) (mul_nonneg hq (sq_nonneg (x1 + b2 - x6))))
      (ztdih_quad5 x1 q b2 a3 a4 x6 x5 a5 b5)
      e5_hlll e5_hllh
  have e4_hlh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 b4 x5 x6 - q * (deltaX4 x1 b2 a3 b4 x5 x6) ^ 2 :=
    ztdih_step5 x1 q b2 a3 b4 x6 x5 a5 b5 (4 * x1 * b2 + q * (x1 + b2 - x6) ^ 2)
      hm5 hM5 hab5 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha2 (le_of_lt hab2))) (mul_nonneg hq (sq_nonneg (x1 + b2 - x6))))
      (ztdih_quad5 x1 q b2 a3 b4 x6 x5 a5 b5)
      e5_hlhl e5_hlhh
  have e4_hhl : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 a4 x5 x6 - q * (deltaX4 x1 b2 b3 a4 x5 x6) ^ 2 :=
    ztdih_step5 x1 q b2 b3 a4 x6 x5 a5 b5 (4 * x1 * b2 + q * (x1 + b2 - x6) ^ 2)
      hm5 hM5 hab5 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha2 (le_of_lt hab2))) (mul_nonneg hq (sq_nonneg (x1 + b2 - x6))))
      (ztdih_quad5 x1 q b2 b3 a4 x6 x5 a5 b5)
      e5_hhll e5_hhlh
  have e4_hhh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 b4 x5 x6 - q * (deltaX4 x1 b2 b3 b4 x5 x6) ^ 2 :=
    ztdih_step5 x1 q b2 b3 b4 x6 x5 a5 b5 (4 * x1 * b2 + q * (x1 + b2 - x6) ^ 2)
      hm5 hM5 hab5 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) (le_trans ha2 (le_of_lt hab2))) (mul_nonneg hq (sq_nonneg (x1 + b2 - x6))))
      (ztdih_quad5 x1 q b2 b3 b4 x6 x5 a5 b5)
      e5_hhhl e5_hhhh
  have e3_ll : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 a3 x4 x5 x6 - q * (deltaX4 x1 a2 a3 x4 x5 x6) ^ 2 :=
    ztdih_step4 x1 q a2 a3 x5 x6 x4 a4 b4 (4 * x1 ^ 2 * (1 + q))
      hm4 hM4 hab4 (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg x1)) (by linarith [hq]))
      (ztdih_quad4 x1 q a2 a3 x5 x6 x4 a4 b4)
      e4_lll e4_llh
  have e3_lh : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 b3 x4 x5 x6 - q * (deltaX4 x1 a2 b3 x4 x5 x6) ^ 2 :=
    ztdih_step4 x1 q a2 b3 x5 x6 x4 a4 b4 (4 * x1 ^ 2 * (1 + q))
      hm4 hM4 hab4 (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg x1)) (by linarith [hq]))
      (ztdih_quad4 x1 q a2 b3 x5 x6 x4 a4 b4)
      e4_lhl e4_lhh
  have e3_hl : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 a3 x4 x5 x6 - q * (deltaX4 x1 b2 a3 x4 x5 x6) ^ 2 :=
    ztdih_step4 x1 q b2 a3 x5 x6 x4 a4 b4 (4 * x1 ^ 2 * (1 + q))
      hm4 hM4 hab4 (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg x1)) (by linarith [hq]))
      (ztdih_quad4 x1 q b2 a3 x5 x6 x4 a4 b4)
      e4_hll e4_hlh
  have e3_hh : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 b3 x4 x5 x6 - q * (deltaX4 x1 b2 b3 x4 x5 x6) ^ 2 :=
    ztdih_step4 x1 q b2 b3 x5 x6 x4 a4 b4 (4 * x1 ^ 2 * (1 + q))
      hm4 hM4 hab4 (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg x1)) (by linarith [hq]))
      (ztdih_quad4 x1 q b2 b3 x5 x6 x4 a4 b4)
      e4_hhl e4_hhh
  have e2_l : (0:ℝ) ≤ 4 * x1 * deltaX x1 a2 x3 x4 x5 x6 - q * (deltaX4 x1 a2 x3 x4 x5 x6) ^ 2 :=
    ztdih_step3 x1 q a2 x4 x5 x6 x3 a3 b3 (4 * x1 * x6 + q * (x1 - a2 + x6) ^ 2)
      hm3 hM3 hab3 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ((le_trans ha6 hm6))) (mul_nonneg hq (sq_nonneg (x1 - a2 + x6))))
      (ztdih_quad3 x1 q a2 x4 x5 x6 x3 a3 b3)
      e3_ll e3_lh
  have e2_h : (0:ℝ) ≤ 4 * x1 * deltaX x1 b2 x3 x4 x5 x6 - q * (deltaX4 x1 b2 x3 x4 x5 x6) ^ 2 :=
    ztdih_step3 x1 q b2 x4 x5 x6 x3 a3 b3 (4 * x1 * x6 + q * (x1 - b2 + x6) ^ 2)
      hm3 hM3 hab3 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ((le_trans ha6 hm6))) (mul_nonneg hq (sq_nonneg (x1 - b2 + x6))))
      (ztdih_quad3 x1 q b2 x4 x5 x6 x3 a3 b3)
      e3_hl e3_hh
  exact ztdih_step2 x1 q x3 x4 x5 x6 x2 a2 b2 (4 * x1 * x5 + q * (x1 - x3 + x5) ^ 2)
    hm2 hM2 hab2 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx1) ((le_trans ha5 hm5))) (mul_nonneg hq (sq_nonneg (x1 - x3 + x5))))
    (ztdih_quad2 x1 q x3 x4 x5 x6 x2 a2 b2)
    e2_l e2_h

/-! ## 4. The 128 vertex-line certificates -/
/-- line `(lo,lo,lo,lo,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lllll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.0688) (6.0688) (4) (4) - (64/25) * (deltaX4 x1 (4) (6.0688) (6.0688) (4) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.0688) (6.0688) (4) (4) - (64/25) * (deltaX4 x1 (4) (6.0688) (6.0688) (4) (4)) ^ 2
      = (18636705534966844/3814697265625) + (x1 - (6.0688)) * ((4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
        + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
      + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (4629554551524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (31015561822012057/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (265246118532364905127/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (22026869825459957653343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (4629554551524/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (31015561822012057/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (265246118532364905127/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (22026869825459957653343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (4629554551524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (31015561822012057/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (265246118532364905127/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (22026869825459957653343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
      + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
      + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (18636705534966844/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,lo,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_llllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.0688) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.0688) (6.0688) (4) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.0688) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.0688) (6.0688) (4) (6.3504)) ^ 2
      = (21219272815193856/3814697265625) + (x1 - (6.0688)) * ((2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
        + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2274006488256/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (85003858289227583/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (168232248290565770651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (85946902791775172693343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2274006488256/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (85003858289227583/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (168232248290565770651/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (85946902791775172693343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2274006488256/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (85003858289227583/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (168232248290565770651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (85946902791775172693343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (21219272815193856/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,hi,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lllhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.0688) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 x1 (4) (6.0688) (6.0688) (6.3504) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.0688) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 x1 (4) (6.0688) (6.0688) (6.3504) (4)) ^ 2
      = (23721919240194396/3814697265625) + (x1 - (6.0688)) * ((1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
        + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (1921178384004/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (70840295902266557/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (138040106561621666651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (69250465977209466443343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (1921178384004/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (70840295902266557/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (138040106561621666651/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (69250465977209466443343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (1921178384004/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (70840295902266557/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (138040106561621666651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (69250465977209466443343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (23721919240194396/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,hi,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lllhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.0688) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.0688) (6.0688) (6.3504) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.0688) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.0688) (6.0688) (6.3504) (6.3504)) ^ 2
      = (26236834304961904/3814697265625) + (x1 - (6.0688)) * ((14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
        + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14173389401216/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (107704359888708067/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (362201512251697320461/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (113610091324855881483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14173389401216/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (107704359888708067/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (362201512251697320461/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (113610091324855881483343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14173389401216/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (107704359888708067/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (362201512251697320461/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (113610091324855881483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (26236834304961904/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,lo,lo)` of debt `1100` (Taylor end = hi);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_llhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.0688) (8) (4) (4) - (64/25) * (deltaX4 x1 (4) (6.0688) (8) (4) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.0688) (8) (4) (4) - (64/25) * (deltaX4 x1 (4) (6.0688) (8) (4) (4)) ^ 2
      = (726111170992410319620100240119/596046447753906250000000000) + ((7.02674064) - x1) * ((57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
        + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ ((7.02674064) - x1) := by linarith
  have hd2 : ((7.02674064) - x1) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
      + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3)
      = (57653359402382962436439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3
        + 3 * (304881230379406355598067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2
        + 3 * (44654587353140406177563/23841857910156250000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1))
        + (156491412176608718532689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (57653359402382962436439/23841857910156250000) := by norm_num
  have hb1 : (0:ℝ) ≤ (304881230379406355598067/143051147460937500000) := by norm_num
  have hb2 : (0:ℝ) ≤ (44654587353140406177563/23841857910156250000) := by norm_num
  have hb3 : (0:ℝ) ≤ (156491412176608718532689/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - ((7.02674064) - x1) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - ((7.02674064) - x1))]
  have hT2 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 2 := by nlinarith [sq_nonneg (((7.02674064) - x1))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (57653359402382962436439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (304881230379406355598067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (44654587353140406177563/23841857910156250000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (156491412176608718532689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
      + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ ((7.02674064) - x1) * ((57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
      + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (726111170992410319620100240119/596046447753906250000000000) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,lo,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_llhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.0688) (8) (4) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.0688) (8) (4) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.0688) (8) (4) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.0688) (8) (4) (6.3504)) ^ 2
      = (25403000815519516/3814697265625) + (x1 - (6.0688)) * ((6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
        + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (6577980068448/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (44297684286006113/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (47823879406502196139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (64825195902677480297311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (6577980068448/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (44297684286006113/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (47823879406502196139/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (64825195902677480297311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (6577980068448/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (44297684286006113/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (47823879406502196139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (64825195902677480297311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (25403000815519516/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,hi,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_llhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.0688) (8) (6.3504) (4) - (64/25) * (deltaX4 x1 (4) (6.0688) (8) (6.3504) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.0688) (8) (6.3504) (4) - (64/25) * (deltaX4 x1 (4) (6.0688) (8) (6.3504) (4)) ^ 2
      = (24809936090203804/3814697265625) + (x1 - (6.0688)) * ((3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
        + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (3997675257624/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24012889727315087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (21302250611249631139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (18679755249108567797311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3997675257624/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (24012889727315087/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (21302250611249631139/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (18679755249108567797311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3997675257624/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24012889727315087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (21302250611249631139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (18679755249108567797311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (24809936090203804/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,hi,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_llhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.0688) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.0688) (8) (6.3504) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.0688) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.0688) (8) (6.3504) (6.3504)) ^ 2
      = (1439388082724572/152587890625) + (x1 - (6.0688)) * ((105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
        + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (105939958156/48828125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (1615027736093192/762939453125) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (23412926639316978431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (186387132809619666627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (105939958156/48828125) := by norm_num
  have hb1 : (0:ℝ) ≤ (1615027736093192/762939453125) := by norm_num
  have hb2 : (0:ℝ) ≤ (23412926639316978431/11444091796875000) := by norm_num
  have hb3 : (0:ℝ) ≤ (186387132809619666627311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (105939958156/48828125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (1615027736093192/762939453125) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (23412926639316978431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (186387132809619666627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1439388082724572/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,lo,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lhlll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (8) (6.0688) (4) (4) - (64/25) * (deltaX4 x1 (4) (8) (6.0688) (4) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (8) (6.0688) (4) (4) - (64/25) * (deltaX4 x1 (4) (8) (6.0688) (4) (4)) ^ 2
      = (19731737815380424/3814697265625) + (x1 - (6.0688)) * ((8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
        + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
      + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (8574199328748/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (15730053917688752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (608875342059929771111/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (60526496222564756398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8574199328748/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (15730053917688752/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (608875342059929771111/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (60526496222564756398343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8574199328748/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (15730053917688752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (608875342059929771111/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (60526496222564756398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
      + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
      + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (19731737815380424/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,lo,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lhllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (8) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 x1 (4) (8) (6.0688) (4) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (8) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 x1 (4) (8) (6.0688) (4) (6.3504)) ^ 2
      = (106196226552972/30517578125) + (x1 - (6.0688)) * ((2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
        + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2754125379156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (105593526633758209/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1074294529100447219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (113212985780778955813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2754125379156/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (105593526633758209/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1074294529100447219239/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (113212985780778955813343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2754125379156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (105593526633758209/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1074294529100447219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (113212985780778955813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (106196226552972/30517578125) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,hi,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lhlhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (8) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 x1 (4) (8) (6.0688) (6.3504) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (8) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 x1 (4) (8) (6.0688) (6.3504) (4)) ^ 2
      = (178908270289772/30517578125) + (x1 - (6.0688)) * ((2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
        + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2274067931156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (28596126123684403/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (858213106846347219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (88826385584825830813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2274067931156/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (28596126123684403/15258789062500) := by norm_num
  have hb2 : (0:ℝ) ≤ (858213106846347219239/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (88826385584825830813343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2274067931156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (28596126123684403/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (858213106846347219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (88826385584825830813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (178908270289772/30517578125) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,hi,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lhlhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (8) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (4) (8) (6.0688) (6.3504) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (8) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (4) (8) (6.0688) (6.3504) (6.3504)) ^ 2
      = (17316378432875836/3814697265625) + (x1 - (6.0688)) * ((14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
        + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14654252706952/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (18881825174755399/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (387885372288628115789/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (123987357311089980228343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14654252706952/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (18881825174755399/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (387885372288628115789/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (123987357311089980228343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14654252706952/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (18881825174755399/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (387885372288628115789/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (123987357311089980228343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (17316378432875836/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,lo,lo)` of debt `1100` (Taylor end = hi);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lhhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (8) (8) (4) (4) - (64/25) * (deltaX4 x1 (4) (8) (8) (4) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (8) (8) (4) (4) - (64/25) * (deltaX4 x1 (4) (8) (8) (4) (4)) ^ 2
      = (2921190917990425673459562700119/596046447753906250000000000) + ((7.02674064) - x1) * ((16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
        + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ ((7.02674064) - x1) := by linarith
  have hd2 : ((7.02674064) - x1) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
      + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3)
      = (16551561326479222131439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3
        + 3 * (69243748144937269378067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2
        + 3 * (21415345170709314792689/71525573730468750000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1))
        + (13165516787084314792689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (16551561326479222131439/23841857910156250000) := by norm_num
  have hb1 : (0:ℝ) ≤ (69243748144937269378067/143051147460937500000) := by norm_num
  have hb2 : (0:ℝ) ≤ (21415345170709314792689/71525573730468750000) := by norm_num
  have hb3 : (0:ℝ) ≤ (13165516787084314792689/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - ((7.02674064) - x1) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - ((7.02674064) - x1))]
  have hT2 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 2 := by nlinarith [sq_nonneg (((7.02674064) - x1))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (16551561326479222131439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (69243748144937269378067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (21415345170709314792689/71525573730468750000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (13165516787084314792689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
      + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ ((7.02674064) - x1) * ((16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
      + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (2921190917990425673459562700119/596046447753906250000000000) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,lo,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lhhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (8) (8) (4) (6.3504) - (64/25) * (deltaX4 x1 (4) (8) (8) (4) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (8) (8) (4) (6.3504) - (64/25) * (deltaX4 x1 (4) (8) (8) (4) (6.3504)) ^ 2
      = (27809635670094064/3814697265625) + (x1 - (6.0688)) * ((13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
        + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (13674843822368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (25221415223494277/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (122933786338992914387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (197588372920312352787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (13674843822368/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (25221415223494277/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (122933786338992914387/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (197588372920312352787311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (13674843822368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (25221415223494277/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (122933786338992914387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (197588372920312352787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (27809635670094064/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,hi,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lhhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (8) (8) (6.3504) (4) - (64/25) * (deltaX4 x1 (4) (8) (8) (6.3504) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (8) (8) (6.3504) (4) - (64/25) * (deltaX4 x1 (4) (8) (8) (6.3504) (4)) ^ 2
      = (30913120738284064/3814697265625) + (x1 - (6.0688)) * ((9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
        + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (9696512712368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (17311295901568027/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (81129447275980414387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (124158237059656102787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (9696512712368/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (17311295901568027/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (81129447275980414387/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (124158237059656102787311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (9696512712368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (17311295901568027/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (81129447275980414387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (124158237059656102787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (30913120738284064/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,hi,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_lhhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (8) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (4) (8) (8) (6.3504) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (8) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (4) (8) (8) (6.3504) (6.3504)) ^ 2
      = (37415625546675136/3814697265625) + (x1 - (6.0688)) * ((18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
        + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (18419627374656/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (11540546965738018/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (172664326686972362903/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (285372675821715170367311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (18419627374656/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (11540546965738018/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (172664326686972362903/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (285372675821715170367311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (18419627374656/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (11540546965738018/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (172664326686972362903/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (285372675821715170367311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (37415625546675136/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,lo,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hllll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.0688) (6.0688) (4) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (6.0688) (4) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.0688) (6.0688) (4) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (6.0688) (4) (4)) ^ 2
      = (24766388408306844/3814697265625) + (x1 - (6.0688)) * ((1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
        + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (1948081726392/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (35884783429795003/22888183593750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (139739439711815462651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (70052614094782744568343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (1948081726392/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (35884783429795003/22888183593750) := by norm_num
  have hb2 : (0:ℝ) ≤ (139739439711815462651/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (70052614094782744568343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (1948081726392/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (35884783429795003/22888183593750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (139739439711815462651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (70052614094782744568343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (24766388408306844/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,lo,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hlllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.0688) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (6.0688) (4) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.0688) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (6.0688) (4) (6.3504)) ^ 2
      = (25883117520063856/3814697265625) + (x1 - (6.0688)) * ((14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
        + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14106464769728/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (35737753568836433/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1081801900472716601383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (113121103747484731483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14106464769728/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (35737753568836433/15258789062500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1081801900472716601383/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (113121103747484731483343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14106464769728/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (35737753568836433/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1081801900472716601383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (113121103747484731483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (25883117520063856/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,hi,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hllhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.0688) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (6.0688) (6.3504) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.0688) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (6.0688) (6.3504) (4)) ^ 2
      = (1009646443479024/152587890625) + (x1 - (6.0688)) * ((2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
        + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2852000121408/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (108491710261323731/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1095855703770605241383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (114717261148279831483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2852000121408/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (108491710261323731/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1095855703770605241383/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (114717261148279831483343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2852000121408/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (108491710261323731/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1095855703770605241383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (114717261148279831483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1009646443479024/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,hi,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hllhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.0688) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (6.0688) (6.3504) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.0688) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (6.0688) (6.3504) (6.3504)) ^ 2
      = (27039395629082824/3814697265625) + (x1 - (6.0688)) * ((16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
        + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
      + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (16770080807148/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (32297176289804752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1323224622028264209511/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (140701940611219268398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (16770080807148/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (32297176289804752/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (1323224622028264209511/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (140701940611219268398343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (16770080807148/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (32297176289804752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1323224622028264209511/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (140701940611219268398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
      + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
      + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (27039395629082824/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,lo,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hlhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.0688) (8) (4) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (8) (4) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.0688) (8) (4) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (8) (4) (4)) ^ 2
      = (1456556422912/244140625) + (x1 - (6.0688)) * ((5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
        + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (5305644288/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (4705232128227134/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (14712793615458253639/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (7531484459817624047311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (5305644288/9765625) := by norm_num
  have hb1 : (0:ℝ) ≤ (4705232128227134/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (14712793615458253639/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (7531484459817624047311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (5305644288/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (4705232128227134/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (14712793615458253639/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (7531484459817624047311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1456556422912/244140625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,lo,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hlhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.0688) (8) (4) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (8) (4) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.0688) (8) (4) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (8) (4) (6.3504)) ^ 2
      = (36052365919299516/3814697265625) + (x1 - (6.0688)) * ((2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
        + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2657332885292/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24310943036688188/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (7833720841032531477/3814697265625000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (187145005911877366627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2657332885292/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (24310943036688188/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (7833720841032531477/3814697265625000) := by norm_num
  have hb3 : (0:ℝ) ≤ (187145005911877366627311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2657332885292/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24310943036688188/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (7833720841032531477/3814697265625000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (187145005911877366627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (36052365919299516/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,hi,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hlhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.0688) (8) (6.3504) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (8) (6.3504) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.0688) (8) (6.3504) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (8) (6.3504) (4)) ^ 2
      = (35831790122294524/3814697265625) + (x1 - (6.0688)) * ((2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
        + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2710258910444/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24838857216231796/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (24060809396384810431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (192073168970467566627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2710258910444/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (24838857216231796/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (24060809396384810431/11444091796875000) := by norm_num
  have hb3 : (0:ℝ) ≤ (192073168970467566627311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2710258910444/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24838857216231796/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (24060809396384810431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (192073168970467566627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (35831790122294524/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,hi,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hlhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.0688) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (8) (6.3504) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.0688) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.0688) (8) (6.3504) (6.3504)) ^ 2
      = (46289875577544736/3814697265625) + (x1 - (6.0688)) * ((20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
        + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
      + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (20738696783008/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (39019283553664346/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (194937043856093730671/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (323030654761564709207311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (20738696783008/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (39019283553664346/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (194937043856093730671/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (323030654761564709207311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (20738696783008/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (39019283553664346/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (194937043856093730671/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (323030654761564709207311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
      + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
      + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (46289875577544736/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,lo,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hhlll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (8) (6.0688) (4) (4) - (64/25) * (deltaX4 x1 (6.3504) (8) (6.0688) (4) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (8) (6.0688) (4) (4) - (64/25) * (deltaX4 x1 (6.3504) (8) (6.0688) (4) (4)) ^ 2
      = (208946833566572/30517578125) + (x1 - (6.0688)) * ((2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
        + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2439562533156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (91840511827285709/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (305731766740332406413/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (94810036854302393313343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2439562533156/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (91840511827285709/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (305731766740332406413/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (94810036854302393313343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2439562533156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (91840511827285709/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (305731766740332406413/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (94810036854302393313343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (208946833566572/30517578125) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,lo,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hhllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (8) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (8) (6.0688) (4) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (8) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (8) (6.0688) (4) (6.3504)) ^ 2
      = (20447825989797884/3814697265625) + (x1 - (6.0688)) * ((15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
        + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (15280284373524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (117922714365242677/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1209339008207190007367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (128679872885622114603343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (15280284373524/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (117922714365242677/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1209339008207190007367/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (128679872885622114603343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (15280284373524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (117922714365242677/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1209339008207190007367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (128679872885622114603343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (20447825989797884/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,hi,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hhlhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (8) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 x1 (6.3504) (8) (6.0688) (6.3504) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (8) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 x1 (6.3504) (8) (6.0688) (6.3504) (4)) ^ 2
      = (25617415498476544/3814697265625) + (x1 - (6.0688)) * ((14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
        + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14797673492096/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (22711915608862627/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1158272097895699167367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (122585866905029795853343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14797673492096/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (22711915608862627/9155273437500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1158272097895699167367/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (122585866905029795853343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14797673492096/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (22711915608862627/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1158272097895699167367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (122585866905029795853343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (25617415498476544/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,hi,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hhlhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (8) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (8) (6.0688) (6.3504) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (8) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (8) (6.0688) (6.3504) (6.3504)) ^ 2
      = (21126580626452576/3814697265625) + (x1 - (6.0688)) * ((3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
        + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
      + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (3256927030976/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (126848575828496087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (262842992835682327099/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (141406782533305717143343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3256927030976/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (126848575828496087/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (262842992835682327099/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (141406782533305717143343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3256927030976/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (126848575828496087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (262842992835682327099/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (141406782533305717143343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
      + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
      + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (21126580626452576/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,lo,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hhhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (8) (8) (4) (4) - (64/25) * (deltaX4 x1 (6.3504) (8) (8) (4) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (8) (8) (4) (4) - (64/25) * (deltaX4 x1 (6.3504) (8) (8) (4) (4)) ^ 2
      = (28682420748974064/3814697265625) + (x1 - (6.0688)) * ((8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
        + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (8945941852368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (5288499003125384/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (24569353388853888129/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (111468604129859227787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8945941852368/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (5288499003125384/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (24569353388853888129/19073486328125000) := by norm_num
  have hb3 : (0:ℝ) ≤ (111468604129859227787311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8945941852368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (5288499003125384/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (24569353388853888129/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (111468604129859227787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (28682420748974064/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,lo,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hhhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (8) (8) (4) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (8) (8) (4) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (8) (8) (4) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (8) (8) (4) (6.3504)) ^ 2
      = (1523145779643468/152587890625) + (x1 - (6.0688)) * ((3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
        + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (3678974749848/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (138237437215656499/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (57424525330749356801/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (284589186783466939117311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3678974749848/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (138237437215656499/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (57424525330749356801/19073486328125000) := by norm_num
  have hb3 : (0:ℝ) ≤ (284589186783466939117311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3678974749848/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (138237437215656499/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (57424525330749356801/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (284589186783466939117311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1523145779643468/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,hi,lo)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hhhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (8) (8) (6.3504) (4) - (64/25) * (deltaX4 x1 (6.3504) (8) (8) (6.3504) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (8) (8) (6.3504) (4) - (64/25) * (deltaX4 x1 (6.3504) (8) (8) (6.3504) (4)) ^ 2
      = (40779805387254876/3814697265625) + (x1 - (6.0688)) * ((17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
        + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (17261477575824/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (128993411204816957/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (159789100090924215403/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (262232654634969801617311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (17261477575824/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (128993411204816957/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (159789100090924215403/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (262232654634969801617311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (17261477575824/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (128993411204816957/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (159789100090924215403/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (262232654634969801617311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (40779805387254876/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,hi,hi)` of debt `1100` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_1100_hhhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (8) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (8) (8) (6.3504) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (8) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (8) (8) (6.3504) (6.3504)) ^ 2
      = (47838630676967644/3814697265625) + (x1 - (6.0688)) * ((24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
        + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
      + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (24187640849724/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (46005304073526208/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (232636461534813081419/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (390766981201052412947311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (24187640849724/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (46005304073526208/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (232636461534813081419/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (390766981201052412947311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (24187640849724/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (46005304073526208/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (232636461534813081419/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (390766981201052412947311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
      + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
      + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (47838630676967644/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,lo,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lllll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (6.0688) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (6.0688) (4)) ^ 2
      = (18636705534966844/3814697265625) + (x1 - (6.0688)) * ((4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
        + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
      + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (4629554551524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (31015561822012057/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (265246118532364905127/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (22026869825459957653343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (4629554551524/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (31015561822012057/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (265246118532364905127/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (22026869825459957653343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (4629554551524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (31015561822012057/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (265246118532364905127/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (22026869825459957653343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
      + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
      + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (18636705534966844/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,lo,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_llllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (6.0688) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (6.0688) (6.3504)) ^ 2
      = (24766388408306844/3814697265625) + (x1 - (6.0688)) * ((1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
        + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (1948081726392/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (35884783429795003/22888183593750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (139739439711815462651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (70052614094782744568343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (1948081726392/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (35884783429795003/22888183593750) := by norm_num
  have hb2 : (0:ℝ) ≤ (139739439711815462651/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (70052614094782744568343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (1948081726392/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (35884783429795003/22888183593750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (139739439711815462651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (70052614094782744568343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (24766388408306844/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,hi,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lllhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.0688) (8) (4) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (8) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.0688) (8) (4) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (8) (4)) ^ 2
      = (19731737815380424/3814697265625) + (x1 - (6.0688)) * ((8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
        + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
      + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (8574199328748/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (15730053917688752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (608875342059929771111/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (60526496222564756398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8574199328748/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (15730053917688752/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (608875342059929771111/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (60526496222564756398343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8574199328748/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (15730053917688752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (608875342059929771111/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (60526496222564756398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
      + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
      + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (19731737815380424/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,hi,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lllhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (8) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (8) (6.3504)) ^ 2
      = (208946833566572/30517578125) + (x1 - (6.0688)) * ((2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
        + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2439562533156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (91840511827285709/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (305731766740332406413/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (94810036854302393313343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2439562533156/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (91840511827285709/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (305731766740332406413/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (94810036854302393313343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2439562533156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (91840511827285709/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (305731766740332406413/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (94810036854302393313343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (208946833566572/30517578125) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,lo,lo)` of debt `0110` (Taylor end = hi);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_llhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (8) (6.0688) (4) - (64/25) * (deltaX4 x1 (4) (4) (8) (6.0688) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (8) (6.0688) (4) - (64/25) * (deltaX4 x1 (4) (4) (8) (6.0688) (4)) ^ 2
      = (726111170992410319620100240119/596046447753906250000000000) + ((7.02674064) - x1) * ((57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
        + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ ((7.02674064) - x1) := by linarith
  have hd2 : ((7.02674064) - x1) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
      + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3)
      = (57653359402382962436439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3
        + 3 * (304881230379406355598067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2
        + 3 * (44654587353140406177563/23841857910156250000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1))
        + (156491412176608718532689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (57653359402382962436439/23841857910156250000) := by norm_num
  have hb1 : (0:ℝ) ≤ (304881230379406355598067/143051147460937500000) := by norm_num
  have hb2 : (0:ℝ) ≤ (44654587353140406177563/23841857910156250000) := by norm_num
  have hb3 : (0:ℝ) ≤ (156491412176608718532689/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - ((7.02674064) - x1) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - ((7.02674064) - x1))]
  have hT2 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 2 := by nlinarith [sq_nonneg (((7.02674064) - x1))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (57653359402382962436439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (304881230379406355598067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (44654587353140406177563/23841857910156250000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (156491412176608718532689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
      + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ ((7.02674064) - x1) * ((57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
      + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (726111170992410319620100240119/596046447753906250000000000) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,lo,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_llhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (4) (4) (8) (6.0688) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (4) (4) (8) (6.0688) (6.3504)) ^ 2
      = (1456556422912/244140625) + (x1 - (6.0688)) * ((5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
        + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (5305644288/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (4705232128227134/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (14712793615458253639/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (7531484459817624047311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (5305644288/9765625) := by norm_num
  have hb1 : (0:ℝ) ≤ (4705232128227134/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (14712793615458253639/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (7531484459817624047311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (5305644288/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (4705232128227134/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (14712793615458253639/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (7531484459817624047311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1456556422912/244140625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,hi,lo)` of debt `0110` (Taylor end = hi);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_llhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (8) (8) (4) - (64/25) * (deltaX4 x1 (4) (4) (8) (8) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (8) (8) (4) - (64/25) * (deltaX4 x1 (4) (4) (8) (8) (4)) ^ 2
      = (2921190917990425673459562700119/596046447753906250000000000) + ((7.02674064) - x1) * ((16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
        + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ ((7.02674064) - x1) := by linarith
  have hd2 : ((7.02674064) - x1) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
      + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3)
      = (16551561326479222131439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3
        + 3 * (69243748144937269378067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2
        + 3 * (21415345170709314792689/71525573730468750000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1))
        + (13165516787084314792689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (16551561326479222131439/23841857910156250000) := by norm_num
  have hb1 : (0:ℝ) ≤ (69243748144937269378067/143051147460937500000) := by norm_num
  have hb2 : (0:ℝ) ≤ (21415345170709314792689/71525573730468750000) := by norm_num
  have hb3 : (0:ℝ) ≤ (13165516787084314792689/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - ((7.02674064) - x1) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - ((7.02674064) - x1))]
  have hT2 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 2 := by nlinarith [sq_nonneg (((7.02674064) - x1))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (16551561326479222131439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (69243748144937269378067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (21415345170709314792689/71525573730468750000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (13165516787084314792689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
      + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ ((7.02674064) - x1) * ((16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
      + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (2921190917990425673459562700119/596046447753906250000000000) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,hi,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_llhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (8) (8) (6.3504) - (64/25) * (deltaX4 x1 (4) (4) (8) (8) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (8) (8) (6.3504) - (64/25) * (deltaX4 x1 (4) (4) (8) (8) (6.3504)) ^ 2
      = (28682420748974064/3814697265625) + (x1 - (6.0688)) * ((8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
        + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (8945941852368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (5288499003125384/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (24569353388853888129/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (111468604129859227787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8945941852368/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (5288499003125384/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (24569353388853888129/19073486328125000) := by norm_num
  have hb3 : (0:ℝ) ≤ (111468604129859227787311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8945941852368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (5288499003125384/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (24569353388853888129/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (111468604129859227787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (28682420748974064/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,lo,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lhlll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (6.0688) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (6.0688) (4)) ^ 2
      = (23721919240194396/3814697265625) + (x1 - (6.0688)) * ((1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
        + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (1921178384004/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (70840295902266557/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (138040106561621666651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (69250465977209466443343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (1921178384004/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (70840295902266557/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (138040106561621666651/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (69250465977209466443343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (1921178384004/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (70840295902266557/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (138040106561621666651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (69250465977209466443343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (23721919240194396/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,lo,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lhllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (6.0688) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (6.0688) (6.3504)) ^ 2
      = (1009646443479024/152587890625) + (x1 - (6.0688)) * ((2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
        + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2852000121408/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (108491710261323731/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1095855703770605241383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (114717261148279831483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2852000121408/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (108491710261323731/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1095855703770605241383/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (114717261148279831483343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2852000121408/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (108491710261323731/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1095855703770605241383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (114717261148279831483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1009646443479024/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,hi,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lhlhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (8) (4) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (8) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (8) (4) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (8) (4)) ^ 2
      = (178908270289772/30517578125) + (x1 - (6.0688)) * ((2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
        + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2274067931156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (28596126123684403/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (858213106846347219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (88826385584825830813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2274067931156/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (28596126123684403/15258789062500) := by norm_num
  have hb2 : (0:ℝ) ≤ (858213106846347219239/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (88826385584825830813343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2274067931156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (28596126123684403/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (858213106846347219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (88826385584825830813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (178908270289772/30517578125) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,hi,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lhlhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (8) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (8) (6.3504)) ^ 2
      = (25617415498476544/3814697265625) + (x1 - (6.0688)) * ((14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
        + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14797673492096/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (22711915608862627/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1158272097895699167367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (122585866905029795853343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14797673492096/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (22711915608862627/9155273437500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1158272097895699167367/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (122585866905029795853343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14797673492096/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (22711915608862627/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1158272097895699167367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (122585866905029795853343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (25617415498476544/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,lo,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lhhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (8) (6.0688) (4) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (6.0688) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (8) (6.0688) (4) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (6.0688) (4)) ^ 2
      = (24809936090203804/3814697265625) + (x1 - (6.0688)) * ((3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
        + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (3997675257624/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24012889727315087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (21302250611249631139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (18679755249108567797311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3997675257624/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (24012889727315087/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (21302250611249631139/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (18679755249108567797311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3997675257624/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24012889727315087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (21302250611249631139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (18679755249108567797311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (24809936090203804/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,lo,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lhhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (6.0688) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (6.0688) (6.3504)) ^ 2
      = (35831790122294524/3814697265625) + (x1 - (6.0688)) * ((2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
        + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2710258910444/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24838857216231796/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (24060809396384810431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (192073168970467566627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2710258910444/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (24838857216231796/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (24060809396384810431/11444091796875000) := by norm_num
  have hb3 : (0:ℝ) ≤ (192073168970467566627311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2710258910444/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24838857216231796/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (24060809396384810431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (192073168970467566627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (35831790122294524/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,hi,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lhhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (8) (8) (4) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (8) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (8) (8) (4) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (8) (4)) ^ 2
      = (30913120738284064/3814697265625) + (x1 - (6.0688)) * ((9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
        + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (9696512712368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (17311295901568027/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (81129447275980414387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (124158237059656102787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (9696512712368/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (17311295901568027/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (81129447275980414387/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (124158237059656102787311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (9696512712368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (17311295901568027/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (81129447275980414387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (124158237059656102787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (30913120738284064/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,hi,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_lhhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (8) (8) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (8) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (8) (8) (6.3504) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (8) (6.3504)) ^ 2
      = (40779805387254876/3814697265625) + (x1 - (6.0688)) * ((17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
        + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (17261477575824/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (128993411204816957/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (159789100090924215403/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (262232654634969801617311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (17261477575824/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (128993411204816957/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (159789100090924215403/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (262232654634969801617311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (17261477575824/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (128993411204816957/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (159789100090924215403/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (262232654634969801617311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (40779805387254876/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,lo,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hllll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (6.0688) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (6.0688) (4)) ^ 2
      = (21219272815193856/3814697265625) + (x1 - (6.0688)) * ((2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
        + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2274006488256/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (85003858289227583/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (168232248290565770651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (85946902791775172693343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2274006488256/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (85003858289227583/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (168232248290565770651/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (85946902791775172693343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2274006488256/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (85003858289227583/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (168232248290565770651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (85946902791775172693343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (21219272815193856/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,lo,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hlllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (6.0688) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (6.0688) (6.3504)) ^ 2
      = (25883117520063856/3814697265625) + (x1 - (6.0688)) * ((14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
        + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14106464769728/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (35737753568836433/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1081801900472716601383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (113121103747484731483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14106464769728/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (35737753568836433/15258789062500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1081801900472716601383/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (113121103747484731483343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14106464769728/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (35737753568836433/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1081801900472716601383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (113121103747484731483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (25883117520063856/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,hi,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hllhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (8) (4) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (8) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (8) (4) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (8) (4)) ^ 2
      = (106196226552972/30517578125) + (x1 - (6.0688)) * ((2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
        + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2754125379156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (105593526633758209/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1074294529100447219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (113212985780778955813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2754125379156/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (105593526633758209/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1074294529100447219239/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (113212985780778955813343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2754125379156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (105593526633758209/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1074294529100447219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (113212985780778955813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (106196226552972/30517578125) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,hi,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hllhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (8) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (8) (6.3504)) ^ 2
      = (20447825989797884/3814697265625) + (x1 - (6.0688)) * ((15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
        + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (15280284373524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (117922714365242677/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1209339008207190007367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (128679872885622114603343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (15280284373524/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (117922714365242677/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1209339008207190007367/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (128679872885622114603343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (15280284373524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (117922714365242677/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1209339008207190007367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (128679872885622114603343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (20447825989797884/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,lo,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hlhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (8) (6.0688) (4) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (6.0688) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (8) (6.0688) (4) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (6.0688) (4)) ^ 2
      = (25403000815519516/3814697265625) + (x1 - (6.0688)) * ((6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
        + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (6577980068448/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (44297684286006113/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (47823879406502196139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (64825195902677480297311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (6577980068448/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (44297684286006113/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (47823879406502196139/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (64825195902677480297311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (6577980068448/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (44297684286006113/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (47823879406502196139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (64825195902677480297311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (25403000815519516/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,lo,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hlhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (6.0688) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (6.0688) (6.3504)) ^ 2
      = (36052365919299516/3814697265625) + (x1 - (6.0688)) * ((2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
        + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2657332885292/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24310943036688188/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (7833720841032531477/3814697265625000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (187145005911877366627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2657332885292/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (24310943036688188/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (7833720841032531477/3814697265625000) := by norm_num
  have hb3 : (0:ℝ) ≤ (187145005911877366627311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2657332885292/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24310943036688188/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (7833720841032531477/3814697265625000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (187145005911877366627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (36052365919299516/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,hi,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hlhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (8) (8) (4) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (8) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (8) (8) (4) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (8) (4)) ^ 2
      = (27809635670094064/3814697265625) + (x1 - (6.0688)) * ((13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
        + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (13674843822368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (25221415223494277/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (122933786338992914387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (197588372920312352787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (13674843822368/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (25221415223494277/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (122933786338992914387/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (197588372920312352787311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (13674843822368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (25221415223494277/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (122933786338992914387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (197588372920312352787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (27809635670094064/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,hi,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hlhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (8) (8) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (8) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (8) (8) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (8) (6.3504)) ^ 2
      = (1523145779643468/152587890625) + (x1 - (6.0688)) * ((3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
        + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (3678974749848/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (138237437215656499/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (57424525330749356801/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (284589186783466939117311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3678974749848/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (138237437215656499/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (57424525330749356801/19073486328125000) := by norm_num
  have hb3 : (0:ℝ) ≤ (284589186783466939117311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3678974749848/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (138237437215656499/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (57424525330749356801/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (284589186783466939117311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1523145779643468/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,lo,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hhlll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (6.0688) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (6.0688) (4)) ^ 2
      = (26236834304961904/3814697265625) + (x1 - (6.0688)) * ((14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
        + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14173389401216/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (107704359888708067/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (362201512251697320461/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (113610091324855881483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14173389401216/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (107704359888708067/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (362201512251697320461/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (113610091324855881483343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14173389401216/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (107704359888708067/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (362201512251697320461/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (113610091324855881483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (26236834304961904/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,lo,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hhllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (6.0688) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (6.0688) (6.3504)) ^ 2
      = (27039395629082824/3814697265625) + (x1 - (6.0688)) * ((16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
        + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
      + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (16770080807148/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (32297176289804752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1323224622028264209511/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (140701940611219268398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (16770080807148/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (32297176289804752/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (1323224622028264209511/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (140701940611219268398343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (16770080807148/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (32297176289804752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1323224622028264209511/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (140701940611219268398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
      + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
      + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (27039395629082824/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,hi,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hhlhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (8) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (8) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (8) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (8) (4)) ^ 2
      = (17316378432875836/3814697265625) + (x1 - (6.0688)) * ((14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
        + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14654252706952/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (18881825174755399/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (387885372288628115789/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (123987357311089980228343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14654252706952/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (18881825174755399/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (387885372288628115789/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (123987357311089980228343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14654252706952/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (18881825174755399/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (387885372288628115789/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (123987357311089980228343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (17316378432875836/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,hi,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hhlhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (8) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (8) (6.3504)) ^ 2
      = (21126580626452576/3814697265625) + (x1 - (6.0688)) * ((3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
        + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
      + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (3256927030976/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (126848575828496087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (262842992835682327099/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (141406782533305717143343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3256927030976/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (126848575828496087/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (262842992835682327099/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (141406782533305717143343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3256927030976/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (126848575828496087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (262842992835682327099/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (141406782533305717143343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
      + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
      + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (21126580626452576/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,lo,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hhhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (6.0688) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (6.0688) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (6.0688) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (6.0688) (4)) ^ 2
      = (1439388082724572/152587890625) + (x1 - (6.0688)) * ((105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
        + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (105939958156/48828125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (1615027736093192/762939453125) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (23412926639316978431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (186387132809619666627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (105939958156/48828125) := by norm_num
  have hb1 : (0:ℝ) ≤ (1615027736093192/762939453125) := by norm_num
  have hb2 : (0:ℝ) ≤ (23412926639316978431/11444091796875000) := by norm_num
  have hb3 : (0:ℝ) ≤ (186387132809619666627311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (105939958156/48828125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (1615027736093192/762939453125) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (23412926639316978431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (186387132809619666627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1439388082724572/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,lo,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hhhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (6.0688) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (6.0688) (6.3504)) ^ 2
      = (46289875577544736/3814697265625) + (x1 - (6.0688)) * ((20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
        + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
      + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (20738696783008/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (39019283553664346/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (194937043856093730671/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (323030654761564709207311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (20738696783008/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (39019283553664346/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (194937043856093730671/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (323030654761564709207311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (20738696783008/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (39019283553664346/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (194937043856093730671/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (323030654761564709207311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
      + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
      + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (46289875577544736/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,hi,lo)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hhhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (8) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (8) (4)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (8) (4) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (8) (4)) ^ 2
      = (37415625546675136/3814697265625) + (x1 - (6.0688)) * ((18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
        + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (18419627374656/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (11540546965738018/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (172664326686972362903/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (285372675821715170367311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (18419627374656/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (11540546965738018/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (172664326686972362903/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (285372675821715170367311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (18419627374656/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (11540546965738018/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (172664326686972362903/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (285372675821715170367311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (37415625546675136/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,hi,hi)` of debt `0110` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0110_hhhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (8) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (8) (6.3504)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (8) (6.3504) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (8) (6.3504)) ^ 2
      = (47838630676967644/3814697265625) + (x1 - (6.0688)) * ((24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
        + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
      + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (24187640849724/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (46005304073526208/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (232636461534813081419/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (390766981201052412947311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (24187640849724/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (46005304073526208/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (232636461534813081419/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (390766981201052412947311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (24187640849724/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (46005304073526208/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (232636461534813081419/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (390766981201052412947311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
      + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
      + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (47838630676967644/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,lo,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lllll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (4) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (4) (6.0688)) ^ 2
      = (18636705534966844/3814697265625) + (x1 - (6.0688)) * ((4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
        + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
      + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (4629554551524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (31015561822012057/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (265246118532364905127/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (22026869825459957653343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (4629554551524/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (31015561822012057/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (265246118532364905127/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (22026869825459957653343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (4629554551524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (31015561822012057/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (265246118532364905127/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (22026869825459957653343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
      + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((4629554551524/6103515625) + (-2476043068/9765625) * (x1 - (6.0688))
      + (-875812/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (18636705534966844/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,lo,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_llllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.0688) (4) (8) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (4) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.0688) (4) (8) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (4) (8)) ^ 2
      = (19731737815380424/3814697265625) + (x1 - (6.0688)) * ((8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
        + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
      + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (8574199328748/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (15730053917688752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (608875342059929771111/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (60526496222564756398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8574199328748/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (15730053917688752/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (608875342059929771111/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (60526496222564756398343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8574199328748/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (15730053917688752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (608875342059929771111/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (60526496222564756398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
      + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8574199328748/6103515625) + (-926172992/9765625) * (x1 - (6.0688))
      + (-721316/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (19731737815380424/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,hi,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lllhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (6.3504) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (6.3504) (6.0688)) ^ 2
      = (24766388408306844/3814697265625) + (x1 - (6.0688)) * ((1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
        + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (1948081726392/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (35884783429795003/22888183593750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (139739439711815462651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (70052614094782744568343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (1948081726392/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (35884783429795003/22888183593750) := by norm_num
  have hb2 : (0:ℝ) ≤ (139739439711815462651/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (70052614094782744568343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (1948081726392/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (35884783429795003/22888183593750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (139739439711815462651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (70052614094782744568343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((1948081726392/1220703125) + (-857504744/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (24766388408306844/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,hi,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lllhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (6.3504) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 x1 (4) (4) (6.0688) (6.3504) (8)) ^ 2
      = (208946833566572/30517578125) + (x1 - (6.0688)) * ((2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
        + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2439562533156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (91840511827285709/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (305731766740332406413/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (94810036854302393313343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2439562533156/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (91840511827285709/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (305731766740332406413/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (94810036854302393313343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2439562533156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (91840511827285709/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (305731766740332406413/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (94810036854302393313343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2439562533156/1220703125) + (238456084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (208946833566572/30517578125) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,lo,lo)` of debt `0101` (Taylor end = hi);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_llhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (8) (4) (6.0688) - (64/25) * (deltaX4 x1 (4) (4) (8) (4) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (8) (4) (6.0688) - (64/25) * (deltaX4 x1 (4) (4) (8) (4) (6.0688)) ^ 2
      = (726111170992410319620100240119/596046447753906250000000000) + ((7.02674064) - x1) * ((57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
        + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ ((7.02674064) - x1) := by linarith
  have hd2 : ((7.02674064) - x1) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
      + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3)
      = (57653359402382962436439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3
        + 3 * (304881230379406355598067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2
        + 3 * (44654587353140406177563/23841857910156250000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1))
        + (156491412176608718532689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (57653359402382962436439/23841857910156250000) := by norm_num
  have hb1 : (0:ℝ) ≤ (304881230379406355598067/143051147460937500000) := by norm_num
  have hb2 : (0:ℝ) ≤ (44654587353140406177563/23841857910156250000) := by norm_num
  have hb3 : (0:ℝ) ≤ (156491412176608718532689/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - ((7.02674064) - x1) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - ((7.02674064) - x1))]
  have hT2 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 2 := by nlinarith [sq_nonneg (((7.02674064) - x1))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (57653359402382962436439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (304881230379406355598067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (44654587353140406177563/23841857910156250000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (156491412176608718532689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
      + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ ((7.02674064) - x1) * ((57653359402382962436439/23841857910156250000) + (-6854525104585423/7629394531250) * ((7.02674064) - x1)
      + (911734064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (726111170992410319620100240119/596046447753906250000000000) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,lo,hi)` of debt `0101` (Taylor end = hi);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_llhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (8) (4) (8) - (64/25) * (deltaX4 x1 (4) (4) (8) (4) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (8) (4) (8) - (64/25) * (deltaX4 x1 (4) (4) (8) (4) (8)) ^ 2
      = (2921190917990425673459562700119/596046447753906250000000000) + ((7.02674064) - x1) * ((16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
        + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ ((7.02674064) - x1) := by linarith
  have hd2 : ((7.02674064) - x1) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
      + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3)
      = (16551561326479222131439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3
        + 3 * (69243748144937269378067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2
        + 3 * (21415345170709314792689/71525573730468750000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1))
        + (13165516787084314792689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (16551561326479222131439/23841857910156250000) := by norm_num
  have hb1 : (0:ℝ) ≤ (69243748144937269378067/143051147460937500000) := by norm_num
  have hb2 : (0:ℝ) ≤ (21415345170709314792689/71525573730468750000) := by norm_num
  have hb3 : (0:ℝ) ≤ (13165516787084314792689/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - ((7.02674064) - x1) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - ((7.02674064) - x1))]
  have hT2 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 2 := by nlinarith [sq_nonneg (((7.02674064) - x1))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ ((7.02674064) - x1) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (16551561326479222131439/23841857910156250000) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (69243748144937269378067/143051147460937500000) * ((7.02674064) - x1) * ((5987129/6250000) - ((7.02674064) - x1)) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (21415345170709314792689/71525573730468750000) * ((7.02674064) - x1) ^ 2 * ((5987129/6250000) - ((7.02674064) - x1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (13165516787084314792689/95367431640625000000) * ((7.02674064) - x1) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
      + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ ((7.02674064) - x1) * ((16551561326479222131439/23841857910156250000) + (-5021709038495423/7629394531250) * ((7.02674064) - x1)
      + (815174064/9765625) * ((7.02674064) - x1) ^ 2 + (-64/25) * ((7.02674064) - x1) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (2921190917990425673459562700119/596046447753906250000000000) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,hi,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_llhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (4) (4) (8) (6.3504) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (4) (4) (8) (6.3504) (6.0688)) ^ 2
      = (1456556422912/244140625) + (x1 - (6.0688)) * ((5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
        + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (5305644288/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (4705232128227134/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (14712793615458253639/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (7531484459817624047311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (5305644288/9765625) := by norm_num
  have hb1 : (0:ℝ) ≤ (4705232128227134/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (14712793615458253639/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (7531484459817624047311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (5305644288/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (4705232128227134/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (14712793615458253639/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (7531484459817624047311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((5305644288/9765625) + (-4041522464/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1456556422912/244140625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,hi,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_llhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (8) (6.3504) (8) - (64/25) * (deltaX4 x1 (4) (4) (8) (6.3504) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (8) (6.3504) (8) - (64/25) * (deltaX4 x1 (4) (4) (8) (6.3504) (8)) ^ 2
      = (28682420748974064/3814697265625) + (x1 - (6.0688)) * ((8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
        + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (8945941852368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (5288499003125384/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (24569353388853888129/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (111468604129859227787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8945941852368/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (5288499003125384/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (24569353388853888129/19073486328125000) := by norm_num
  have hb3 : (0:ℝ) ≤ (111468604129859227787311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8945941852368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (5288499003125384/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (24569353388853888129/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (111468604129859227787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8945941852368/6103515625) + (-2426923392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (28682420748974064/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,lo,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lhlll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (4) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (4) (6.0688)) ^ 2
      = (21219272815193856/3814697265625) + (x1 - (6.0688)) * ((2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
        + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2274006488256/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (85003858289227583/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (168232248290565770651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (85946902791775172693343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2274006488256/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (85003858289227583/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (168232248290565770651/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (85946902791775172693343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2274006488256/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (85003858289227583/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (168232248290565770651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (85946902791775172693343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2274006488256/1220703125) + (-181312292/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (21219272815193856/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,lo,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lhllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (4) (8) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (4) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (4) (8) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (4) (8)) ^ 2
      = (106196226552972/30517578125) + (x1 - (6.0688)) * ((2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
        + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2754125379156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (105593526633758209/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1074294529100447219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (113212985780778955813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2754125379156/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (105593526633758209/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1074294529100447219239/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (113212985780778955813343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2754125379156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (105593526633758209/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1074294529100447219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (113212985780778955813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2754125379156/1220703125) + (1545866084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (106196226552972/30517578125) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,hi,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lhlhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (6.3504) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (6.3504) (6.0688)) ^ 2
      = (25883117520063856/3814697265625) + (x1 - (6.0688)) * ((14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
        + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14106464769728/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (35737753568836433/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1081801900472716601383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (113121103747484731483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14106464769728/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (35737753568836433/15258789062500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1081801900472716601383/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (113121103747484731483343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14106464769728/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (35737753568836433/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1081801900472716601383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (113121103747484731483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14106464769728/6103515625) + (945210924/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (25883117520063856/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,hi,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lhlhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (6.3504) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 x1 (4) (6.3504) (6.0688) (6.3504) (8)) ^ 2
      = (20447825989797884/3814697265625) + (x1 - (6.0688)) * ((15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
        + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (15280284373524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (117922714365242677/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1209339008207190007367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (128679872885622114603343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (15280284373524/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (117922714365242677/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1209339008207190007367/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (128679872885622114603343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (15280284373524/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (117922714365242677/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1209339008207190007367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (128679872885622114603343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((15280284373524/6103515625) + (2218480052/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (20447825989797884/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,lo,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lhhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (8) (4) (6.0688) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (4) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (8) (4) (6.0688) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (4) (6.0688)) ^ 2
      = (25403000815519516/3814697265625) + (x1 - (6.0688)) * ((6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
        + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (6577980068448/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (44297684286006113/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (47823879406502196139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (64825195902677480297311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (6577980068448/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (44297684286006113/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (47823879406502196139/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (64825195902677480297311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (6577980068448/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (44297684286006113/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (47823879406502196139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (64825195902677480297311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((6577980068448/6103515625) + (-3365330012/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (25403000815519516/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,lo,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lhhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (8) (4) (8) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (4) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (8) (4) (8) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (4) (8)) ^ 2
      = (27809635670094064/3814697265625) + (x1 - (6.0688)) * ((13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
        + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (13674843822368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (25221415223494277/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (122933786338992914387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (197588372920312352787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (13674843822368/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (25221415223494277/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (122933786338992914387/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (197588372920312352787311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (13674843822368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (25221415223494277/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (122933786338992914387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (197588372920312352787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((13674843822368/6103515625) + (-1119513392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (27809635670094064/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,hi,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lhhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (6.3504) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (6.3504) (6.0688)) ^ 2
      = (36052365919299516/3814697265625) + (x1 - (6.0688)) * ((2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
        + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2657332885292/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24310943036688188/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (7833720841032531477/3814697265625000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (187145005911877366627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2657332885292/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (24310943036688188/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (7833720841032531477/3814697265625000) := by norm_num
  have hb3 : (0:ℝ) ≤ (187145005911877366627311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2657332885292/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24310943036688188/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (7833720841032531477/3814697265625000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (187145005911877366627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2657332885292/1220703125) + (-1607589248/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (36052365919299516/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,hi,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_lhhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (8) (6.3504) (8) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (6.3504) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (8) (6.3504) (8) - (64/25) * (deltaX4 x1 (4) (6.3504) (8) (6.3504) (8)) ^ 2
      = (1523145779643468/152587890625) + (x1 - (6.0688)) * ((3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
        + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (3678974749848/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (138237437215656499/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (57424525330749356801/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (284589186783466939117311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3678974749848/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (138237437215656499/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (57424525330749356801/19073486328125000) := by norm_num
  have hb3 : (0:ℝ) ≤ (284589186783466939117311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3678974749848/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (138237437215656499/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (57424525330749356801/19073486328125000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (284589186783466939117311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3678974749848/1220703125) + (184318124/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1523145779643468/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,lo,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hllll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (4) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (4) (6.0688)) ^ 2
      = (23721919240194396/3814697265625) + (x1 - (6.0688)) * ((1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
        + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (1921178384004/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (70840295902266557/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (138040106561621666651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (69250465977209466443343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (1921178384004/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (70840295902266557/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (138040106561621666651/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (69250465977209466443343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (1921178384004/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (70840295902266557/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (138040106561621666651/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (69250465977209466443343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((1921178384004/1220703125) + (-804321068/9765625) * (x1 - (6.0688))
      + (-137556/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (23721919240194396/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,lo,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hlllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (4) (8) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (4) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (4) (8) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (4) (8)) ^ 2
      = (178908270289772/30517578125) + (x1 - (6.0688)) * ((2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
        + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2274067931156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (28596126123684403/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (858213106846347219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (88826385584825830813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2274067931156/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (28596126123684403/15258789062500) := by norm_num
  have hb2 : (0:ℝ) ≤ (858213106846347219239/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (88826385584825830813343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2274067931156/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (28596126123684403/15258789062500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (858213106846347219239/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (88826385584825830813343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2274067931156/1220703125) + (341286084/9765625) * (x1 - (6.0688))
      + (-533284/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (178908270289772/30517578125) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,hi,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hllhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (6.3504) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (6.3504) (6.0688)) ^ 2
      = (1009646443479024/152587890625) + (x1 - (6.0688)) * ((2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
        + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2852000121408/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (108491710261323731/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1095855703770605241383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (114717261148279831483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2852000121408/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (108491710261323731/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1095855703770605241383/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (114717261148279831483343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2852000121408/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (108491710261323731/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1095855703770605241383/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (114717261148279831483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2852000121408/1220703125) + (1030013356/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1009646443479024/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,hi,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hllhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (6.3504) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 x1 (6.3504) (4) (6.0688) (6.3504) (8)) ^ 2
      = (25617415498476544/3814697265625) + (x1 - (6.0688)) * ((14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
        + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14797673492096/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (22711915608862627/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1158272097895699167367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (122585866905029795853343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14797673492096/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (22711915608862627/9155273437500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1158272097895699167367/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (122585866905029795853343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14797673492096/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (22711915608862627/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1158272097895699167367/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (122585866905029795853343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14797673492096/6103515625) + (344342252/1953125) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (25617415498476544/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,lo,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hlhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (8) (4) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (4) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (8) (4) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (4) (6.0688)) ^ 2
      = (24809936090203804/3814697265625) + (x1 - (6.0688)) * ((3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
        + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (3997675257624/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24012889727315087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (21302250611249631139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (18679755249108567797311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3997675257624/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (24012889727315087/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (21302250611249631139/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (18679755249108567797311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3997675257624/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24012889727315087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (21302250611249631139/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (18679755249108567797311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3997675257624/6103515625) + (-3988338788/9765625) * (x1 - (6.0688))
      + (-1117472/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (24809936090203804/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,lo,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hlhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (8) (4) (8) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (4) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (8) (4) (8) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (4) (8)) ^ 2
      = (30913120738284064/3814697265625) + (x1 - (6.0688)) * ((9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
        + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (9696512712368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (17311295901568027/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (81129447275980414387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (124158237059656102787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (9696512712368/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (17311295901568027/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (81129447275980414387/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (124158237059656102787311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (9696512712368/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (17311295901568027/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (81129447275980414387/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (124158237059656102787311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((9696512712368/6103515625) + (-2324093392/9765625) * (x1 - (6.0688))
      + (-962976/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (30913120738284064/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,hi,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hlhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (6.3504) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (6.3504) (6.0688)) ^ 2
      = (35831790122294524/3814697265625) + (x1 - (6.0688)) * ((2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
        + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (2710258910444/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24838857216231796/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (24060809396384810431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (192073168970467566627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (2710258910444/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (24838857216231796/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (24060809396384810431/11444091796875000) := by norm_num
  have hb3 : (0:ℝ) ≤ (192073168970467566627311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (2710258910444/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24838857216231796/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (24060809396384810431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (192073168970467566627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((2710258910444/1220703125) + (-1522786816/9765625) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (35831790122294524/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,hi,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hlhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (8) (6.3504) (8) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (6.3504) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (8) (6.3504) (8) - (64/25) * (deltaX4 x1 (6.3504) (4) (8) (6.3504) (8)) ^ 2
      = (40779805387254876/3814697265625) + (x1 - (6.0688)) * ((17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
        + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (17261477575824/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (128993411204816957/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (159789100090924215403/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (262232654634969801617311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (17261477575824/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (128993411204816957/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (159789100090924215403/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (262232654634969801617311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (17261477575824/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (128993411204816957/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (159789100090924215403/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (262232654634969801617311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((17261477575824/6103515625) + (-312450668/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (40779805387254876/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,lo,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hhlll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (4) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (4) (6.0688)) ^ 2
      = (26236834304961904/3814697265625) + (x1 - (6.0688)) * ((14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
        + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14173389401216/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (107704359888708067/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (362201512251697320461/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (113610091324855881483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14173389401216/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (107704359888708067/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (362201512251697320461/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (113610091324855881483343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14173389401216/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (107704359888708067/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (362201512251697320461/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (113610091324855881483343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14173389401216/6103515625) + (937971692/9765625) * (x1 - (6.0688))
      + (-499748/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (26236834304961904/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,lo,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hhllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (4) (8) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (4) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (4) (8) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (4) (8)) ^ 2
      = (17316378432875836/3814697265625) + (x1 - (6.0688)) * ((14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
        + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (14654252706952/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (18881825174755399/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (387885372288628115789/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (123987357311089980228343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (14654252706952/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (18881825174755399/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (387885372288628115789/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (123987357311089980228343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (14654252706952/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (18881825174755399/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (387885372288628115789/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (123987357311089980228343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((14654252706952/6103515625) + (2260887144/9765625) * (x1 - (6.0688))
      + (-345252/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (17316378432875836/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,hi,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hhlhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (6.3504) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (6.3504) (6.0688)) ^ 2
      = (27039395629082824/3814697265625) + (x1 - (6.0688)) * ((16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
        + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
      + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (16770080807148/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (32297176289804752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1323224622028264209511/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (140701940611219268398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (16770080807148/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (32297176289804752/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (1323224622028264209511/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (140701940611219268398343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (16770080807148/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (32297176289804752/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1323224622028264209511/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (140701940611219268398343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
      + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((16770080807148/6103515625) + (2280291008/9765625) * (x1 - (6.0688))
      + (-311716/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (27039395629082824/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,hi,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hhlhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (6.3504) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (6.0688) (6.3504) (8)) ^ 2
      = (21126580626452576/3814697265625) + (x1 - (6.0688)) * ((3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
        + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
      + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (3256927030976/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (126848575828496087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (262842992835682327099/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (141406782533305717143343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3256927030976/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (126848575828496087/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (262842992835682327099/91552734375000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (141406782533305717143343/47683715820312500000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3256927030976/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (126848575828496087/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (262842992835682327099/91552734375000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (141406782533305717143343/47683715820312500000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
      + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3256927030976/1220703125) + (3149297212/9765625) * (x1 - (6.0688))
      + (-31444/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (21126580626452576/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,lo,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hhhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (4) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (4) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (4) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (4) (6.0688)) ^ 2
      = (1439388082724572/152587890625) + (x1 - (6.0688)) * ((105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
        + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (105939958156/48828125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (1615027736093192/762939453125) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (23412926639316978431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (186387132809619666627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (105939958156/48828125) := by norm_num
  have hb1 : (0:ℝ) ≤ (1615027736093192/762939453125) := by norm_num
  have hb2 : (0:ℝ) ≤ (23412926639316978431/11444091796875000) := by norm_num
  have hb3 : (0:ℝ) ≤ (186387132809619666627311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (105939958156/48828125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (1615027736093192/762939453125) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (23412926639316978431/11444091796875000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (186387132809619666627311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((105939958156/48828125) + (-322965696/1953125) * (x1 - (6.0688))
      + (-185888/3125) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1439388082724572/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,lo,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hhhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (4) (8) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (4) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (4) (8) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (4) (8)) ^ 2
      = (37415625546675136/3814697265625) + (x1 - (6.0688)) * ((18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
        + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (18419627374656/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (11540546965738018/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (172664326686972362903/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (285372675821715170367311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (18419627374656/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (11540546965738018/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (172664326686972362903/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (285372675821715170367311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (18419627374656/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (11540546965738018/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (172664326686972362903/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (285372675821715170367311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((18419627374656/6103515625) + (226725216/9765625) * (x1 - (6.0688))
      + (-774944/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (37415625546675136/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,hi,lo)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hhhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (6.3504) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (6.3504) (6.0688)) ^ 2
      = (46289875577544736/3814697265625) + (x1 - (6.0688)) * ((20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
        + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
      + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (20738696783008/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (39019283553664346/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (194937043856093730671/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (323030654761564709207311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (20738696783008/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (39019283553664346/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (194937043856093730671/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (323030654761564709207311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (20738696783008/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (39019283553664346/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (194937043856093730671/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (323030654761564709207311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
      + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((20738696783008/6103515625) + (358708384/9765625) * (x1 - (6.0688))
      + (-741408/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (46289875577544736/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,hi,hi)` of debt `0101` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0101_hhhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (6.3504) (8) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (6.3504) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (8) (6.3504) (8) - (64/25) * (deltaX4 x1 (6.3504) (6.3504) (8) (6.3504) (8)) ^ 2
      = (47838630676967644/3814697265625) + (x1 - (6.0688)) * ((24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
        + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
      + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3)
      = (24187640849724/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (46005304073526208/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (232636461534813081419/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (390766981201052412947311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (24187640849724/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (46005304073526208/11444091796875) := by norm_num
  have hb2 : (0:ℝ) ≤ (232636461534813081419/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (390766981201052412947311/95367431640625000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (24187640849724/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (46005304073526208/11444091796875) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (232636461534813081419/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (390766981201052412947311/95367431640625000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
      + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((24187640849724/6103515625) + (1746352832/9765625) * (x1 - (6.0688))
      + (-586912/15625) * (x1 - (6.0688)) ^ 2 + (-64/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (47838630676967644/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,lo,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lllll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (4) (4) (4) (6.0688) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (4) (4) (4) (6.0688) (6.0688)) ^ 2
      = (38985255104/9765625) + (x1 - (6.0688)) * ((811008/625) + (947568/15625) * (x1 - (6.0688))
        + (-16) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((811008/625) + (947568/15625) * (x1 - (6.0688))
      + (-16) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (811008/625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (8038191913589/6103515625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (9751814878950959/7324218750000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2044308847946441727670799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (811008/625) := by norm_num
  have hb1 : (0:ℝ) ≤ (8038191913589/6103515625) := by norm_num
  have hb2 : (0:ℝ) ≤ (9751814878950959/7324218750000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2044308847946441727670799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (811008/625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (8038191913589/6103515625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (9751814878950959/7324218750000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2044308847946441727670799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (811008/625) + (947568/15625) * (x1 - (6.0688))
      + (-16) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((811008/625) + (947568/15625) * (x1 - (6.0688))
      + (-16) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (38985255104/9765625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,lo,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_llllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (4) (6.0688) (8) - (36/25) * (deltaX4 x1 (4) (4) (4) (6.0688) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (4) (6.0688) (8) - (36/25) * (deltaX4 x1 (4) (4) (4) (6.0688) (8)) ^ 2
      = (871568042288/244140625) + (x1 - (6.0688)) * ((12939973312/9765625) + (1058793436/9765625) * (x1 - (6.0688))
        + (-163096/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((12939973312/9765625) + (1058793436/9765625) * (x1 - (6.0688))
      + (-163096/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (12939973312/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (62240908121421311/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (106132556716590949311/76293945312500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2163801904647168211330799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (12939973312/9765625) := by norm_num
  have hb1 : (0:ℝ) ≤ (62240908121421311/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (106132556716590949311/76293945312500000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2163801904647168211330799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (12939973312/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (62240908121421311/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (106132556716590949311/76293945312500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2163801904647168211330799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (12939973312/9765625) + (1058793436/9765625) * (x1 - (6.0688))
      + (-163096/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((12939973312/9765625) + (1058793436/9765625) * (x1 - (6.0688))
      + (-163096/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (871568042288/244140625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,hi,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lllhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (4) (8) (6.0688) - (36/25) * (deltaX4 x1 (4) (4) (4) (8) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (4) (8) (6.0688) - (36/25) * (deltaX4 x1 (4) (4) (4) (8) (6.0688)) ^ 2
      = (871568042288/244140625) + (x1 - (6.0688)) * ((12939973312/9765625) + (1058793436/9765625) * (x1 - (6.0688))
        + (-163096/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((12939973312/9765625) + (1058793436/9765625) * (x1 - (6.0688))
      + (-163096/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (12939973312/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (62240908121421311/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (106132556716590949311/76293945312500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2163801904647168211330799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (12939973312/9765625) := by norm_num
  have hb1 : (0:ℝ) ≤ (62240908121421311/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (106132556716590949311/76293945312500000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2163801904647168211330799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (12939973312/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (62240908121421311/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (106132556716590949311/76293945312500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2163801904647168211330799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (12939973312/9765625) + (1058793436/9765625) * (x1 - (6.0688))
      + (-163096/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((12939973312/9765625) + (1058793436/9765625) * (x1 - (6.0688))
      + (-163096/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (871568042288/244140625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,lo,hi,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lllhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (4) (8) (8) - (36/25) * (deltaX4 x1 (4) (4) (4) (8) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (4) (8) (8) - (36/25) * (deltaX4 x1 (4) (4) (4) (8) (8)) ^ 2
      = (14624100486433164/3814697265625) + (x1 - (6.0688)) * ((8347925260992/6103515625) + (1315570616/9765625) * (x1 - (6.0688))
        + (-76192/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8347925260992/6103515625) + (1315570616/9765625) * (x1 - (6.0688))
      + (-76192/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (8347925260992/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (32289281102045183/22888183593750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (83099257544195166779/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2275134182168419094990799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8347925260992/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (32289281102045183/22888183593750) := by norm_num
  have hb2 : (0:ℝ) ≤ (83099257544195166779/57220458984375000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2275134182168419094990799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8347925260992/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (32289281102045183/22888183593750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (83099257544195166779/57220458984375000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2275134182168419094990799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8347925260992/6103515625) + (1315570616/9765625) * (x1 - (6.0688))
      + (-76192/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8347925260992/6103515625) + (1315570616/9765625) * (x1 - (6.0688))
      + (-76192/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (14624100486433164/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,lo,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_llhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (4) (4) (6.3504) (6.0688) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (4) (4) (6.3504) (6.0688) (6.0688)) ^ 2
      = (24939977681427084/3814697265625) + (x1 - (6.0688)) * ((8483162456376/6103515625) + (-1293860232/9765625) * (x1 - (6.0688))
        + (-608436/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8483162456376/6103515625) + (-1293860232/9765625) * (x1 - (6.0688))
      + (-608436/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (8483162456376/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (10281181898930253/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (197350729327973233377/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (1870671838368887553980799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8483162456376/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (10281181898930253/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (197350729327973233377/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (1870671838368887553980799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8483162456376/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (10281181898930253/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (197350729327973233377/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (1870671838368887553980799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8483162456376/6103515625) + (-1293860232/9765625) * (x1 - (6.0688))
      + (-608436/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8483162456376/6103515625) + (-1293860232/9765625) * (x1 - (6.0688))
      + (-608436/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (24939977681427084/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,lo,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_llhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 x1 (4) (4) (6.3504) (6.0688) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 x1 (4) (4) (6.3504) (6.0688) (8)) ^ 2
      = (27432048396767084/3814697265625) + (x1 - (6.0688)) * ((11373200538212/6103515625) + (-394664544/9765625) * (x1 - (6.0688))
        + (-521532/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((11373200538212/6103515625) + (-394664544/9765625) * (x1 - (6.0688))
      + (-521532/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (11373200538212/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (7059023096035538/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (278833943666050999499/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2735559213085726737640799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (11373200538212/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (7059023096035538/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (278833943666050999499/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2735559213085726737640799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (11373200538212/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (7059023096035538/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (278833943666050999499/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2735559213085726737640799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (11373200538212/6103515625) + (-394664544/9765625) * (x1 - (6.0688))
      + (-521532/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((11373200538212/6103515625) + (-394664544/9765625) * (x1 - (6.0688))
      + (-521532/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (27432048396767084/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,hi,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_llhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 x1 (4) (4) (6.3504) (8) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 x1 (4) (4) (6.3504) (8) (6.0688)) ^ 2
      = (27432048396767084/3814697265625) + (x1 - (6.0688)) * ((11373200538212/6103515625) + (-394664544/9765625) * (x1 - (6.0688))
        + (-521532/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((11373200538212/6103515625) + (-394664544/9765625) * (x1 - (6.0688))
      + (-521532/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (11373200538212/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (7059023096035538/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (278833943666050999499/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2735559213085726737640799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (11373200538212/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (7059023096035538/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (278833943666050999499/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2735559213085726737640799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (11373200538212/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (7059023096035538/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (278833943666050999499/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2735559213085726737640799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (11373200538212/6103515625) + (-394664544/9765625) * (x1 - (6.0688))
      + (-521532/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((11373200538212/6103515625) + (-394664544/9765625) * (x1 - (6.0688))
      + (-521532/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (27432048396767084/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,lo,hi,hi,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_llhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (4) (6.3504) (8) (8) - (36/25) * (deltaX4 x1 (4) (4) (6.3504) (8) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (4) (6.3504) (8) (8) - (36/25) * (deltaX4 x1 (4) (4) (6.3504) (8) (8)) ^ 2
      = (30559677774914196/3814697265625) + (x1 - (6.0688)) * ((13834010112876/6103515625) + (294744888/9765625) * (x1 - (6.0688))
        + (-434628/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((13834010112876/6103515625) + (294744888/9765625) * (x1 - (6.0688))
      + (-434628/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (13834010112876/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (17366040793867773/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (347493083029663725621/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (3461739026582090321300799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (13834010112876/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (17366040793867773/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (347493083029663725621/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (3461739026582090321300799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (13834010112876/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (17366040793867773/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (347493083029663725621/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (3461739026582090321300799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (13834010112876/6103515625) + (294744888/9765625) * (x1 - (6.0688))
      + (-434628/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((13834010112876/6103515625) + (294744888/9765625) * (x1 - (6.0688))
      + (-434628/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (30559677774914196/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,lo,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lhlll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (4) (6.3504) (4) (6.0688) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (4) (6.3504) (4) (6.0688) (6.0688)) ^ 2
      = (10359275042067084/3814697265625) + (x1 - (6.0688)) * ((8227229968188/6103515625) + (1419729452/9765625) * (x1 - (6.0688))
        + (-144232/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8227229968188/6103515625) + (1419729452/9765625) * (x1 - (6.0688))
      + (-144232/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (8227229968188/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (63829250604965827/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (329125119870984515411/228881835937500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2254453312763949960890799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8227229968188/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (63829250604965827/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (329125119870984515411/228881835937500000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2254453312763949960890799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8227229968188/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (63829250604965827/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (329125119870984515411/228881835937500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2254453312763949960890799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8227229968188/6103515625) + (1419729452/9765625) * (x1 - (6.0688))
      + (-144232/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8227229968188/6103515625) + (1419729452/9765625) * (x1 - (6.0688))
      + (-144232/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (10359275042067084/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,lo,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lhllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (4) (6.0688) (8) - (36/25) * (deltaX4 x1 (4) (6.3504) (4) (6.0688) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (4) (6.0688) (8) - (36/25) * (deltaX4 x1 (4) (6.3504) (4) (6.0688) (8)) ^ 2
      = (2250572162100696/3814697265625) + (x1 - (6.0688)) * ((7282699461576/6103515625) + (2063601188/9765625) * (x1 - (6.0688))
        + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((7282699461576/6103515625) + (2063601188/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (7282699461576/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (57709007591097313/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (151865987858883322297/114440917968750000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2122482104433443944550799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (7282699461576/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (57709007591097313/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (151865987858883322297/114440917968750000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2122482104433443944550799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (7282699461576/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (57709007591097313/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (151865987858883322297/114440917968750000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2122482104433443944550799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (7282699461576/6103515625) + (2063601188/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((7282699461576/6103515625) + (2063601188/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (2250572162100696/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,hi,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lhlhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (4) (8) (6.0688) - (36/25) * (deltaX4 x1 (4) (6.3504) (4) (8) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (4) (8) (6.0688) - (36/25) * (deltaX4 x1 (4) (6.3504) (4) (8) (6.0688)) ^ 2
      = (8807014357727084/3814697265625) + (x1 - (6.0688)) * ((7197009906352/6103515625) + (1581322612/9765625) * (x1 - (6.0688))
        + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((7197009906352/6103515625) + (1581322612/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (7197009906352/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (56344469914805237/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (48883326212624314099/38146972656250000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2028873114416236344550799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (7197009906352/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (56344469914805237/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (48883326212624314099/38146972656250000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2028873114416236344550799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (7197009906352/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (56344469914805237/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (48883326212624314099/38146972656250000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2028873114416236344550799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (7197009906352/6103515625) + (1581322612/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((7197009906352/6103515625) + (1581322612/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (8807014357727084/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,lo,hi,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lhlhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (4) (8) (8) - (36/25) * (deltaX4 x1 (4) (6.3504) (4) (8) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (4) (8) (8) - (36/25) * (deltaX4 x1 (4) (6.3504) (4) (8) (8)) ^ 2
      = (4710725891733536/3814697265625) + (x1 - (6.0688)) * ((6559449138832/6103515625) + (2015408092/9765625) * (x1 - (6.0688))
        + (29576/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((6559449138832/6103515625) + (2015408092/9765625) * (x1 - (6.0688))
      + (29576/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (6559449138832/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (52212495599851967/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (92092711631910151259/76293945312500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (1942243906431254728210799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (6559449138832/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (52212495599851967/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (92092711631910151259/76293945312500000) := by norm_num
  have hb3 : (0:ℝ) ≤ (1942243906431254728210799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (6559449138832/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (52212495599851967/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (92092711631910151259/76293945312500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (1942243906431254728210799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (6559449138832/6103515625) + (2015408092/9765625) * (x1 - (6.0688))
      + (29576/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((6559449138832/6103515625) + (2015408092/9765625) * (x1 - (6.0688))
      + (29576/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (4710725891733536/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,lo,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lhhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (4) (6.3504) (6.3504) (6.0688) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (4) (6.3504) (6.3504) (6.0688) (6.0688)) ^ 2
      = (1934609456816/244140625) + (x1 - (6.0688)) * ((21544901024/9765625) + (60181704/9765625) * (x1 - (6.0688))
        + (-502668/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((21544901024/9765625) + (60181704/9765625) * (x1 - (6.0688))
      + (-502668/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (21544901024/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (16846967076053659/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (335738063442531991151/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (3328420926437606687200799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (21544901024/9765625) := by norm_num
  have hb1 : (0:ℝ) ≤ (16846967076053659/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (335738063442531991151/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (3328420926437606687200799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (21544901024/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (16846967076053659/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (335738063442531991151/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (3328420926437606687200799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (21544901024/9765625) + (60181704/9765625) * (x1 - (6.0688))
      + (-502668/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((21544901024/9765625) + (60181704/9765625) * (x1 - (6.0688))
      + (-502668/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1934609456816/244140625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,lo,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lhhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 x1 (4) (6.3504) (6.3504) (6.0688) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 x1 (4) (6.3504) (6.3504) (6.0688) (8)) ^ 2
      = (28632596212040696/3814697265625) + (x1 - (6.0688)) * ((15879124173412/6103515625) + (1136685692/9765625) * (x1 - (6.0688))
        + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((15879124173412/6103515625) + (1136685692/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (15879124173412/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (120794802268204567/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1221235893034382771819/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (4100728230670213370860799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (15879124173412/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (120794802268204567/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1221235893034382771819/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (4100728230670213370860799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (15879124173412/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (120794802268204567/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1221235893034382771819/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (4100728230670213370860799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (15879124173412/6103515625) + (1136685692/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((15879124173412/6103515625) + (1136685692/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (28632596212040696/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,hi,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lhhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 x1 (4) (6.3504) (6.3504) (8) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 x1 (4) (6.3504) (6.3504) (8) (6.0688)) ^ 2
      = (2097820634112/244140625) + (x1 - (6.0688)) * ((24252636544/9765625) + (654407116/9765625) * (x1 - (6.0688))
        + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((24252636544/9765625) + (654407116/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (24252636544/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (114663738755502491/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1152706597786241251819/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (3848235046106005770860799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (24252636544/9765625) := by norm_num
  have hb1 : (0:ℝ) ≤ (114663738755502491/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1152706597786241251819/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (3848235046106005770860799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (24252636544/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (114663738755502491/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1152706597786241251819/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (3848235046106005770860799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (24252636544/9765625) + (654407116/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((24252636544/9765625) + (654407116/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (2097820634112/244140625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(lo,hi,hi,hi,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_lhhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (4) (6.3504) (6.3504) (8) (8) - (36/25) * (deltaX4 x1 (4) (6.3504) (6.3504) (8) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (4) (6.3504) (6.3504) (8) (8) - (36/25) * (deltaX4 x1 (4) (6.3504) (6.3504) (8) (8)) ^ 2
      = (33214529494137484/3814697265625) + (x1 - (6.0688)) * ((3471248296868/1220703125) + (1521124848/9765625) * (x1 - (6.0688))
        + (-65772/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3471248296868/1220703125) + (1521124848/9765625) * (x1 - (6.0688))
      + (-65772/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (3471248296868/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (11037383650422529/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (89620460628475528679/30517578125000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (4535337568643136854520799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3471248296868/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (11037383650422529/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (89620460628475528679/30517578125000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (4535337568643136854520799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3471248296868/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (11037383650422529/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (89620460628475528679/30517578125000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (4535337568643136854520799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3471248296868/1220703125) + (1521124848/9765625) * (x1 - (6.0688))
      + (-65772/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3471248296868/1220703125) + (1521124848/9765625) * (x1 - (6.0688))
      + (-65772/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (33214529494137484/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,lo,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hllll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (4) (4) (6.0688) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (4) (4) (6.0688) (6.0688)) ^ 2
      = (10359275042067084/3814697265625) + (x1 - (6.0688)) * ((8227229968188/6103515625) + (1419729452/9765625) * (x1 - (6.0688))
        + (-144232/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8227229968188/6103515625) + (1419729452/9765625) * (x1 - (6.0688))
      + (-144232/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (8227229968188/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (63829250604965827/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (329125119870984515411/228881835937500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2254453312763949960890799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8227229968188/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (63829250604965827/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (329125119870984515411/228881835937500000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2254453312763949960890799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8227229968188/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (63829250604965827/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (329125119870984515411/228881835937500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2254453312763949960890799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8227229968188/6103515625) + (1419729452/9765625) * (x1 - (6.0688))
      + (-144232/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8227229968188/6103515625) + (1419729452/9765625) * (x1 - (6.0688))
      + (-144232/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (10359275042067084/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,lo,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hlllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (4) (6.0688) (8) - (36/25) * (deltaX4 x1 (6.3504) (4) (4) (6.0688) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (4) (6.0688) (8) - (36/25) * (deltaX4 x1 (6.3504) (4) (4) (6.0688) (8)) ^ 2
      = (8807014357727084/3814697265625) + (x1 - (6.0688)) * ((7197009906352/6103515625) + (1581322612/9765625) * (x1 - (6.0688))
        + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((7197009906352/6103515625) + (1581322612/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (7197009906352/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (56344469914805237/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (48883326212624314099/38146972656250000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2028873114416236344550799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (7197009906352/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (56344469914805237/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (48883326212624314099/38146972656250000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2028873114416236344550799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (7197009906352/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (56344469914805237/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (48883326212624314099/38146972656250000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2028873114416236344550799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (7197009906352/6103515625) + (1581322612/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((7197009906352/6103515625) + (1581322612/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (8807014357727084/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,hi,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hllhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (4) (8) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (4) (4) (8) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (4) (8) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (4) (4) (8) (6.0688)) ^ 2
      = (2250572162100696/3814697265625) + (x1 - (6.0688)) * ((7282699461576/6103515625) + (2063601188/9765625) * (x1 - (6.0688))
        + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((7282699461576/6103515625) + (2063601188/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (7282699461576/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (57709007591097313/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (151865987858883322297/114440917968750000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2122482104433443944550799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (7282699461576/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (57709007591097313/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (151865987858883322297/114440917968750000) := by norm_num
  have hb3 : (0:ℝ) ≤ (2122482104433443944550799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (7282699461576/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (57709007591097313/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (151865987858883322297/114440917968750000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2122482104433443944550799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (7282699461576/6103515625) + (2063601188/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((7282699461576/6103515625) + (2063601188/9765625) * (x1 - (6.0688))
      + (-57328/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (2250572162100696/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,lo,hi,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hllhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (4) (8) (8) - (36/25) * (deltaX4 x1 (6.3504) (4) (4) (8) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (4) (8) (8) - (36/25) * (deltaX4 x1 (6.3504) (4) (4) (8) (8)) ^ 2
      = (4710725891733536/3814697265625) + (x1 - (6.0688)) * ((6559449138832/6103515625) + (2015408092/9765625) * (x1 - (6.0688))
        + (29576/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((6559449138832/6103515625) + (2015408092/9765625) * (x1 - (6.0688))
      + (29576/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (6559449138832/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (52212495599851967/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (92092711631910151259/76293945312500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (1942243906431254728210799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (6559449138832/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (52212495599851967/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (92092711631910151259/76293945312500000) := by norm_num
  have hb3 : (0:ℝ) ≤ (1942243906431254728210799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (6559449138832/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (52212495599851967/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (92092711631910151259/76293945312500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (1942243906431254728210799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (6559449138832/6103515625) + (2015408092/9765625) * (x1 - (6.0688))
      + (29576/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((6559449138832/6103515625) + (2015408092/9765625) * (x1 - (6.0688))
      + (29576/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (4710725891733536/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,lo,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hlhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (4) (6.3504) (6.0688) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (4) (6.3504) (6.0688) (6.0688)) ^ 2
      = (1934609456816/244140625) + (x1 - (6.0688)) * ((21544901024/9765625) + (60181704/9765625) * (x1 - (6.0688))
        + (-502668/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((21544901024/9765625) + (60181704/9765625) * (x1 - (6.0688))
      + (-502668/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (21544901024/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (16846967076053659/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (335738063442531991151/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (3328420926437606687200799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (21544901024/9765625) := by norm_num
  have hb1 : (0:ℝ) ≤ (16846967076053659/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (335738063442531991151/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (3328420926437606687200799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (21544901024/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (16846967076053659/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (335738063442531991151/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (3328420926437606687200799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (21544901024/9765625) + (60181704/9765625) * (x1 - (6.0688))
      + (-502668/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((21544901024/9765625) + (60181704/9765625) * (x1 - (6.0688))
      + (-502668/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1934609456816/244140625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,lo,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hlhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 x1 (6.3504) (4) (6.3504) (6.0688) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 x1 (6.3504) (4) (6.3504) (6.0688) (8)) ^ 2
      = (2097820634112/244140625) + (x1 - (6.0688)) * ((24252636544/9765625) + (654407116/9765625) * (x1 - (6.0688))
        + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((24252636544/9765625) + (654407116/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (24252636544/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (114663738755502491/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1152706597786241251819/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (3848235046106005770860799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (24252636544/9765625) := by norm_num
  have hb1 : (0:ℝ) ≤ (114663738755502491/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1152706597786241251819/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (3848235046106005770860799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (24252636544/9765625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (114663738755502491/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1152706597786241251819/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (3848235046106005770860799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (24252636544/9765625) + (654407116/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((24252636544/9765625) + (654407116/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (2097820634112/244140625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,hi,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hlhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (4) (6.3504) (8) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (4) (6.3504) (8) (6.0688)) ^ 2
      = (28632596212040696/3814697265625) + (x1 - (6.0688)) * ((15879124173412/6103515625) + (1136685692/9765625) * (x1 - (6.0688))
        + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((15879124173412/6103515625) + (1136685692/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (15879124173412/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (120794802268204567/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (1221235893034382771819/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (4100728230670213370860799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (15879124173412/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (120794802268204567/45776367187500) := by norm_num
  have hb2 : (0:ℝ) ≤ (1221235893034382771819/457763671875000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (4100728230670213370860799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (15879124173412/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (120794802268204567/45776367187500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (1221235893034382771819/457763671875000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (4100728230670213370860799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (15879124173412/6103515625) + (1136685692/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((15879124173412/6103515625) + (1136685692/9765625) * (x1 - (6.0688))
      + (-415764/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (28632596212040696/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,lo,hi,hi,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hlhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (4) (6.3504) (8) (8) - (36/25) * (deltaX4 x1 (6.3504) (4) (6.3504) (8) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (4) (6.3504) (8) (8) - (36/25) * (deltaX4 x1 (6.3504) (4) (6.3504) (8) (8)) ^ 2
      = (33214529494137484/3814697265625) + (x1 - (6.0688)) * ((3471248296868/1220703125) + (1521124848/9765625) * (x1 - (6.0688))
        + (-65772/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((3471248296868/1220703125) + (1521124848/9765625) * (x1 - (6.0688))
      + (-65772/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (3471248296868/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (11037383650422529/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (89620460628475528679/30517578125000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (4535337568643136854520799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (3471248296868/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (11037383650422529/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (89620460628475528679/30517578125000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (4535337568643136854520799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (3471248296868/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (11037383650422529/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (89620460628475528679/30517578125000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (4535337568643136854520799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (3471248296868/1220703125) + (1521124848/9765625) * (x1 - (6.0688))
      + (-65772/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((3471248296868/1220703125) + (1521124848/9765625) * (x1 - (6.0688))
      + (-65772/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (33214529494137484/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,lo,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hhlll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (4) (6.0688) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (4) (6.0688) (6.0688)) ^ 2
      = (9763415732659436/3814697265625) + (x1 - (6.0688)) * ((8508029230048/6103515625) + (387296504/1953125) * (x1 - (6.0688))
        + (-38464/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((8508029230048/6103515625) + (387296504/1953125) * (x1 - (6.0688))
      + (-38464/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (8508029230048/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (6670871188873127/4577636718750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (14494319857050946753/9536743164062500) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (2411478133817169794110799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (8508029230048/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (6670871188873127/4577636718750) := by norm_num
  have hb2 : (0:ℝ) ≤ (14494319857050946753/9536743164062500) := by norm_num
  have hb3 : (0:ℝ) ≤ (2411478133817169794110799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (8508029230048/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (6670871188873127/4577636718750) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (14494319857050946753/9536743164062500) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (2411478133817169794110799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (8508029230048/6103515625) + (387296504/1953125) * (x1 - (6.0688))
      + (-38464/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((8508029230048/6103515625) + (387296504/1953125) * (x1 - (6.0688))
      + (-38464/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (9763415732659436/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,lo,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hhllh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (4) (6.0688) (8) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (4) (6.0688) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (4) (6.0688) (8) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (4) (6.0688) (8)) ^ 2
      = (99651472962764/152587890625) + (x1 - (6.0688)) * ((265050449372/244140625) + (455076796/1953125) * (x1 - (6.0688))
        + (9688/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((265050449372/244140625) + (455076796/1953125) * (x1 - (6.0688))
      + (9688/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (265050449372/244140625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (10620542722089671/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (56551877122892168251/45776367187500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (1999550143613223677770799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (265050449372/244140625) := by norm_num
  have hb1 : (0:ℝ) ≤ (10620542722089671/9155273437500) := by norm_num
  have hb2 : (0:ℝ) ≤ (56551877122892168251/45776367187500000) := by norm_num
  have hb3 : (0:ℝ) ≤ (1999550143613223677770799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (265050449372/244140625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (10620542722089671/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (56551877122892168251/45776367187500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (1999550143613223677770799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (265050449372/244140625) + (455076796/1953125) * (x1 - (6.0688))
      + (9688/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((265050449372/244140625) + (455076796/1953125) * (x1 - (6.0688))
      + (9688/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (99651472962764/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,hi,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hhlhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (4) (8) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (4) (8) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (4) (8) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (4) (8) (6.0688)) ^ 2
      = (99651472962764/152587890625) + (x1 - (6.0688)) * ((265050449372/244140625) + (455076796/1953125) * (x1 - (6.0688))
        + (9688/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((265050449372/244140625) + (455076796/1953125) * (x1 - (6.0688))
      + (9688/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (265050449372/244140625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (10620542722089671/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (56551877122892168251/45776367187500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (1999550143613223677770799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (265050449372/244140625) := by norm_num
  have hb1 : (0:ℝ) ≤ (10620542722089671/9155273437500) := by norm_num
  have hb2 : (0:ℝ) ≤ (56551877122892168251/45776367187500000) := by norm_num
  have hb3 : (0:ℝ) ≤ (1999550143613223677770799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (265050449372/244140625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (10620542722089671/9155273437500) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (56551877122892168251/45776367187500000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (1999550143613223677770799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (265050449372/244140625) + (455076796/1953125) * (x1 - (6.0688))
      + (9688/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((265050449372/244140625) + (455076796/1953125) * (x1 - (6.0688))
      + (9688/3125) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (99651472962764/152587890625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,lo,hi,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hhlhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (4) (8) (8) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (4) (8) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (4) (8) (8) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (4) (8) (8)) ^ 2
      = (175061744707264/3814697265625) + (x1 - (6.0688)) * ((5265474095744/6103515625) + (2404499184/9765625) * (x1 - (6.0688))
        + (135344/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((5265474095744/6103515625) + (2404499184/9765625) * (x1 - (6.0688))
      + (135344/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (5265474095744/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (3590838951402557/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (117025916680825700219/114440917968750000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (1686466933279801961430799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (5265474095744/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (3590838951402557/3814697265625) := by norm_num
  have hb2 : (0:ℝ) ≤ (117025916680825700219/114440917968750000) := by norm_num
  have hb3 : (0:ℝ) ≤ (1686466933279801961430799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (5265474095744/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (3590838951402557/3814697265625) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (117025916680825700219/114440917968750000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (1686466933279801961430799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (5265474095744/6103515625) + (2404499184/9765625) * (x1 - (6.0688))
      + (135344/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((5265474095744/6103515625) + (2404499184/9765625) * (x1 - (6.0688))
      + (135344/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (175061744707264/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,lo,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hhhll (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (6.3504) (6.0688) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (6.3504) (6.0688) (6.0688)) ^ 2
      = (36856197749776356/3814697265625) + (x1 - (6.0688)) * ((705921688332/244140625) + (1103477256/9765625) * (x1 - (6.0688))
        + (-15876/625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((705921688332/244140625) + (1103477256/9765625) * (x1 - (6.0688))
      + (-15876/625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (705921688332/244140625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (22335330288718251/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (18041062374473527557/6103515625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (4539677643493037420420799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (705921688332/244140625) := by norm_num
  have hb1 : (0:ℝ) ≤ (22335330288718251/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (18041062374473527557/6103515625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (4539677643493037420420799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (705921688332/244140625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (22335330288718251/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (18041062374473527557/6103515625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (4539677643493037420420799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (705921688332/244140625) + (1103477256/9765625) * (x1 - (6.0688))
      + (-15876/625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((705921688332/244140625) + (1103477256/9765625) * (x1 - (6.0688))
      + (-15876/625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (36856197749776356/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,lo,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hhhlh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (6.3504) (6.0688) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (6.3504) (6.0688) (8)) ^ 2
      = (36097095170443104/3814697265625) + (x1 - (6.0688)) * ((19124365752576/6103515625) + (1875010968/9765625) * (x1 - (6.0688))
        + (-309996/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((19124365752576/6103515625) + (1875010968/9765625) * (x1 - (6.0688))
      + (-309996/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (19124365752576/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24373204379962953/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (495893029063071115047/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (5032028165852204004080799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (19124365752576/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (24373204379962953/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (495893029063071115047/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (5032028165852204004080799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (19124365752576/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24373204379962953/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (495893029063071115047/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (5032028165852204004080799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (19124365752576/6103515625) + (1875010968/9765625) * (x1 - (6.0688))
      + (-309996/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((19124365752576/6103515625) + (1875010968/9765625) * (x1 - (6.0688))
      + (-309996/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (36097095170443104/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,hi,lo)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hhhhl (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (6.3504) (8) (6.0688)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (6.3504) (8) (6.0688)) ^ 2
      = (36097095170443104/3814697265625) + (x1 - (6.0688)) * ((19124365752576/6103515625) + (1875010968/9765625) * (x1 - (6.0688))
        + (-309996/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((19124365752576/6103515625) + (1875010968/9765625) * (x1 - (6.0688))
      + (-309996/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (19124365752576/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (24373204379962953/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (495893029063071115047/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (5032028165852204004080799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (19124365752576/6103515625) := by norm_num
  have hb1 : (0:ℝ) ≤ (24373204379962953/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (495893029063071115047/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (5032028165852204004080799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (19124365752576/6103515625) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (24373204379962953/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (495893029063071115047/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (5032028165852204004080799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (19124365752576/6103515625) + (1875010968/9765625) * (x1 - (6.0688))
      + (-309996/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((19124365752576/6103515625) + (1875010968/9765625) * (x1 - (6.0688))
      + (-309996/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (36097095170443104/3814697265625) := by norm_num
  linarith [key, hdp, hC0]

/-- line `(hi,hi,hi,hi,hi)` of debt `0011` (Taylor end = lo);
exact Bernstein certificate on the residual cubic in the `x1` increment. -/
theorem ztgline_0011_hhhhh (x1 : ℝ) (h1 : (6.0688) ≤ x1) (h2 : x1 ≤ (7.02674064)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.3504) (8) (8) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (6.3504) (8) (8)) ^ 2 := by
  have key : 4 * x1 * deltaX x1 (6.3504) (6.3504) (6.3504) (8) (8) - (36/25) * (deltaX4 x1 (6.3504) (6.3504) (6.3504) (8) (8)) ^ 2
      = (1532529625728492/152587890625) + (x1 - (6.0688)) * ((4119896605176/1220703125) + (2436758424/9765625) * (x1 - (6.0688))
        + (-223092/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := by
    unfold deltaX deltaX4; ring
  have hd : (0:ℝ) ≤ (x1 - (6.0688)) := by linarith
  have hd2 : (x1 - (6.0688)) ≤ (5987129/6250000) := by linarith
  have hQ : (5987129/6250000) ^ 3 * ((4119896605176/1220703125) + (2436758424/9765625) * (x1 - (6.0688))
      + (-223092/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3)
      = (4119896605176/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3
        + 3 * (26357236575113529/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2
        + 3 * (538635979694839001169/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688)))
        + (5492676686040894987740799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := by
    ring
  have hb0 : (0:ℝ) ≤ (4119896605176/1220703125) := by norm_num
  have hb1 : (0:ℝ) ≤ (26357236575113529/7629394531250) := by norm_num
  have hb2 : (0:ℝ) ≤ (538635979694839001169/152587890625000000) := by norm_num
  have hb3 : (0:ℝ) ≤ (5492676686040894987740799/1525878906250000000000) := by norm_num
  have hP3 : (0:ℝ) ≤ (5987129/6250000) - (x1 - (6.0688)) := by linarith
  have hP2 : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 2 := by nlinarith [sq_nonneg ((5987129/6250000) - (x1 - (6.0688)))]
  have hT2 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 2 := by nlinarith [sq_nonneg ((x1 - (6.0688)))]
  have hP3c : (0:ℝ) ≤ ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := by nlinarith [hP3, hP2]
  have hT3 : (0:ℝ) ≤ (x1 - (6.0688)) ^ 3 := by nlinarith [hd, hT2]
  have hp0 : (0:ℝ) ≤ (4119896605176/1220703125) * ((5987129/6250000) - (x1 - (6.0688))) ^ 3 := mul_nonneg hb0 hP3c
  have hp1 : (0:ℝ) ≤ 3 * (26357236575113529/7629394531250) * (x1 - (6.0688)) * ((5987129/6250000) - (x1 - (6.0688))) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb1) hd) hP2
  have hp2 : (0:ℝ) ≤ 3 * (538635979694839001169/152587890625000000) * (x1 - (6.0688)) ^ 2 * ((5987129/6250000) - (x1 - (6.0688))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb2) hT2) hP3
  have hp3 : (0:ℝ) ≤ (5492676686040894987740799/1525878906250000000000) * (x1 - (6.0688)) ^ 3 := mul_nonneg hb3 hT3
  have hQ0 : (0:ℝ) ≤ (4119896605176/1220703125) + (2436758424/9765625) * (x1 - (6.0688))
      + (-223092/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3 := by
    linarith [hQ, hp0, hp1, hp2, hp3]
  have hdp : (0:ℝ) ≤ (x1 - (6.0688)) * ((4119896605176/1220703125) + (2436758424/9765625) * (x1 - (6.0688))
      + (-223092/15625) * (x1 - (6.0688)) ^ 2 + (-36/25) * (x1 - (6.0688)) ^ 3) := mul_nonneg hd hQ0
  have hC0 : (0:ℝ) ≤ (1532529625728492/152587890625) := by norm_num
  linarith [key, hdp, hC0]


/-! ## 5. The four `dihY` lower bounds -/
/-- **dihY lower bound** for the `ZTGIJCF4 1_1_0_0` debt box:
`1.008 ≤ dihY` (via `arctan 8 / 5` with the polynomial certificate above).
Consumed with `γ4 ≥ 0.05` (trio) / `γ4 ≥ 0.065` (`0011`) by the Assembly
wiring to close the decoupled route. -/
theorem ztg_dihY_1_1_0_0 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1l : 2 * hminus ≤ y1) (h1h : y1 ≤ 2 * hplus)
    (h2l : 2 ≤ y2) (h2h : y2 ≤ 2 * hminus)
    (h3l : bank_ZTGIJCF4lo 1 ≤ y3) (h3h : y3 ≤ bank_ZTGIJCF4hi 1)
    (h4l : bank_ZTGIJCF4lo 1 ≤ y4) (h4h : y4 ≤ bank_ZTGIJCF4hi 1)
    (h5l : bank_ZTGIJCF4lo 0 ≤ y5) (h5h : y5 ≤ bank_ZTGIJCF4hi 0)
    (h6l : bank_ZTGIJCF4lo 0 ≤ y6) (h6h : y6 ≤ bank_ZTGIJCF4hi 0) :
    (1.008:ℝ) ≤ dihY y1 y2 y3 y4 y5 y6 := by
  have hmi : (1.23175:ℝ) ≤ hminus := Kepler.NliBanks7.hminus_ge_123175
  have hmiu : hminus < (1.26:ℝ) := mi_hminus_lt_h0
  have hy1p : (0:ℝ) ≤ y1 := by linarith [hmi, h1l]
  have hy1pos : (0:ℝ) < y1 := by linarith [hmi, h1l]
  have hx1l : (6.0688) ≤ y1 * y1 := by
    have h246 : (4927/2000:ℝ) ≤ y1 := by linarith [hmi, h1l]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy1p), sq_nonneg (y1 - 4927/2000)]
  have hx1h : y1 * y1 ≤ 7.02674064 := Kepler.NliBanks3.sq_le_hplus y1 (hy1p) (h1h)
  have h3hm : (2:ℝ) * hminus ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3s8 : y3 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h3h
  have hy3p : (0:ℝ) ≤ y3 := by linarith [hmi, h3hm]
  have hx3l : (6.0688) ≤ y3 * y3 := by
    have h246 : (4927/2000:ℝ) ≤ y3 := by linarith [hmi, h3hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy3p), sq_nonneg (y3 - 4927/2000)]
  have hx3h : y3 * y3 ≤ (8) := Kepler.NliBanks3.sq_le_8 y3 (hy3p) (h3s8)
  have hw3l : (6.0650528:ℝ) ≤ y3 * y3 := by linarith [hx3l]
  have h4hm : (2:ℝ) * hminus ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4s8 : y4 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h4h
  have hy4p : (0:ℝ) ≤ y4 := by linarith [hmi, h4hm]
  have hx4l : (6.0688) ≤ y4 * y4 := by
    have h246 : (4927/2000:ℝ) ≤ y4 := by linarith [hmi, h4hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy4p), sq_nonneg (y4 - 4927/2000)]
  have hx4h : y4 * y4 ≤ (8) := Kepler.NliBanks3.sq_le_8 y4 (hy4p) (h4s8)
  have hw4l : (6.0650528:ℝ) ≤ y4 * y4 := by linarith [hx4l]
  have h5two : (2:ℝ) ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5hm : y5 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h5h
  have hy5p : (0:ℝ) ≤ y5 := by linarith [h5two]
  have hx5l : (4) ≤ y5 * y5 := Kepler.NliBanks3.sq_ge_4 y5 (h5two)
  have hx5h : y5 * y5 ≤ (6.3504) := by
    have h252 : y5 ≤ (63/25:ℝ) := by linarith [h5hm, hmiu]
    nlinarith [mul_nonneg (hy5p) (sub_nonneg.mpr h252), sq_nonneg (y5 - 63/25)]
  have hw5h : y5 * y5 ≤ (8) := by linarith [hx5h]
  have h6two : (2:ℝ) ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6hm : y6 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h6h
  have hy6p : (0:ℝ) ≤ y6 := by linarith [h6two]
  have hx6l : (4) ≤ y6 * y6 := Kepler.NliBanks3.sq_ge_4 y6 (h6two)
  have hx6h : y6 * y6 ≤ (6.3504) := by
    have h252 : y6 ≤ (63/25:ℝ) := by linarith [h6hm, hmiu]
    nlinarith [mul_nonneg (hy6p) (sub_nonneg.mpr h252), sq_nonneg (y6 - 63/25)]
  have hw6h : y6 * y6 ≤ (8) := by linarith [hx6h]
  have hy2p : (0:ℝ) ≤ y2 := by linarith [h2l]
  have hx2l : (4) ≤ y2 * y2 := Kepler.NliBanks3.sq_ge_4 y2 (h2l)
  have hx2h : y2 * y2 ≤ (6.3504) := by
    have h252 : y2 ≤ (63/25:ℝ) := by linarith [h2h, hmiu]
    nlinarith [mul_nonneg (hy2p) (sub_nonneg.mpr h252), sq_nonneg (y2 - 63/25)]
  have hw2h : y2 * y2 ≤ (8) := by linarith [hx2h]
  have hw1l : (6.0650528:ℝ) ≤ y1 * y1 := by linarith [hx1l]
  have hw3h : y3 * y3 ≤ (8) := hx3h
  have hw4h : y4 * y4 ≤ (8) := hx4h
  have hw5l : (4) ≤ y5 * y5 := hx5l
  have hw6l : (4) ≤ y6 * y6 := hx6l
  have hΔ : (50:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    Kepler.NliBanks5.dX_box_ge_wide (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
      (by linarith [hx1l]) hx1h hx2l hw2h (by linarith [hx3l]) hx3h (by linarith [hx4l]) hx4h hx5l hw5h hx6l hw6h
  have hΔy : (50:ℝ) ≤ deltaY y1 y2 y3 y4 y5 y6 := hΔ
  have hcf00 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.0688) (6.0688) (4) (4) - (64/25) * (deltaX4 (y1*y1) (4) (6.0688) (6.0688) (4) (4)) ^ 2 := ztgline_1100_lllll (y1*y1) hx1l hx1h
  have hcf01 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.0688) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (6.0688) (6.0688) (4) (6.3504)) ^ 2 := ztgline_1100_llllh (y1*y1) hx1l hx1h
  have hcf02 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.0688) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 (y1*y1) (4) (6.0688) (6.0688) (6.3504) (4)) ^ 2 := ztgline_1100_lllhl (y1*y1) hx1l hx1h
  have hcf03 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.0688) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (6.0688) (6.0688) (6.3504) (6.3504)) ^ 2 := ztgline_1100_lllhh (y1*y1) hx1l hx1h
  have hcf04 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.0688) (8) (4) (4) - (64/25) * (deltaX4 (y1*y1) (4) (6.0688) (8) (4) (4)) ^ 2 := ztgline_1100_llhll (y1*y1) hx1l hx1h
  have hcf05 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.0688) (8) (4) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (6.0688) (8) (4) (6.3504)) ^ 2 := ztgline_1100_llhlh (y1*y1) hx1l hx1h
  have hcf06 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.0688) (8) (6.3504) (4) - (64/25) * (deltaX4 (y1*y1) (4) (6.0688) (8) (6.3504) (4)) ^ 2 := ztgline_1100_llhhl (y1*y1) hx1l hx1h
  have hcf07 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.0688) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (6.0688) (8) (6.3504) (6.3504)) ^ 2 := ztgline_1100_llhhh (y1*y1) hx1l hx1h
  have hcf08 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (8) (6.0688) (4) (4) - (64/25) * (deltaX4 (y1*y1) (4) (8) (6.0688) (4) (4)) ^ 2 := ztgline_1100_lhlll (y1*y1) hx1l hx1h
  have hcf09 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (8) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (8) (6.0688) (4) (6.3504)) ^ 2 := ztgline_1100_lhllh (y1*y1) hx1l hx1h
  have hcf10 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (8) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 (y1*y1) (4) (8) (6.0688) (6.3504) (4)) ^ 2 := ztgline_1100_lhlhl (y1*y1) hx1l hx1h
  have hcf11 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (8) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (8) (6.0688) (6.3504) (6.3504)) ^ 2 := ztgline_1100_lhlhh (y1*y1) hx1l hx1h
  have hcf12 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (8) (8) (4) (4) - (64/25) * (deltaX4 (y1*y1) (4) (8) (8) (4) (4)) ^ 2 := ztgline_1100_lhhll (y1*y1) hx1l hx1h
  have hcf13 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (8) (8) (4) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (8) (8) (4) (6.3504)) ^ 2 := ztgline_1100_lhhlh (y1*y1) hx1l hx1h
  have hcf14 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (8) (8) (6.3504) (4) - (64/25) * (deltaX4 (y1*y1) (4) (8) (8) (6.3504) (4)) ^ 2 := ztgline_1100_lhhhl (y1*y1) hx1l hx1h
  have hcf15 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (8) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (8) (8) (6.3504) (6.3504)) ^ 2 := ztgline_1100_lhhhh (y1*y1) hx1l hx1h
  have hcf16 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.0688) (6.0688) (4) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.0688) (6.0688) (4) (4)) ^ 2 := ztgline_1100_hllll (y1*y1) hx1l hx1h
  have hcf17 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.0688) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.0688) (6.0688) (4) (6.3504)) ^ 2 := ztgline_1100_hlllh (y1*y1) hx1l hx1h
  have hcf18 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.0688) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.0688) (6.0688) (6.3504) (4)) ^ 2 := ztgline_1100_hllhl (y1*y1) hx1l hx1h
  have hcf19 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.0688) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.0688) (6.0688) (6.3504) (6.3504)) ^ 2 := ztgline_1100_hllhh (y1*y1) hx1l hx1h
  have hcf20 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.0688) (8) (4) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.0688) (8) (4) (4)) ^ 2 := ztgline_1100_hlhll (y1*y1) hx1l hx1h
  have hcf21 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.0688) (8) (4) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.0688) (8) (4) (6.3504)) ^ 2 := ztgline_1100_hlhlh (y1*y1) hx1l hx1h
  have hcf22 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.0688) (8) (6.3504) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.0688) (8) (6.3504) (4)) ^ 2 := ztgline_1100_hlhhl (y1*y1) hx1l hx1h
  have hcf23 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.0688) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.0688) (8) (6.3504) (6.3504)) ^ 2 := ztgline_1100_hlhhh (y1*y1) hx1l hx1h
  have hcf24 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (8) (6.0688) (4) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (8) (6.0688) (4) (4)) ^ 2 := ztgline_1100_hhlll (y1*y1) hx1l hx1h
  have hcf25 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (8) (6.0688) (4) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (8) (6.0688) (4) (6.3504)) ^ 2 := ztgline_1100_hhllh (y1*y1) hx1l hx1h
  have hcf26 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (8) (6.0688) (6.3504) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (8) (6.0688) (6.3504) (4)) ^ 2 := ztgline_1100_hhlhl (y1*y1) hx1l hx1h
  have hcf27 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (8) (6.0688) (6.3504) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (8) (6.0688) (6.3504) (6.3504)) ^ 2 := ztgline_1100_hhlhh (y1*y1) hx1l hx1h
  have hcf28 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (8) (8) (4) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (8) (8) (4) (4)) ^ 2 := ztgline_1100_hhhll (y1*y1) hx1l hx1h
  have hcf29 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (8) (8) (4) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (8) (8) (4) (6.3504)) ^ 2 := ztgline_1100_hhhlh (y1*y1) hx1l hx1h
  have hcf30 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (8) (8) (6.3504) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (8) (8) (6.3504) (4)) ^ 2 := ztgline_1100_hhhhl (y1*y1) hx1l hx1h
  have hcf31 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (8) (8) (6.3504) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (8) (8) (6.3504) (6.3504)) ^ 2 := ztgline_1100_hhhhh (y1*y1) hx1l hx1h
  have hz : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
      - (64/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 :=
    ztgG_box5 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) (64/25)
      (by norm_num) (mul_self_nonneg y1)
      (4) (6.3504) (6.0688) (8) (6.0688) (8) (4) (6.3504) (4) (6.3504)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hx2l hx2h hx3l hx3h hx4l hx4h hx5l hx5h hx6l hx6h
      hcf00 hcf01 hcf02 hcf03 hcf04 hcf05 hcf06 hcf07 hcf08 hcf09 hcf10 hcf11 hcf12 hcf13 hcf14 hcf15 hcf16 hcf17 hcf18 hcf19 hcf20 hcf21 hcf22 hcf23 hcf24 hcf25 hcf26 hcf27 hcf28 hcf29 hcf30 hcf31
  have h41 : (0:ℝ) < 4 * (y1 * y1) :=
    mul_pos (by norm_num) (mul_pos (hy1pos) (hy1pos))
  have hdY : (0:ℝ) < deltaY y1 y2 y3 y4 y5 y6 := by linarith [hΔy]
  have hX : (0:ℝ) < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) :=
    Real.sqrt_pos.mpr (mul_pos h41 hdY)
  have hz' : (0:ℝ) ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6
      - (64/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 := hz
  have hlt : (8 / 5:ℝ) * |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)|
      ≤ Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) := by
    have hsq : ((8 / 5:ℝ) * deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2
        ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6 := by
      have e : ((8 / 5:ℝ) * deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2
          = (64/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 := by
        rw [mul_pow]
        norm_num
      rw [e]
      linarith [hz']
    have hw := Real.abs_le_sqrt hsq
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 8 / 5)] at hw
    exact hw
  exact le_trans ztg_arctan_8_5_lb (ztg_dihY_ge_arctan (by norm_num) hX hlt)
/-- **dihY lower bound** for the `ZTGIJCF4 0_1_1_0` debt box:
`1.008 ≤ dihY` (via `arctan 8 / 5` with the polynomial certificate above).
Consumed with `γ4 ≥ 0.05` (trio) / `γ4 ≥ 0.065` (`0011`) by the Assembly
wiring to close the decoupled route. -/
theorem ztg_dihY_0_1_1_0 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1l : 2 * hminus ≤ y1) (h1h : y1 ≤ 2 * hplus)
    (h2l : 2 ≤ y2) (h2h : y2 ≤ 2 * hminus)
    (h3l : bank_ZTGIJCF4lo 0 ≤ y3) (h3h : y3 ≤ bank_ZTGIJCF4hi 0)
    (h4l : bank_ZTGIJCF4lo 1 ≤ y4) (h4h : y4 ≤ bank_ZTGIJCF4hi 1)
    (h5l : bank_ZTGIJCF4lo 1 ≤ y5) (h5h : y5 ≤ bank_ZTGIJCF4hi 1)
    (h6l : bank_ZTGIJCF4lo 0 ≤ y6) (h6h : y6 ≤ bank_ZTGIJCF4hi 0) :
    (1.008:ℝ) ≤ dihY y1 y2 y3 y4 y5 y6 := by
  have hmi : (1.23175:ℝ) ≤ hminus := Kepler.NliBanks7.hminus_ge_123175
  have hmiu : hminus < (1.26:ℝ) := mi_hminus_lt_h0
  have hy1p : (0:ℝ) ≤ y1 := by linarith [hmi, h1l]
  have hy1pos : (0:ℝ) < y1 := by linarith [hmi, h1l]
  have hx1l : (6.0688) ≤ y1 * y1 := by
    have h246 : (4927/2000:ℝ) ≤ y1 := by linarith [hmi, h1l]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy1p), sq_nonneg (y1 - 4927/2000)]
  have hx1h : y1 * y1 ≤ 7.02674064 := Kepler.NliBanks3.sq_le_hplus y1 (hy1p) (h1h)
  have h3two : (2:ℝ) ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3hm : y3 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h3h
  have hy3p : (0:ℝ) ≤ y3 := by linarith [h3two]
  have hx3l : (4) ≤ y3 * y3 := Kepler.NliBanks3.sq_ge_4 y3 (h3two)
  have hx3h : y3 * y3 ≤ (6.3504) := by
    have h252 : y3 ≤ (63/25:ℝ) := by linarith [h3hm, hmiu]
    nlinarith [mul_nonneg (hy3p) (sub_nonneg.mpr h252), sq_nonneg (y3 - 63/25)]
  have hw3h : y3 * y3 ≤ (8) := by linarith [hx3h]
  have h4hm : (2:ℝ) * hminus ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4s8 : y4 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h4h
  have hy4p : (0:ℝ) ≤ y4 := by linarith [hmi, h4hm]
  have hx4l : (6.0688) ≤ y4 * y4 := by
    have h246 : (4927/2000:ℝ) ≤ y4 := by linarith [hmi, h4hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy4p), sq_nonneg (y4 - 4927/2000)]
  have hx4h : y4 * y4 ≤ (8) := Kepler.NliBanks3.sq_le_8 y4 (hy4p) (h4s8)
  have hw4l : (6.0650528:ℝ) ≤ y4 * y4 := by linarith [hx4l]
  have h5hm : (2:ℝ) * hminus ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5s8 : y5 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h5h
  have hy5p : (0:ℝ) ≤ y5 := by linarith [hmi, h5hm]
  have hx5l : (6.0688) ≤ y5 * y5 := by
    have h246 : (4927/2000:ℝ) ≤ y5 := by linarith [hmi, h5hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy5p), sq_nonneg (y5 - 4927/2000)]
  have hx5h : y5 * y5 ≤ (8) := Kepler.NliBanks3.sq_le_8 y5 (hy5p) (h5s8)
  have hw5l : (6.0650528:ℝ) ≤ y5 * y5 := by linarith [hx5l]
  have h6two : (2:ℝ) ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6hm : y6 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h6h
  have hy6p : (0:ℝ) ≤ y6 := by linarith [h6two]
  have hx6l : (4) ≤ y6 * y6 := Kepler.NliBanks3.sq_ge_4 y6 (h6two)
  have hx6h : y6 * y6 ≤ (6.3504) := by
    have h252 : y6 ≤ (63/25:ℝ) := by linarith [h6hm, hmiu]
    nlinarith [mul_nonneg (hy6p) (sub_nonneg.mpr h252), sq_nonneg (y6 - 63/25)]
  have hw6h : y6 * y6 ≤ (8) := by linarith [hx6h]
  have hy2p : (0:ℝ) ≤ y2 := by linarith [h2l]
  have hx2l : (4) ≤ y2 * y2 := Kepler.NliBanks3.sq_ge_4 y2 (h2l)
  have hx2h : y2 * y2 ≤ (6.3504) := by
    have h252 : y2 ≤ (63/25:ℝ) := by linarith [h2h, hmiu]
    nlinarith [mul_nonneg (hy2p) (sub_nonneg.mpr h252), sq_nonneg (y2 - 63/25)]
  have hw2h : y2 * y2 ≤ (8) := by linarith [hx2h]
  have hw1l : (6.0650528:ℝ) ≤ y1 * y1 := by linarith [hx1l]
  have hw3l : (4) ≤ y3 * y3 := hx3l
  have hw4h : y4 * y4 ≤ (8) := hx4h
  have hw5h : y5 * y5 ≤ (8) := hx5h
  have hw6l : (4) ≤ y6 * y6 := hx6l
  have hΔ : (50:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    Kepler.NliBanks5.dX_box_ge_wide (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
      (by linarith [hx1l]) hx1h hx2l hw2h hx3l hw3h (by linarith [hx4l]) hx4h (by linarith [hx5l]) hx5h hx6l hw6h
  have hΔy : (50:ℝ) ≤ deltaY y1 y2 y3 y4 y5 y6 := hΔ
  have hcf00 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 (y1*y1) (4) (4) (6.0688) (6.0688) (4)) ^ 2 := ztgline_0110_lllll (y1*y1) hx1l hx1h
  have hcf01 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (4) (6.0688) (6.0688) (6.3504)) ^ 2 := ztgline_0110_llllh (y1*y1) hx1l hx1h
  have hcf02 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.0688) (8) (4) - (64/25) * (deltaX4 (y1*y1) (4) (4) (6.0688) (8) (4)) ^ 2 := ztgline_0110_lllhl (y1*y1) hx1l hx1h
  have hcf03 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (4) (6.0688) (8) (6.3504)) ^ 2 := ztgline_0110_lllhh (y1*y1) hx1l hx1h
  have hcf04 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (8) (6.0688) (4) - (64/25) * (deltaX4 (y1*y1) (4) (4) (8) (6.0688) (4)) ^ 2 := ztgline_0110_llhll (y1*y1) hx1l hx1h
  have hcf05 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (4) (8) (6.0688) (6.3504)) ^ 2 := ztgline_0110_llhlh (y1*y1) hx1l hx1h
  have hcf06 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (8) (8) (4) - (64/25) * (deltaX4 (y1*y1) (4) (4) (8) (8) (4)) ^ 2 := ztgline_0110_llhhl (y1*y1) hx1l hx1h
  have hcf07 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (8) (8) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (4) (8) (8) (6.3504)) ^ 2 := ztgline_0110_llhhh (y1*y1) hx1l hx1h
  have hcf08 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.0688) (6.0688) (4)) ^ 2 := ztgline_0110_lhlll (y1*y1) hx1l hx1h
  have hcf09 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.0688) (6.0688) (6.3504)) ^ 2 := ztgline_0110_lhllh (y1*y1) hx1l hx1h
  have hcf10 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.0688) (8) (4) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.0688) (8) (4)) ^ 2 := ztgline_0110_lhlhl (y1*y1) hx1l hx1h
  have hcf11 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.0688) (8) (6.3504)) ^ 2 := ztgline_0110_lhlhh (y1*y1) hx1l hx1h
  have hcf12 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (8) (6.0688) (4) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (8) (6.0688) (4)) ^ 2 := ztgline_0110_lhhll (y1*y1) hx1l hx1h
  have hcf13 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (8) (6.0688) (6.3504)) ^ 2 := ztgline_0110_lhhlh (y1*y1) hx1l hx1h
  have hcf14 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (8) (8) (4) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (8) (8) (4)) ^ 2 := ztgline_0110_lhhhl (y1*y1) hx1l hx1h
  have hcf15 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (8) (8) (6.3504) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (8) (8) (6.3504)) ^ 2 := ztgline_0110_lhhhh (y1*y1) hx1l hx1h
  have hcf16 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.0688) (6.0688) (4)) ^ 2 := ztgline_0110_hllll (y1*y1) hx1l hx1h
  have hcf17 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.0688) (6.0688) (6.3504)) ^ 2 := ztgline_0110_hlllh (y1*y1) hx1l hx1h
  have hcf18 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.0688) (8) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.0688) (8) (4)) ^ 2 := ztgline_0110_hllhl (y1*y1) hx1l hx1h
  have hcf19 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.0688) (8) (6.3504)) ^ 2 := ztgline_0110_hllhh (y1*y1) hx1l hx1h
  have hcf20 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (8) (6.0688) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (8) (6.0688) (4)) ^ 2 := ztgline_0110_hlhll (y1*y1) hx1l hx1h
  have hcf21 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (8) (6.0688) (6.3504)) ^ 2 := ztgline_0110_hlhlh (y1*y1) hx1l hx1h
  have hcf22 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (8) (8) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (8) (8) (4)) ^ 2 := ztgline_0110_hlhhl (y1*y1) hx1l hx1h
  have hcf23 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (8) (8) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (8) (8) (6.3504)) ^ 2 := ztgline_0110_hlhhh (y1*y1) hx1l hx1h
  have hcf24 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.0688) (6.0688) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.0688) (6.0688) (4)) ^ 2 := ztgline_0110_hhlll (y1*y1) hx1l hx1h
  have hcf25 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.0688) (6.0688) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.0688) (6.0688) (6.3504)) ^ 2 := ztgline_0110_hhllh (y1*y1) hx1l hx1h
  have hcf26 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.0688) (8) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.0688) (8) (4)) ^ 2 := ztgline_0110_hhlhl (y1*y1) hx1l hx1h
  have hcf27 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.0688) (8) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.0688) (8) (6.3504)) ^ 2 := ztgline_0110_hhlhh (y1*y1) hx1l hx1h
  have hcf28 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (8) (6.0688) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (8) (6.0688) (4)) ^ 2 := ztgline_0110_hhhll (y1*y1) hx1l hx1h
  have hcf29 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (8) (6.0688) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (8) (6.0688) (6.3504)) ^ 2 := ztgline_0110_hhhlh (y1*y1) hx1l hx1h
  have hcf30 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (8) (8) (4) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (8) (8) (4)) ^ 2 := ztgline_0110_hhhhl (y1*y1) hx1l hx1h
  have hcf31 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (8) (8) (6.3504) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (8) (8) (6.3504)) ^ 2 := ztgline_0110_hhhhh (y1*y1) hx1l hx1h
  have hz : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
      - (64/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 :=
    ztgG_box5 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) (64/25)
      (by norm_num) (mul_self_nonneg y1)
      (4) (6.3504) (4) (6.3504) (6.0688) (8) (6.0688) (8) (4) (6.3504)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hx2l hx2h hx3l hx3h hx4l hx4h hx5l hx5h hx6l hx6h
      hcf00 hcf01 hcf02 hcf03 hcf04 hcf05 hcf06 hcf07 hcf08 hcf09 hcf10 hcf11 hcf12 hcf13 hcf14 hcf15 hcf16 hcf17 hcf18 hcf19 hcf20 hcf21 hcf22 hcf23 hcf24 hcf25 hcf26 hcf27 hcf28 hcf29 hcf30 hcf31
  have h41 : (0:ℝ) < 4 * (y1 * y1) :=
    mul_pos (by norm_num) (mul_pos (hy1pos) (hy1pos))
  have hdY : (0:ℝ) < deltaY y1 y2 y3 y4 y5 y6 := by linarith [hΔy]
  have hX : (0:ℝ) < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) :=
    Real.sqrt_pos.mpr (mul_pos h41 hdY)
  have hz' : (0:ℝ) ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6
      - (64/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 := hz
  have hlt : (8 / 5:ℝ) * |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)|
      ≤ Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) := by
    have hsq : ((8 / 5:ℝ) * deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2
        ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6 := by
      have e : ((8 / 5:ℝ) * deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2
          = (64/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 := by
        rw [mul_pow]
        norm_num
      rw [e]
      linarith [hz']
    have hw := Real.abs_le_sqrt hsq
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 8 / 5)] at hw
    exact hw
  exact le_trans ztg_arctan_8_5_lb (ztg_dihY_ge_arctan (by norm_num) hX hlt)
/-- **dihY lower bound** for the `ZTGIJCF4 0_1_0_1` debt box:
`1.008 ≤ dihY` (via `arctan 8 / 5` with the polynomial certificate above).
Consumed with `γ4 ≥ 0.05` (trio) / `γ4 ≥ 0.065` (`0011`) by the Assembly
wiring to close the decoupled route. -/
theorem ztg_dihY_0_1_0_1 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1l : 2 * hminus ≤ y1) (h1h : y1 ≤ 2 * hplus)
    (h2l : 2 ≤ y2) (h2h : y2 ≤ 2 * hminus)
    (h3l : bank_ZTGIJCF4lo 0 ≤ y3) (h3h : y3 ≤ bank_ZTGIJCF4hi 0)
    (h4l : bank_ZTGIJCF4lo 1 ≤ y4) (h4h : y4 ≤ bank_ZTGIJCF4hi 1)
    (h5l : bank_ZTGIJCF4lo 0 ≤ y5) (h5h : y5 ≤ bank_ZTGIJCF4hi 0)
    (h6l : bank_ZTGIJCF4lo 1 ≤ y6) (h6h : y6 ≤ bank_ZTGIJCF4hi 1) :
    (1.008:ℝ) ≤ dihY y1 y2 y3 y4 y5 y6 := by
  have hmi : (1.23175:ℝ) ≤ hminus := Kepler.NliBanks7.hminus_ge_123175
  have hmiu : hminus < (1.26:ℝ) := mi_hminus_lt_h0
  have hy1p : (0:ℝ) ≤ y1 := by linarith [hmi, h1l]
  have hy1pos : (0:ℝ) < y1 := by linarith [hmi, h1l]
  have hx1l : (6.0688) ≤ y1 * y1 := by
    have h246 : (4927/2000:ℝ) ≤ y1 := by linarith [hmi, h1l]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy1p), sq_nonneg (y1 - 4927/2000)]
  have hx1h : y1 * y1 ≤ 7.02674064 := Kepler.NliBanks3.sq_le_hplus y1 (hy1p) (h1h)
  have h3two : (2:ℝ) ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3hm : y3 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h3h
  have hy3p : (0:ℝ) ≤ y3 := by linarith [h3two]
  have hx3l : (4) ≤ y3 * y3 := Kepler.NliBanks3.sq_ge_4 y3 (h3two)
  have hx3h : y3 * y3 ≤ (6.3504) := by
    have h252 : y3 ≤ (63/25:ℝ) := by linarith [h3hm, hmiu]
    nlinarith [mul_nonneg (hy3p) (sub_nonneg.mpr h252), sq_nonneg (y3 - 63/25)]
  have hw3h : y3 * y3 ≤ (8) := by linarith [hx3h]
  have h4hm : (2:ℝ) * hminus ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4s8 : y4 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h4h
  have hy4p : (0:ℝ) ≤ y4 := by linarith [hmi, h4hm]
  have hx4l : (6.0688) ≤ y4 * y4 := by
    have h246 : (4927/2000:ℝ) ≤ y4 := by linarith [hmi, h4hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy4p), sq_nonneg (y4 - 4927/2000)]
  have hx4h : y4 * y4 ≤ (8) := Kepler.NliBanks3.sq_le_8 y4 (hy4p) (h4s8)
  have hw4l : (6.0650528:ℝ) ≤ y4 * y4 := by linarith [hx4l]
  have h5two : (2:ℝ) ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5hm : y5 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h5h
  have hy5p : (0:ℝ) ≤ y5 := by linarith [h5two]
  have hx5l : (4) ≤ y5 * y5 := Kepler.NliBanks3.sq_ge_4 y5 (h5two)
  have hx5h : y5 * y5 ≤ (6.3504) := by
    have h252 : y5 ≤ (63/25:ℝ) := by linarith [h5hm, hmiu]
    nlinarith [mul_nonneg (hy5p) (sub_nonneg.mpr h252), sq_nonneg (y5 - 63/25)]
  have hw5h : y5 * y5 ≤ (8) := by linarith [hx5h]
  have h6hm : (2:ℝ) * hminus ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6s8 : y6 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h6h
  have hy6p : (0:ℝ) ≤ y6 := by linarith [hmi, h6hm]
  have hx6l : (6.0688) ≤ y6 * y6 := by
    have h246 : (4927/2000:ℝ) ≤ y6 := by linarith [hmi, h6hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy6p), sq_nonneg (y6 - 4927/2000)]
  have hx6h : y6 * y6 ≤ (8) := Kepler.NliBanks3.sq_le_8 y6 (hy6p) (h6s8)
  have hw6l : (6.0650528:ℝ) ≤ y6 * y6 := by linarith [hx6l]
  have hy2p : (0:ℝ) ≤ y2 := by linarith [h2l]
  have hx2l : (4) ≤ y2 * y2 := Kepler.NliBanks3.sq_ge_4 y2 (h2l)
  have hx2h : y2 * y2 ≤ (6.3504) := by
    have h252 : y2 ≤ (63/25:ℝ) := by linarith [h2h, hmiu]
    nlinarith [mul_nonneg (hy2p) (sub_nonneg.mpr h252), sq_nonneg (y2 - 63/25)]
  have hw2h : y2 * y2 ≤ (8) := by linarith [hx2h]
  have hw1l : (6.0650528:ℝ) ≤ y1 * y1 := by linarith [hx1l]
  have hw3l : (4) ≤ y3 * y3 := hx3l
  have hw4h : y4 * y4 ≤ (8) := hx4h
  have hw5l : (4) ≤ y5 * y5 := hx5l
  have hw6h : y6 * y6 ≤ (8) := hx6h
  have hΔ : (50:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    Kepler.NliBanks5.dX_box_ge_wide (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
      (by linarith [hx1l]) hx1h hx2l hw2h hx3l hw3h (by linarith [hx4l]) hx4h hx5l hw5h (by linarith [hx6l]) hx6h
  have hΔy : (50:ℝ) ≤ deltaY y1 y2 y3 y4 y5 y6 := hΔ
  have hcf00 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 (y1*y1) (4) (4) (6.0688) (4) (6.0688)) ^ 2 := ztgline_0101_lllll (y1*y1) hx1l hx1h
  have hcf01 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.0688) (4) (8) - (64/25) * (deltaX4 (y1*y1) (4) (4) (6.0688) (4) (8)) ^ 2 := ztgline_0101_llllh (y1*y1) hx1l hx1h
  have hcf02 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 (y1*y1) (4) (4) (6.0688) (6.3504) (6.0688)) ^ 2 := ztgline_0101_lllhl (y1*y1) hx1l hx1h
  have hcf03 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 (y1*y1) (4) (4) (6.0688) (6.3504) (8)) ^ 2 := ztgline_0101_lllhh (y1*y1) hx1l hx1h
  have hcf04 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (8) (4) (6.0688) - (64/25) * (deltaX4 (y1*y1) (4) (4) (8) (4) (6.0688)) ^ 2 := ztgline_0101_llhll (y1*y1) hx1l hx1h
  have hcf05 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (8) (4) (8) - (64/25) * (deltaX4 (y1*y1) (4) (4) (8) (4) (8)) ^ 2 := ztgline_0101_llhlh (y1*y1) hx1l hx1h
  have hcf06 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 (y1*y1) (4) (4) (8) (6.3504) (6.0688)) ^ 2 := ztgline_0101_llhhl (y1*y1) hx1l hx1h
  have hcf07 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (8) (6.3504) (8) - (64/25) * (deltaX4 (y1*y1) (4) (4) (8) (6.3504) (8)) ^ 2 := ztgline_0101_llhhh (y1*y1) hx1l hx1h
  have hcf08 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.0688) (4) (6.0688)) ^ 2 := ztgline_0101_lhlll (y1*y1) hx1l hx1h
  have hcf09 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.0688) (4) (8) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.0688) (4) (8)) ^ 2 := ztgline_0101_lhllh (y1*y1) hx1l hx1h
  have hcf10 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.0688) (6.3504) (6.0688)) ^ 2 := ztgline_0101_lhlhl (y1*y1) hx1l hx1h
  have hcf11 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.0688) (6.3504) (8)) ^ 2 := ztgline_0101_lhlhh (y1*y1) hx1l hx1h
  have hcf12 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (8) (4) (6.0688) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (8) (4) (6.0688)) ^ 2 := ztgline_0101_lhhll (y1*y1) hx1l hx1h
  have hcf13 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (8) (4) (8) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (8) (4) (8)) ^ 2 := ztgline_0101_lhhlh (y1*y1) hx1l hx1h
  have hcf14 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (8) (6.3504) (6.0688)) ^ 2 := ztgline_0101_lhhhl (y1*y1) hx1l hx1h
  have hcf15 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (8) (6.3504) (8) - (64/25) * (deltaX4 (y1*y1) (4) (6.3504) (8) (6.3504) (8)) ^ 2 := ztgline_0101_lhhhh (y1*y1) hx1l hx1h
  have hcf16 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.0688) (4) (6.0688)) ^ 2 := ztgline_0101_hllll (y1*y1) hx1l hx1h
  have hcf17 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.0688) (4) (8) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.0688) (4) (8)) ^ 2 := ztgline_0101_hlllh (y1*y1) hx1l hx1h
  have hcf18 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.0688) (6.3504) (6.0688)) ^ 2 := ztgline_0101_hllhl (y1*y1) hx1l hx1h
  have hcf19 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.0688) (6.3504) (8)) ^ 2 := ztgline_0101_hllhh (y1*y1) hx1l hx1h
  have hcf20 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (8) (4) (6.0688) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (8) (4) (6.0688)) ^ 2 := ztgline_0101_hlhll (y1*y1) hx1l hx1h
  have hcf21 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (8) (4) (8) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (8) (4) (8)) ^ 2 := ztgline_0101_hlhlh (y1*y1) hx1l hx1h
  have hcf22 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (8) (6.3504) (6.0688)) ^ 2 := ztgline_0101_hlhhl (y1*y1) hx1l hx1h
  have hcf23 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (8) (6.3504) (8) - (64/25) * (deltaX4 (y1*y1) (6.3504) (4) (8) (6.3504) (8)) ^ 2 := ztgline_0101_hlhhh (y1*y1) hx1l hx1h
  have hcf24 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.0688) (4) (6.0688) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.0688) (4) (6.0688)) ^ 2 := ztgline_0101_hhlll (y1*y1) hx1l hx1h
  have hcf25 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.0688) (4) (8) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.0688) (4) (8)) ^ 2 := ztgline_0101_hhllh (y1*y1) hx1l hx1h
  have hcf26 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.0688) (6.3504) (6.0688) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.0688) (6.3504) (6.0688)) ^ 2 := ztgline_0101_hhlhl (y1*y1) hx1l hx1h
  have hcf27 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.0688) (6.3504) (8) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.0688) (6.3504) (8)) ^ 2 := ztgline_0101_hhlhh (y1*y1) hx1l hx1h
  have hcf28 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (8) (4) (6.0688) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (8) (4) (6.0688)) ^ 2 := ztgline_0101_hhhll (y1*y1) hx1l hx1h
  have hcf29 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (8) (4) (8) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (8) (4) (8)) ^ 2 := ztgline_0101_hhhlh (y1*y1) hx1l hx1h
  have hcf30 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (8) (6.3504) (6.0688) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (8) (6.3504) (6.0688)) ^ 2 := ztgline_0101_hhhhl (y1*y1) hx1l hx1h
  have hcf31 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (8) (6.3504) (8) - (64/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (8) (6.3504) (8)) ^ 2 := ztgline_0101_hhhhh (y1*y1) hx1l hx1h
  have hz : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
      - (64/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 :=
    ztgG_box5 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) (64/25)
      (by norm_num) (mul_self_nonneg y1)
      (4) (6.3504) (4) (6.3504) (6.0688) (8) (4) (6.3504) (6.0688) (8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hx2l hx2h hx3l hx3h hx4l hx4h hx5l hx5h hx6l hx6h
      hcf00 hcf01 hcf02 hcf03 hcf04 hcf05 hcf06 hcf07 hcf08 hcf09 hcf10 hcf11 hcf12 hcf13 hcf14 hcf15 hcf16 hcf17 hcf18 hcf19 hcf20 hcf21 hcf22 hcf23 hcf24 hcf25 hcf26 hcf27 hcf28 hcf29 hcf30 hcf31
  have h41 : (0:ℝ) < 4 * (y1 * y1) :=
    mul_pos (by norm_num) (mul_pos (hy1pos) (hy1pos))
  have hdY : (0:ℝ) < deltaY y1 y2 y3 y4 y5 y6 := by linarith [hΔy]
  have hX : (0:ℝ) < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) :=
    Real.sqrt_pos.mpr (mul_pos h41 hdY)
  have hz' : (0:ℝ) ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6
      - (64/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 := hz
  have hlt : (8 / 5:ℝ) * |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)|
      ≤ Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) := by
    have hsq : ((8 / 5:ℝ) * deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2
        ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6 := by
      have e : ((8 / 5:ℝ) * deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2
          = (64/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 := by
        rw [mul_pow]
        norm_num
      rw [e]
      linarith [hz']
    have hw := Real.abs_le_sqrt hsq
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 8 / 5)] at hw
    exact hw
  exact le_trans ztg_arctan_8_5_lb (ztg_dihY_ge_arctan (by norm_num) hX hlt)
/-- **dihY lower bound** for the `ZTGIJCF4 0_0_1_1` debt box:
`0.875 ≤ dihY` (via `arctan 6 / 5` with the polynomial certificate above).
Consumed with `γ4 ≥ 0.05` (trio) / `γ4 ≥ 0.065` (`0011`) by the Assembly
wiring to close the decoupled route. -/
theorem ztg_dihY_0_0_1_1 {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1l : 2 * hminus ≤ y1) (h1h : y1 ≤ 2 * hplus)
    (h2l : 2 ≤ y2) (h2h : y2 ≤ 2 * hminus)
    (h3l : bank_ZTGIJCF4lo 0 ≤ y3) (h3h : y3 ≤ bank_ZTGIJCF4hi 0)
    (h4l : bank_ZTGIJCF4lo 0 ≤ y4) (h4h : y4 ≤ bank_ZTGIJCF4hi 0)
    (h5l : bank_ZTGIJCF4lo 1 ≤ y5) (h5h : y5 ≤ bank_ZTGIJCF4hi 1)
    (h6l : bank_ZTGIJCF4lo 1 ≤ y6) (h6h : y6 ≤ bank_ZTGIJCF4hi 1) :
    (0.875:ℝ) ≤ dihY y1 y2 y3 y4 y5 y6 := by
  have hmi : (1.23175:ℝ) ≤ hminus := Kepler.NliBanks7.hminus_ge_123175
  have hmiu : hminus < (1.26:ℝ) := mi_hminus_lt_h0
  have hy1p : (0:ℝ) ≤ y1 := by linarith [hmi, h1l]
  have hy1pos : (0:ℝ) < y1 := by linarith [hmi, h1l]
  have hx1l : (6.0688) ≤ y1 * y1 := by
    have h246 : (4927/2000:ℝ) ≤ y1 := by linarith [hmi, h1l]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy1p), sq_nonneg (y1 - 4927/2000)]
  have hx1h : y1 * y1 ≤ 7.02674064 := Kepler.NliBanks3.sq_le_hplus y1 (hy1p) (h1h)
  have h3two : (2:ℝ) ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3hm : y3 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h3h
  have hy3p : (0:ℝ) ≤ y3 := by linarith [h3two]
  have hx3l : (4) ≤ y3 * y3 := Kepler.NliBanks3.sq_ge_4 y3 (h3two)
  have hx3h : y3 * y3 ≤ (6.3504) := by
    have h252 : y3 ≤ (63/25:ℝ) := by linarith [h3hm, hmiu]
    nlinarith [mul_nonneg (hy3p) (sub_nonneg.mpr h252), sq_nonneg (y3 - 63/25)]
  have hw3h : y3 * y3 ≤ (8) := by linarith [hx3h]
  have h4two : (2:ℝ) ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4hm : y4 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h4h
  have hy4p : (0:ℝ) ≤ y4 := by linarith [h4two]
  have hx4l : (4) ≤ y4 * y4 := Kepler.NliBanks3.sq_ge_4 y4 (h4two)
  have hx4h : y4 * y4 ≤ (6.3504) := by
    have h252 : y4 ≤ (63/25:ℝ) := by linarith [h4hm, hmiu]
    nlinarith [mul_nonneg (hy4p) (sub_nonneg.mpr h252), sq_nonneg (y4 - 63/25)]
  have hw4h : y4 * y4 ≤ (8) := by linarith [hx4h]
  have h5hm : (2:ℝ) * hminus ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5s8 : y5 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h5h
  have hy5p : (0:ℝ) ≤ y5 := by linarith [hmi, h5hm]
  have hx5l : (6.0688) ≤ y5 * y5 := by
    have h246 : (4927/2000:ℝ) ≤ y5 := by linarith [hmi, h5hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy5p), sq_nonneg (y5 - 4927/2000)]
  have hx5h : y5 * y5 ≤ (8) := Kepler.NliBanks3.sq_le_8 y5 (hy5p) (h5s8)
  have hw5l : (6.0650528:ℝ) ≤ y5 * y5 := by linarith [hx5l]
  have h6hm : (2:ℝ) * hminus ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6s8 : y6 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h6h
  have hy6p : (0:ℝ) ≤ y6 := by linarith [hmi, h6hm]
  have hx6l : (6.0688) ≤ y6 * y6 := by
    have h246 : (4927/2000:ℝ) ≤ y6 := by linarith [hmi, h6hm]
    nlinarith [mul_nonneg (sub_nonneg.mpr h246) (hy6p), sq_nonneg (y6 - 4927/2000)]
  have hx6h : y6 * y6 ≤ (8) := Kepler.NliBanks3.sq_le_8 y6 (hy6p) (h6s8)
  have hw6l : (6.0650528:ℝ) ≤ y6 * y6 := by linarith [hx6l]
  have hy2p : (0:ℝ) ≤ y2 := by linarith [h2l]
  have hx2l : (4) ≤ y2 * y2 := Kepler.NliBanks3.sq_ge_4 y2 (h2l)
  have hx2h : y2 * y2 ≤ (6.3504) := by
    have h252 : y2 ≤ (63/25:ℝ) := by linarith [h2h, hmiu]
    nlinarith [mul_nonneg (hy2p) (sub_nonneg.mpr h252), sq_nonneg (y2 - 63/25)]
  have hw2h : y2 * y2 ≤ (8) := by linarith [hx2h]
  have hw1l : (6.0650528:ℝ) ≤ y1 * y1 := by linarith [hx1l]
  have hw3l : (4) ≤ y3 * y3 := hx3l
  have hw4l : (4) ≤ y4 * y4 := hx4l
  have hw5h : y5 * y5 ≤ (8) := hx5h
  have hw6h : y6 * y6 ≤ (8) := hx6h
  have hΔ : (50:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    Kepler.NliBanks5.dX_box_ge_wide (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
      (by linarith [hx1l]) hx1h hx2l hw2h hx3l hw3h hx4l hw4h (by linarith [hx5l]) hx5h (by linarith [hx6l]) hx6h
  have hΔy : (50:ℝ) ≤ deltaY y1 y2 y3 y4 y5 y6 := hΔ
  have hcf00 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 (y1*y1) (4) (4) (4) (6.0688) (6.0688)) ^ 2 := ztgline_0011_lllll (y1*y1) hx1l hx1h
  have hcf01 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (4) (6.0688) (8) - (36/25) * (deltaX4 (y1*y1) (4) (4) (4) (6.0688) (8)) ^ 2 := ztgline_0011_llllh (y1*y1) hx1l hx1h
  have hcf02 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (4) (8) (6.0688) - (36/25) * (deltaX4 (y1*y1) (4) (4) (4) (8) (6.0688)) ^ 2 := ztgline_0011_lllhl (y1*y1) hx1l hx1h
  have hcf03 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (4) (8) (8) - (36/25) * (deltaX4 (y1*y1) (4) (4) (4) (8) (8)) ^ 2 := ztgline_0011_lllhh (y1*y1) hx1l hx1h
  have hcf04 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 (y1*y1) (4) (4) (6.3504) (6.0688) (6.0688)) ^ 2 := ztgline_0011_llhll (y1*y1) hx1l hx1h
  have hcf05 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 (y1*y1) (4) (4) (6.3504) (6.0688) (8)) ^ 2 := ztgline_0011_llhlh (y1*y1) hx1l hx1h
  have hcf06 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 (y1*y1) (4) (4) (6.3504) (8) (6.0688)) ^ 2 := ztgline_0011_llhhl (y1*y1) hx1l hx1h
  have hcf07 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (4) (6.3504) (8) (8) - (36/25) * (deltaX4 (y1*y1) (4) (4) (6.3504) (8) (8)) ^ 2 := ztgline_0011_llhhh (y1*y1) hx1l hx1h
  have hcf08 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 (y1*y1) (4) (6.3504) (4) (6.0688) (6.0688)) ^ 2 := ztgline_0011_lhlll (y1*y1) hx1l hx1h
  have hcf09 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (4) (6.0688) (8) - (36/25) * (deltaX4 (y1*y1) (4) (6.3504) (4) (6.0688) (8)) ^ 2 := ztgline_0011_lhllh (y1*y1) hx1l hx1h
  have hcf10 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (4) (8) (6.0688) - (36/25) * (deltaX4 (y1*y1) (4) (6.3504) (4) (8) (6.0688)) ^ 2 := ztgline_0011_lhlhl (y1*y1) hx1l hx1h
  have hcf11 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (4) (8) (8) - (36/25) * (deltaX4 (y1*y1) (4) (6.3504) (4) (8) (8)) ^ 2 := ztgline_0011_lhlhh (y1*y1) hx1l hx1h
  have hcf12 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.3504) (6.0688) (6.0688)) ^ 2 := ztgline_0011_lhhll (y1*y1) hx1l hx1h
  have hcf13 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.3504) (6.0688) (8)) ^ 2 := ztgline_0011_lhhlh (y1*y1) hx1l hx1h
  have hcf14 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.3504) (8) (6.0688)) ^ 2 := ztgline_0011_lhhhl (y1*y1) hx1l hx1h
  have hcf15 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (4) (6.3504) (6.3504) (8) (8) - (36/25) * (deltaX4 (y1*y1) (4) (6.3504) (6.3504) (8) (8)) ^ 2 := ztgline_0011_lhhhh (y1*y1) hx1l hx1h
  have hcf16 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 (y1*y1) (6.3504) (4) (4) (6.0688) (6.0688)) ^ 2 := ztgline_0011_hllll (y1*y1) hx1l hx1h
  have hcf17 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (4) (6.0688) (8) - (36/25) * (deltaX4 (y1*y1) (6.3504) (4) (4) (6.0688) (8)) ^ 2 := ztgline_0011_hlllh (y1*y1) hx1l hx1h
  have hcf18 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (4) (8) (6.0688) - (36/25) * (deltaX4 (y1*y1) (6.3504) (4) (4) (8) (6.0688)) ^ 2 := ztgline_0011_hllhl (y1*y1) hx1l hx1h
  have hcf19 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (4) (8) (8) - (36/25) * (deltaX4 (y1*y1) (6.3504) (4) (4) (8) (8)) ^ 2 := ztgline_0011_hllhh (y1*y1) hx1l hx1h
  have hcf20 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.3504) (6.0688) (6.0688)) ^ 2 := ztgline_0011_hlhll (y1*y1) hx1l hx1h
  have hcf21 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.3504) (6.0688) (8)) ^ 2 := ztgline_0011_hlhlh (y1*y1) hx1l hx1h
  have hcf22 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.3504) (8) (6.0688)) ^ 2 := ztgline_0011_hlhhl (y1*y1) hx1l hx1h
  have hcf23 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (4) (6.3504) (8) (8) - (36/25) * (deltaX4 (y1*y1) (6.3504) (4) (6.3504) (8) (8)) ^ 2 := ztgline_0011_hlhhh (y1*y1) hx1l hx1h
  have hcf24 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (4) (6.0688) (6.0688) - (36/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (4) (6.0688) (6.0688)) ^ 2 := ztgline_0011_hhlll (y1*y1) hx1l hx1h
  have hcf25 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (4) (6.0688) (8) - (36/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (4) (6.0688) (8)) ^ 2 := ztgline_0011_hhllh (y1*y1) hx1l hx1h
  have hcf26 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (4) (8) (6.0688) - (36/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (4) (8) (6.0688)) ^ 2 := ztgline_0011_hhlhl (y1*y1) hx1l hx1h
  have hcf27 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (4) (8) (8) - (36/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (4) (8) (8)) ^ 2 := ztgline_0011_hhlhh (y1*y1) hx1l hx1h
  have hcf28 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.3504) (6.0688) (6.0688) - (36/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.3504) (6.0688) (6.0688)) ^ 2 := ztgline_0011_hhhll (y1*y1) hx1l hx1h
  have hcf29 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.3504) (6.0688) (8) - (36/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.3504) (6.0688) (8)) ^ 2 := ztgline_0011_hhhlh (y1*y1) hx1l hx1h
  have hcf30 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.3504) (8) (6.0688) - (36/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.3504) (8) (6.0688)) ^ 2 := ztgline_0011_hhhhl (y1*y1) hx1l hx1h
  have hcf31 : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (6.3504) (6.3504) (6.3504) (8) (8) - (36/25) * (deltaX4 (y1*y1) (6.3504) (6.3504) (6.3504) (8) (8)) ^ 2 := ztgline_0011_hhhhh (y1*y1) hx1l hx1h
  have hz : (0:ℝ) ≤ 4 * (y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)
      - (36/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 :=
    ztgG_box5 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) (36/25)
      (by norm_num) (mul_self_nonneg y1)
      (4) (6.3504) (4) (6.3504) (4) (6.3504) (6.0688) (8) (6.0688) (8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hx2l hx2h hx3l hx3h hx4l hx4h hx5l hx5h hx6l hx6h
      hcf00 hcf01 hcf02 hcf03 hcf04 hcf05 hcf06 hcf07 hcf08 hcf09 hcf10 hcf11 hcf12 hcf13 hcf14 hcf15 hcf16 hcf17 hcf18 hcf19 hcf20 hcf21 hcf22 hcf23 hcf24 hcf25 hcf26 hcf27 hcf28 hcf29 hcf30 hcf31
  have h41 : (0:ℝ) < 4 * (y1 * y1) :=
    mul_pos (by norm_num) (mul_pos (hy1pos) (hy1pos))
  have hdY : (0:ℝ) < deltaY y1 y2 y3 y4 y5 y6 := by linarith [hΔy]
  have hX : (0:ℝ) < Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) :=
    Real.sqrt_pos.mpr (mul_pos h41 hdY)
  have hz' : (0:ℝ) ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6
      - (36/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 := hz
  have hlt : (6 / 5:ℝ) * |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)|
      ≤ Real.sqrt (4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6) := by
    have hsq : ((6 / 5:ℝ) * deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2
        ≤ 4 * (y1 * y1) * deltaY y1 y2 y3 y4 y5 y6 := by
      have e : ((6 / 5:ℝ) * deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2
          = (36/25) * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) ^ 2 := by
        rw [mul_pow]
        norm_num
      rw [e]
      linarith [hz']
    have hw := Real.abs_le_sqrt hsq
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6 / 5)] at hw
    exact hw
  exact le_trans ztg_arctan_6_5_lb (ztg_dihY_ge_arctan (by norm_num) hX hlt)

/-! ## Axiom audit (house style): every declaration of this module,
individually printed (no truncation). -/
#print axioms ztg_dihY_1_1_0_0
#print axioms ztg_dihY_0_1_1_0
#print axioms ztg_dihY_0_1_0_1
#print axioms ztg_dihY_0_0_1_1
#print axioms ztgG_box5
#print axioms ztdih_quad2
#print axioms ztdih_step2
#print axioms ztdih_quad3
#print axioms ztdih_step3
#print axioms ztdih_quad4
#print axioms ztdih_step4
#print axioms ztdih_quad5
#print axioms ztdih_step5
#print axioms ztdih_quad6
#print axioms ztdih_step6
#print axioms ztgline_1100_lllll
#print axioms ztgline_1100_llllh
#print axioms ztgline_1100_lllhl
#print axioms ztgline_1100_lllhh
#print axioms ztgline_1100_llhll
#print axioms ztgline_1100_llhlh
#print axioms ztgline_1100_llhhl
#print axioms ztgline_1100_llhhh
#print axioms ztgline_1100_lhlll
#print axioms ztgline_1100_lhllh
#print axioms ztgline_1100_lhlhl
#print axioms ztgline_1100_lhlhh
#print axioms ztgline_1100_lhhll
#print axioms ztgline_1100_lhhlh
#print axioms ztgline_1100_lhhhl
#print axioms ztgline_1100_lhhhh
#print axioms ztgline_1100_hllll
#print axioms ztgline_1100_hlllh
#print axioms ztgline_1100_hllhl
#print axioms ztgline_1100_hllhh
#print axioms ztgline_1100_hlhll
#print axioms ztgline_1100_hlhlh
#print axioms ztgline_1100_hlhhl
#print axioms ztgline_1100_hlhhh
#print axioms ztgline_1100_hhlll
#print axioms ztgline_1100_hhllh
#print axioms ztgline_1100_hhlhl
#print axioms ztgline_1100_hhlhh
#print axioms ztgline_1100_hhhll
#print axioms ztgline_1100_hhhlh
#print axioms ztgline_1100_hhhhl
#print axioms ztgline_1100_hhhhh
#print axioms ztgline_0110_lllll
#print axioms ztgline_0110_llllh
#print axioms ztgline_0110_lllhl
#print axioms ztgline_0110_lllhh
#print axioms ztgline_0110_llhll
#print axioms ztgline_0110_llhlh
#print axioms ztgline_0110_llhhl
#print axioms ztgline_0110_llhhh
#print axioms ztgline_0110_lhlll
#print axioms ztgline_0110_lhllh
#print axioms ztgline_0110_lhlhl
#print axioms ztgline_0110_lhlhh
#print axioms ztgline_0110_lhhll
#print axioms ztgline_0110_lhhlh
#print axioms ztgline_0110_lhhhl
#print axioms ztgline_0110_lhhhh
#print axioms ztgline_0110_hllll
#print axioms ztgline_0110_hlllh
#print axioms ztgline_0110_hllhl
#print axioms ztgline_0110_hllhh
#print axioms ztgline_0110_hlhll
#print axioms ztgline_0110_hlhlh
#print axioms ztgline_0110_hlhhl
#print axioms ztgline_0110_hlhhh
#print axioms ztgline_0110_hhlll
#print axioms ztgline_0110_hhllh
#print axioms ztgline_0110_hhlhl
#print axioms ztgline_0110_hhlhh
#print axioms ztgline_0110_hhhll
#print axioms ztgline_0110_hhhlh
#print axioms ztgline_0110_hhhhl
#print axioms ztgline_0110_hhhhh
#print axioms ztgline_0101_lllll
#print axioms ztgline_0101_llllh
#print axioms ztgline_0101_lllhl
#print axioms ztgline_0101_lllhh
#print axioms ztgline_0101_llhll
#print axioms ztgline_0101_llhlh
#print axioms ztgline_0101_llhhl
#print axioms ztgline_0101_llhhh
#print axioms ztgline_0101_lhlll
#print axioms ztgline_0101_lhllh
#print axioms ztgline_0101_lhlhl
#print axioms ztgline_0101_lhlhh
#print axioms ztgline_0101_lhhll
#print axioms ztgline_0101_lhhlh
#print axioms ztgline_0101_lhhhl
#print axioms ztgline_0101_lhhhh
#print axioms ztgline_0101_hllll
#print axioms ztgline_0101_hlllh
#print axioms ztgline_0101_hllhl
#print axioms ztgline_0101_hllhh
#print axioms ztgline_0101_hlhll
#print axioms ztgline_0101_hlhlh
#print axioms ztgline_0101_hlhhl
#print axioms ztgline_0101_hlhhh
#print axioms ztgline_0101_hhlll
#print axioms ztgline_0101_hhllh
#print axioms ztgline_0101_hhlhl
#print axioms ztgline_0101_hhlhh
#print axioms ztgline_0101_hhhll
#print axioms ztgline_0101_hhhlh
#print axioms ztgline_0101_hhhhl
#print axioms ztgline_0101_hhhhh
#print axioms ztgline_0011_lllll
#print axioms ztgline_0011_llllh
#print axioms ztgline_0011_lllhl
#print axioms ztgline_0011_lllhh
#print axioms ztgline_0011_llhll
#print axioms ztgline_0011_llhlh
#print axioms ztgline_0011_llhhl
#print axioms ztgline_0011_llhhh
#print axioms ztgline_0011_lhlll
#print axioms ztgline_0011_lhllh
#print axioms ztgline_0011_lhlhl
#print axioms ztgline_0011_lhlhh
#print axioms ztgline_0011_lhhll
#print axioms ztgline_0011_lhhlh
#print axioms ztgline_0011_lhhhl
#print axioms ztgline_0011_lhhhh
#print axioms ztgline_0011_hllll
#print axioms ztgline_0011_hlllh
#print axioms ztgline_0011_hllhl
#print axioms ztgline_0011_hllhh
#print axioms ztgline_0011_hlhll
#print axioms ztgline_0011_hlhlh
#print axioms ztgline_0011_hlhhl
#print axioms ztgline_0011_hlhhh
#print axioms ztgline_0011_hhlll
#print axioms ztgline_0011_hhllh
#print axioms ztgline_0011_hhlhl
#print axioms ztgline_0011_hhlhh
#print axioms ztgline_0011_hhhll
#print axioms ztgline_0011_hhhlh
#print axioms ztgline_0011_hhhhl
#print axioms ztgline_0011_hhhhh

end Kepler.NliBanksZTGIJCF4Dih