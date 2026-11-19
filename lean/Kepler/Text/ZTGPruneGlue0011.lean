/-
Kepler.Text.ZTGPruneGlue0011 — lane ztg-bernstein-pilot-w1 (2026-11-19).
The two monotone-prune glue steps for the ZTGIJCF4 0_0_1_1 debt
(q = 36/25), closing the gap between the landed pruned-face leaf
`BernsteinLeaf0011.ztgG_leaf_0_0_1_1` (commit 9a4a9dc6) and the ORIGINAL
debt-box obligation (no pinned x1/x4):

  0 <= 4*x1*deltaX x1 x2 x3 x4 x5 x6
       - (36/25)*(deltaX4 x1 x2 x3 x4 x5 x6)^2

on x1 in [3793/625, 43917129/6250000], x2, x3, x4 in [4, 3969/625],
x5, x6 in [3793/625, 8]  (the bank's `ztgG_box5`-shape conclusion,
lean/Kepler/NliBanksZTGIJCF4Dih.lean).

Glue piece A (x4 prune, on the x1 = 3793/625 face): `ztgG` is a
univariate QUADRATIC in x4 with leading coefficient -4*a^2*(1+q) < 0 and
the exact difference identity (`ztgG_quad_diff_x4`, one `ring`)

  g(x4) - g(4) = (x4-4) * 4*a*(1+q) * (ztgd0 - a*(4+x4)),

so g is nondecreasing in x4 on [4, 3969/625] once `ztgd0 - a*(4+x4) >= 0`;
that expression is multi-affine in (x2, x3, x5, x6), certificate = its 16
corner values (`ztgW_nonneg`).  This replaces the engine's 162-value
first-difference evidence with 16 exact rationals (weaker, sufficient
condition: the difference identity needs the average slope, not the
pointwise derivative).

Glue piece B (x1 prune, on the full box): the x1-slot derivative closed
form (`ztgG_hasDerivAt_x1`, built from the in-tree `g4dDX1` =
d deltaX/d x1, Gamma4Deriv.lean) plus `monotoneOn_of_hasDerivWithinAt_nonneg`;
the derivative-sign certificate is the 972-constant Bernstein tensor of
Dgrad (ZTGDgrad0011.dgrad_nonneg, separate generated file).

Assembly: 0 <= g(3793/625, x2, x3, 4, x5, x6)  [the landed leaf]
          <= g(3793/625, x2, x3, x4, x5, x6)  [piece A]
          <= g(x1, x2, x3, x4, x5, x6)        [piece B].

Data provenance: bernstein-representative-w1 (engine, exact rational),
verified symbolically in this lane's work/verify_glue.py and
work/verify_peel_n.py (peel_n identities, quad-diff identity, W corners).
No sorry/axiom/native_decide; every declaration axiom-audited below.
-/
import Mathlib
import Kepler.Text.SphereKit
import Kepler.Text.Gamma4Deriv
import Kepler.Text.BernsteinLeaf0011
import Kepler.Text.ZTGDgrad0011

set_option maxHeartbeats 4000000

namespace Kepler.Text.ZTGPruneGlue0011

/-! ## Derivative transports (value normalization without defeq fights) -/

theorem hasDerivAt_of_eq {f : ℝ → ℝ} {v w t : ℝ} (h : HasDerivAt f v t)
    (hw : v = w) : HasDerivAt f w t := by
  subst hw; exact h

/-- Quadratic Horner derivative: clean statement, composed proof, value
normalized once by `ring` through `hasDerivAt_of_eq`. -/
theorem hasDerivAt_quad (C L Qc t : ℝ) :
    HasDerivAt (fun s => C + (L * s + Qc * (s * s)))
      (L + (Qc + Qc) * t) t := by
  have hC : HasDerivAt (fun _ : ℝ => C) (0:ℝ) t := hasDerivAt_const t C
  have hL : HasDerivAt (fun s : ℝ => L * s) (L * 1) t :=
    (hasDerivAt_id t).const_mul L
  have hsq : HasDerivAt (fun s : ℝ => s * s) (1 * t + t * 1) t :=
    (hasDerivAt_id t).mul (hasDerivAt_id t)
  have hQ : HasDerivAt (fun s : ℝ => Qc * (s * s)) (Qc * (1 * t + t * 1)) t :=
    hsq.const_mul Qc
  have h := hC.add (hL.add hQ)
  -- PR-28 pattern: the composed Pi-literal must be bridged to the single
  -- lambda by an explicit function equality before the value transport.
  have hfun : (fun s : ℝ => C + (L * s + Qc * (s * s)))
      = (fun _ : ℝ => C) + ((fun s : ℝ => L * s)
        + (fun s : ℝ => Qc * (s * s))) := by
    funext s
    simp only [Pi.add_apply]
  rw [hfun]
  exact hasDerivAt_of_eq h (by ring)

/-! ## Slot-1 quadratic forms of `deltaX` and `deltaX4` -/

noncomputable def dxqC (x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x2 * x5 * (-x2 + x3 + x4 - x5 + x6) + x3 * x6 * (x2 - x3 + x4 + x5 - x6)
    - x2 * x3 * x4 - x4 * x5 * x6

noncomputable def dxqL (x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x4 * (x2 + x3 - x4 + x5 + x6) + x2 * x5 + x3 * x6 - x3 * x5 - x2 * x6

noncomputable def dxq4C (x2 x3 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6

noncomputable def dxq4L (x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x2 + x3 - 2 * x4 + x5 + x6

theorem deltaX_quad_x1 (s x2 x3 x4 x5 x6 : ℝ) :
    deltaX s x2 x3 x4 x5 x6
      = dxqC x2 x3 x4 x5 x6
        + (dxqL x2 x3 x4 x5 x6 * s + (-x4) * (s * s)) := by
  simp only [deltaX, dxqC, dxqL]
  ring

theorem deltaX4_quad_x1 (s x2 x3 x4 x5 x6 : ℝ) :
    deltaX4 s x2 x3 x4 x5 x6
      = dxq4C x2 x3 x5 x6
        + (dxq4L x2 x3 x4 x5 x6 * s + (-1) * (s * s)) := by
  simp only [deltaX4, dxq4C, dxq4L]
  ring

/-- The in-tree partial `g4dDX1` is the linear coefficient of the slot-1
quadratic form of `deltaX` (one `ring`). -/
theorem g4dDX1_eq_dxqL (s x2 x3 x4 x5 x6 : ℝ) :
    g4dDX1 s x2 x3 x4 x5 x6
      = dxqL x2 x3 x4 x5 x6 - 2 * x4 * s := by
  simp only [g4dDX1, dxqL]
  ring

/-! ## The x1-slot derivative of the obligation polynomial -/

/-- Closed form: d/dx1 [4*x1*deltaX - q*deltaX4^2] = Dgrad, with the
in-tree partials `g4dDX1` (= d deltaX/d x1) and -2*x1+x2+x3-2*x4+x5+x6
(= d deltaX4/d x1). -/
theorem ztgG_hasDerivAt_x1 (q t x2 x3 x4 x5 x6 : ℝ) :
    HasDerivAt (fun s => 4 * s * deltaX s x2 x3 x4 x5 x6
        - q * (deltaX4 s x2 x3 x4 x5 x6) ^ 2)
      (4 * deltaX t x2 x3 x4 x5 x6
        + 4 * t * g4dDX1 t x2 x3 x4 x5 x6
        - 2 * q * deltaX4 t x2 x3 x4 x5 x6
          * (-2 * t + x2 + x3 - 2 * x4 + x5 + x6)) t := by
  have hΔ : HasDerivAt (fun s => deltaX s x2 x3 x4 x5 x6)
      (dxqL x2 x3 x4 x5 x6 - 2 * x4 * t) t := by
    have hf : (fun s => deltaX s x2 x3 x4 x5 x6)
        = fun s => dxqC x2 x3 x4 x5 x6
            + (dxqL x2 x3 x4 x5 x6 * s + (-x4) * (s * s)) := by
      funext s; exact deltaX_quad_x1 s x2 x3 x4 x5 x6
    rw [hf]
    exact hasDerivAt_of_eq
      (hasDerivAt_quad (dxqC x2 x3 x4 x5 x6) (dxqL x2 x3 x4 x5 x6)
        (-x4) t) (by ring)
  have hΔ4 : HasDerivAt (fun s => deltaX4 s x2 x3 x4 x5 x6)
      (dxq4L x2 x3 x4 x5 x6 - 2 * t) t := by
    have hf : (fun s => deltaX4 s x2 x3 x4 x5 x6)
        = fun s => dxq4C x2 x3 x5 x6
            + (dxq4L x2 x3 x4 x5 x6 * s + (-1) * (s * s)) := by
      funext s; exact deltaX4_quad_x1 s x2 x3 x4 x5 x6
    rw [hf]
    exact hasDerivAt_of_eq
      (hasDerivAt_quad (dxq4C x2 x3 x5 x6) (dxq4L x2 x3 x4 x5 x6)
        (-1) t) (by ring)
  have h4s : HasDerivAt (fun s : ℝ => 4 * s) (4 * 1) t :=
    (hasDerivAt_id t).const_mul 4
  have hmul : HasDerivAt
      (fun s => 4 * s * deltaX s x2 x3 x4 x5 x6)
      ((4 * 1) * deltaX t x2 x3 x4 x5 x6
        + 4 * t * (dxqL x2 x3 x4 x5 x6 - 2 * x4 * t)) t :=
    h4s.mul hΔ
  have hΔ4sq : HasDerivAt (fun s => (deltaX4 s x2 x3 x4 x5 x6) ^ 2)
      (2 * (deltaX4 t x2 x3 x4 x5 x6) ^ (2 - 1)
        * (dxq4L x2 x3 x4 x5 x6 - 2 * t)) t :=
    hΔ4.pow 2
  have hQ : HasDerivAt
      (fun s => q * (deltaX4 s x2 x3 x4 x5 x6) ^ 2)
      (q * (2 * (deltaX4 t x2 x3 x4 x5 x6) ^ (2 - 1)
        * (dxq4L x2 x3 x4 x5 x6 - 2 * t))) t :=
    hΔ4sq.const_mul q
  have hsub := hmul.sub hQ
  have hfun2 : (fun s : ℝ => 4 * s * deltaX s x2 x3 x4 x5 x6
        - q * (deltaX4 s x2 x3 x4 x5 x6) ^ 2)
      = (fun s : ℝ => 4 * s * deltaX s x2 x3 x4 x5 x6)
        - (fun s : ℝ => q * (deltaX4 s x2 x3 x4 x5 x6) ^ 2) := by
    funext s
    simp only [Pi.sub_apply]
  rw [hfun2]
  exact hasDerivAt_of_eq hsub (by
    simp only [g4dDX1, dxqL, dxq4L]
    ring)

/-! ## The x4-prune quadratic difference identity -/

/-- The x1-face value of `deltaX4`'s linear part: also the constant term
of `deltaX4` in its x4-slot affine form. -/
noncomputable def ztgd0 (a x2 x3 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 + x2 * x5 + x3 * x6 - x5 * x6 + a * (-a + x2 + x3 + x5 + x6)

/-- Exact quadratic difference: for every a, q the x4-slot difference of
the obligation polynomial factors through one affine bracket.  One
`ring` after the three unfolds. -/
theorem ztgG_quad_diff_x4 (a q x2 x3 t1 t2 x5 x6 : ℝ) :
    (4 * a * deltaX a x2 x3 t2 x5 x6
        - q * (deltaX4 a x2 x3 t2 x5 x6) ^ 2)
      - (4 * a * deltaX a x2 x3 t1 x5 x6
        - q * (deltaX4 a x2 x3 t1 x5 x6) ^ 2)
      = (t2 - t1) * (4 * a * (1 + q)
          * (ztgd0 a x2 x3 x5 x6 - a * (t1 + t2))) := by
  unfold deltaX deltaX4 ztgd0
  ring

/-- The certificate expression of the x4 prune on the x1-face:
`ztgd0 - a*(4 + 3969/625)` (multi-affine in x2, x3, x5, x6 up to the
constant). -/
noncomputable def ztgW (x2 x3 x5 x6 : ℝ) : ℝ :=
  ztgd0 (3793/625:ℝ) x2 x3 x5 x6
    - (3793/625:ℝ) * ((4:ℝ) + (3969/625:ℝ))

/-! ## The x4-prune certificate: W = ztgd0 - a*(4+BB) is multi-affine
in (x2, x3, x5, x6); its 16 corner values on the box are the
certificate (all positive, min 7143083/390625; exact rationals
from work/verify_glue.py; the multilinear-interpolation identity
is closed by one `ring`). -/
theorem ztgW_nonneg (x2 x3 x5 x6 : ℝ)
    (hx2l : (4:ℝ) ≤ x2) (hx2h : x2 ≤ (3969/625:ℝ))
    (hx3l : (4:ℝ) ≤ x3) (hx3h : x3 ≤ (3969/625:ℝ))
    (hx5l : (3793/625:ℝ) ≤ x5) (hx5h : x5 ≤ (8:ℝ))
    (hx6l : (3793/625:ℝ) ≤ x6) (hx6h : x6 ≤ (8:ℝ)) :
    (0:ℝ) ≤ ztgW x2 x3 x5 x6 := by
  have hbx2l : (0:ℝ) ≤ x2 - (4:ℝ) := by linarith
  have hbx2h : (0:ℝ) ≤ (3969/625:ℝ) - x2 := by linarith
  have hbx3l : (0:ℝ) ≤ x3 - (4:ℝ) := by linarith
  have hbx3h : (0:ℝ) ≤ (3969/625:ℝ) - x3 := by linarith
  have hbx5l : (0:ℝ) ≤ x5 - (3793/625:ℝ) := by linarith
  have hbx5h : (0:ℝ) ≤ (8:ℝ) - x5 := by linarith
  have hbx6l : (0:ℝ) ≤ x6 - (3793/625:ℝ) := by linarith
  have hbx6h : (0:ℝ) ≤ (8:ℝ) - x6 := by linarith
  have hs : (0:ℝ) ≤ ((3969/625:ℝ) - (4:ℝ)) ^ 2 * ((8:ℝ) - (3793/625:ℝ)) ^ 2 * ztgW x2 x3 x5 x6 := by
    have hId : ((3969/625:ℝ) - (4:ℝ)) ^ 2 * ((8:ℝ) - (3793/625:ℝ)) ^ 2 * ztgW x2 x3 x5 x6
      = ((3969/625:ℝ) - x2) * ((3969/625:ℝ) - x3) * ((8:ℝ) - x5) * ((8:ℝ) - x6) * (7143083/390625:ℝ)
        + ((3969/625:ℝ) - x2) * ((3969/625:ℝ) - x3) * ((8:ℝ) - x5) * (x6 - (3793/625:ℝ)) * (10160583/390625:ℝ)
        + ((3969/625:ℝ) - x2) * ((3969/625:ℝ) - x3) * (x5 - (3793/625:ℝ)) * ((8:ℝ) - x6) * (10160583/390625:ℝ)
        + ((3969/625:ℝ) - x2) * ((3969/625:ℝ) - x3) * (x5 - (3793/625:ℝ)) * (x6 - (3793/625:ℝ)) * (11721234/390625:ℝ)
        + ((3969/625:ℝ) - x2) * (x3 - (4:ℝ)) * ((8:ℝ) - x5) * ((8:ℝ) - x6) * (14614417/390625:ℝ)
        + ((3969/625:ℝ) - x2) * (x3 - (4:ℝ)) * ((8:ℝ) - x5) * (x6 - (3793/625:ℝ)) * (31048/625:ℝ)
        + ((3969/625:ℝ) - x2) * (x3 - (4:ℝ)) * (x5 - (3793/625:ℝ)) * ((8:ℝ) - x6) * (17631917/390625:ℝ)
        + ((3969/625:ℝ) - x2) * (x3 - (4:ℝ)) * (x5 - (3793/625:ℝ)) * (x6 - (3793/625:ℝ)) * (20965651/390625:ℝ)
        + (x2 - (4:ℝ)) * ((3969/625:ℝ) - x3) * ((8:ℝ) - x5) * ((8:ℝ) - x6) * (14614417/390625:ℝ)
        + (x2 - (4:ℝ)) * ((3969/625:ℝ) - x3) * ((8:ℝ) - x5) * (x6 - (3793/625:ℝ)) * (17631917/390625:ℝ)
        + (x2 - (4:ℝ)) * ((3969/625:ℝ) - x3) * (x5 - (3793/625:ℝ)) * ((8:ℝ) - x6) * (31048/625:ℝ)
        + (x2 - (4:ℝ)) * ((3969/625:ℝ) - x3) * (x5 - (3793/625:ℝ)) * (x6 - (3793/625:ℝ)) * (20965651/390625:ℝ)
        + (x2 - (4:ℝ)) * (x3 - (4:ℝ)) * ((8:ℝ) - x5) * ((8:ℝ) - x6) * (3985558/78125:ℝ)
        + (x2 - (4:ℝ)) * (x3 - (4:ℝ)) * ((8:ℝ) - x5) * (x6 - (3793/625:ℝ)) * (24718373/390625:ℝ)
        + (x2 - (4:ℝ)) * (x3 - (4:ℝ)) * (x5 - (3793/625:ℝ)) * ((8:ℝ) - x6) * (24718373/390625:ℝ)
        + (x2 - (4:ℝ)) * (x3 - (4:ℝ)) * (x5 - (3793/625:ℝ)) * (x6 - (3793/625:ℝ)) * (28052107/390625:ℝ)
        := by
      unfold ztgW ztgd0
      ring
    rw [hId]
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ((mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2h hbx3h) hbx5h) hbx6h) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2h hbx3h) hbx5h) hbx6l) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2h hbx3h) hbx5l) hbx6h) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2h hbx3h) hbx5l) hbx6l) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2h hbx3l) hbx5h) hbx6h) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2h hbx3l) hbx5h) hbx6l) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2h hbx3l) hbx5l) hbx6h) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2h hbx3l) hbx5l) hbx6l) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2l hbx3h) hbx5h) hbx6h) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2l hbx3h) hbx5h) hbx6l) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2l hbx3h) hbx5l) hbx6h) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2l hbx3h) hbx5l) hbx6l) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2l hbx3l) hbx5h) hbx6h) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2l hbx3l) hbx5h) hbx6l) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2l hbx3l) hbx5l) hbx6h) (by norm_num))) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hbx2l hbx3l) hbx5l) hbx6l) (by norm_num))
  exact Kepler.Text.ZTGDgrad0011.nonneg_of_pos_mul (by norm_num) hs

/-! ## The original-box assembly -/

/-- The original debt-box obligation (no pinned x1/x4): the landed
81-coefficient face leaf plus the two monotone-prune glue steps. -/
theorem ztgG_box_0_0_1_1 (x1 x2 x3 x4 x5 x6 : ℝ)
    (hx1l : (3793/625:ℝ) ≤ x1) (hx1h : x1 ≤ (43917129/6250000:ℝ))
    (hx2l : (4:ℝ) ≤ x2) (hx2h : x2 ≤ (3969/625:ℝ))
    (hx3l : (4:ℝ) ≤ x3) (hx3h : x3 ≤ (3969/625:ℝ))
    (hx4l : (4:ℝ) ≤ x4) (hx4h : x4 ≤ (3969/625:ℝ))
    (hx5l : (3793/625:ℝ) ≤ x5) (hx5h : x5 ≤ (8:ℝ))
    (hx6l : (3793/625:ℝ) ≤ x6) (hx6h : x6 ≤ (8:ℝ)) :
    (0:ℝ) ≤ 4 * x1 * deltaX x1 x2 x3 x4 x5 x6
        - (36/25) * (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2 := by
  -- (i) the landed leaf at the pruned face
  have hleaf : (0:ℝ) ≤ 4 * (3793/625:ℝ)
        * deltaX (3793/625:ℝ) x2 x3 (4:ℝ) x5 x6
        - (36/25) * (deltaX4 (3793/625:ℝ) x2 x3 (4:ℝ) x5 x6) ^ 2 :=
    Kepler.Text.BernsteinLeaf0011.ztgG_leaf_0_0_1_1 (3793/625:ℝ) x2 x3
      (4:ℝ) x5 x6 rfl rfl hx2l hx2h hx3l hx3h hx5l hx5h hx6l hx6h
  -- (ii) x4 prune on the x1-face (piece A)
  have hW : (0:ℝ) ≤ ztgW x2 x3 x5 x6 :=
    ztgW_nonneg x2 x3 x5 x6 hx2l hx2h hx3l hx3h hx5l hx5h hx6l hx6h
  have hstep4 : 4 * (3793/625:ℝ) * deltaX (3793/625:ℝ) x2 x3 (4:ℝ) x5 x6
        - (36/25) * (deltaX4 (3793/625:ℝ) x2 x3 (4:ℝ) x5 x6) ^ 2
      ≤ 4 * (3793/625:ℝ) * deltaX (3793/625:ℝ) x2 x3 x4 x5 x6
        - (36/25) * (deltaX4 (3793/625:ℝ) x2 x3 x4 x5 x6) ^ 2 := by
    have hd := ztgG_quad_diff_x4 (3793/625:ℝ) (36/25:ℝ) x2 x3 (4:ℝ) x4
      x5 x6
    have hb1 : (0:ℝ) ≤ x4 - (4:ℝ) := by linarith
    have hb2 : (0:ℝ) ≤ ztgd0 (3793/625:ℝ) x2 x3 x5 x6
        - (3793/625:ℝ) * ((4:ℝ) + x4) := by
      have e : ztgd0 (3793/625:ℝ) x2 x3 x5 x6
          - (3793/625:ℝ) * ((4:ℝ) + x4)
        = ztgW x2 x3 x5 x6 + (3793/625:ℝ) * ((3969/625:ℝ) - x4) := by
        unfold ztgW
        ring
      rw [e]
      exact add_nonneg hW
        (mul_nonneg (by norm_num) (by linarith))
    have hpos : (0:ℝ) ≤ (x4 - (4:ℝ))
        * (4 * (3793/625:ℝ) * (1 + (36/25:ℝ))
          * (ztgd0 (3793/625:ℝ) x2 x3 x5 x6
              - (3793/625:ℝ) * ((4:ℝ) + x4))) := by
      exact mul_nonneg hb1
        (mul_nonneg (by norm_num) hb2)
    linarith
  -- (iii) x1 prune on the full box (piece B)
  -- PR-29 discipline: the lemma's implicit f' is pinned by the EXPLICITLY
  -- typed hder (the closed-form Dgrad value), not left to unification.
  have hcont : ContinuousOn
      (fun s => 4 * s * deltaX s x2 x3 x4 x5 x6
        - (36/25) * (deltaX4 s x2 x3 x4 x5 x6) ^ 2)
      (Set.Icc (3793/625:ℝ) (43917129/6250000:ℝ)) := fun x _ =>
    (ztgG_hasDerivAt_x1 (36/25:ℝ) x x2 x3 x4 x5 x6
      ).differentiableAt.continuousAt.continuousWithinAt
  have hder : ∀ x ∈ interior
      (Set.Icc (3793/625:ℝ) (43917129/6250000:ℝ)),
      HasDerivWithinAt
        (fun s => 4 * s * deltaX s x2 x3 x4 x5 x6
          - (36/25) * (deltaX4 s x2 x3 x4 x5 x6) ^ 2)
        (4 * deltaX x x2 x3 x4 x5 x6
          + 4 * x * g4dDX1 x x2 x3 x4 x5 x6
          - 2 * (36/25:ℝ) * deltaX4 x x2 x3 x4 x5 x6
            * (-2 * x + x2 + x3 - 2 * x4 + x5 + x6))
        (interior (Set.Icc (3793/625:ℝ) (43917129/6250000:ℝ))) x :=
    fun x _ => (ztgG_hasDerivAt_x1 (36/25:ℝ) x x2 x3 x4 x5 x6
      ).hasDerivWithinAt
  have hpos : ∀ x ∈ interior
      (Set.Icc (3793/625:ℝ) (43917129/6250000:ℝ)),
      (0:ℝ) ≤ 4 * deltaX x x2 x3 x4 x5 x6
        + 4 * x * g4dDX1 x x2 x3 x4 x5 x6
        - 2 * (36/25:ℝ) * deltaX4 x x2 x3 x4 x5 x6
          * (-2 * x + x2 + x3 - 2 * x4 + x5 + x6) := by
    intro x hx
    have hx' : x ∈ Set.Icc (3793/625:ℝ) (43917129/6250000:ℝ) :=
      interior_subset hx
    exact Kepler.Text.ZTGDgrad0011.dgrad_nonneg x x2 x3 x4 x5 x6
      hx'.1 hx'.2 hx2l hx2h hx3l hx3h hx4l hx4h hx5l hx5h hx6l hx6h
  have hmono : MonotoneOn
      (fun s => 4 * s * deltaX s x2 x3 x4 x5 x6
        - (36/25) * (deltaX4 s x2 x3 x4 x5 x6) ^ 2)
      (Set.Icc (3793/625:ℝ) (43917129/6250000:ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Icc (3793/625:ℝ) (43917129/6250000:ℝ)) hcont hder hpos
  have hstep1 : 4 * (3793/625:ℝ) * deltaX (3793/625:ℝ) x2 x3 x4 x5 x6
        - (36/25) * (deltaX4 (3793/625:ℝ) x2 x3 x4 x5 x6) ^ 2
      ≤ 4 * x1 * deltaX x1 x2 x3 x4 x5 x6
        - (36/25) * (deltaX4 x1 x2 x3 x4 x5 x6) ^ 2 :=
    hmono (Set.mem_Icc.mpr ⟨le_refl _, by norm_num⟩)
      (Set.mem_Icc.mpr ⟨hx1l, hx1h⟩) hx1l
  linarith

end Kepler.Text.ZTGPruneGlue0011

#print axioms Kepler.Text.ZTGPruneGlue0011.hasDerivAt_of_eq
#print axioms Kepler.Text.ZTGPruneGlue0011.hasDerivAt_quad
#print axioms Kepler.Text.ZTGPruneGlue0011.ztgG_hasDerivAt_x1
#print axioms Kepler.Text.ZTGPruneGlue0011.ztgG_quad_diff_x4
#print axioms Kepler.Text.ZTGPruneGlue0011.ztgW_nonneg
#print axioms Kepler.Text.ZTGPruneGlue0011.ztgG_box_0_0_1_1

