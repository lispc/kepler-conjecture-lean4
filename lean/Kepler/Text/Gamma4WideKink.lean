/-
Kepler.Text.Gamma4WideKink — lane `nli-rest-b2`, part 1: the `lmfun` fold
(`y = 2·h0 = 2.52`) and the fold-plane minimum theorem for `gamma4fgcy`.

`lmfun h = if h ≤ h0 then (h0 − h)/(h0 − 1) else 0`, so on the `y`-axis the
fold is at `y/2 = h0`, i.e. `y = 2·h0`.  This module records:

* the two branch values `lmfun (y/2)` for `y ≤ 2h0` and `2h0 ≤ y`, the branch
  derivatives (`−1/(2(h0−1))` and `0`), and the two-sided range on the
  subcritical branch;
* the **fold-plane minimum theorem**: a continuous function whose derivative
  is `≤ 0` on `(a, 2h0)` and `≥ 0` on `(2h0, b)` attains its minimum over
  `[a,b]` at `2h0`;
* the `gamma4fgcy` y₁-slot instance of that theorem, with the two derivative
  premises written as explicit `g4dDVolY1 − g4dDVol4f1` inequalities (the
  branch values of `lmfun'` are substituted).  This is the machine-checked
  kink reduction: it **proves** that the minimum sits on the fold plane,
  rather than assuming the refined corner scan.

The continuity of the `gamma4fgcy` y₁-slice is carried as an explicit
hypothesis `hcont` (it is the standard continuity of `√`, `atn2` and the
piecewise-affine `lmfun`, assembled in the repo's continuity kits); everything
else is discharged here.

No `sorry`/`axiom`/`native_decide`; every declaration is axiom-audited.
-/
import Kepler.Text.Gamma4Deriv8
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option maxHeartbeats 4000000

open Set Filter
open scoped Topology

namespace Kepler.Text

/-! ## The fold of `lmfun : y ↦ lmfun (y/2)` at `y = 2·h0` -/

/-- On the subcritical side `y ≤ 2·h0`, `lmfun (y/2)` is the affine branch. -/
theorem g4w_lmfun_div2_of_le {y : ℝ} (hy : y ≤ 2 * h0) :
    lmfun (y / 2) = (h0 - y / 2) / (h0 - 1) := by
  rw [lmfun, if_pos]
  linarith

/-- On the supercritical side `2·h0 ≤ y`, `lmfun (y/2)` vanishes. -/
theorem g4w_lmfun_div2_of_ge {y : ℝ} (hy : 2 * h0 ≤ y) :
    lmfun (y / 2) = 0 := by
  rw [lmfun]
  split_ifs with h
  · have hyk : y / 2 = h0 := by linarith
    rw [hyk]; ring
  · rfl

/-- Two-sided range on the subcritical side: `0 ≤ lmfun (y/2) ≤ 1`. -/
theorem g4w_lmfun_div2_bounds_of_le {y : ℝ} (h1 : 2 ≤ y) (h2 : y ≤ 2 * h0) :
    0 ≤ lmfun (y / 2) ∧ lmfun (y / 2) ≤ 1 := by
  rw [g4w_lmfun_div2_of_le h2]
  have hden : (0:ℝ) < h0 - 1 := by norm_num [h0]
  have h0v : h0 = 1.26 := rfl
  constructor
  · rw [le_div_iff₀ hden]; nlinarith [h0v]
  · rw [div_le_one hden]; nlinarith [h0v]

/-- The fold-plane value is zero. -/
theorem g4w_lmfun_div2_at_fold : lmfun ((2 * h0) / 2) = 0 := by
  have h : (2 * h0) / 2 = h0 := by ring
  rw [h, lmfun, if_pos le_rfl]
  ring

/-- Derivative of `t ↦ lmfun (t/2)` on the subcritical branch. -/
theorem g4w_deriv_lmfun_div2_left {t : ℝ} (ht : t < 2 * h0) :
    HasDerivAt (fun s : ℝ => lmfun (s / 2)) ((-1 / (h0 - 1)) / 2) t := by
  have hlt : t / 2 < h0 := by linarith
  have h := g4d_hasDerivAt_lmfun_div2 (g4d_lmfun_hasDerivAt_of_lt hlt)
  convert h using 1 <;> ring

/-- Derivative of `t ↦ lmfun (t/2)` on the supercritical branch. -/
theorem g4w_deriv_lmfun_div2_right {t : ℝ} (ht : 2 * h0 < t) :
    HasDerivAt (fun s : ℝ => lmfun (s / 2)) 0 t := by
  have hgt : h0 < t / 2 := by linarith
  have h := g4d_hasDerivAt_lmfun_div2 (g4d_lmfun_hasDerivAt_of_gt hgt)
  simpa using h

/-! ## The fold-plane minimum theorem -/

/-- **Fold-plane minimum**.  Let `f` be continuous on `[a,b]`, differentiable on
the open intervals `(a, k)` and `(k, b)` with `deriv f ≤ 0` on the left and
`deriv f ≥ 0` on the right.  Then `f k ≤ f x` for every `x ∈ [a,b]`.

This is the kink reduction: the minimum is attained *on the fold plane*, so
the refined-corner scan is not merely a heuristic — on this axis it is
implied by the two branch slope signs. -/
theorem g4w_fold_min {f : ℝ → ℝ} {a b k : ℝ}
    (hak : a ≤ k) (hkb : k ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiffL : DifferentiableOn ℝ f (Ioo a k))
    (hdiffR : DifferentiableOn ℝ f (Ioo k b))
    (hL : ∀ x ∈ Ioo a k, deriv f x ≤ 0)
    (hR : ∀ x ∈ Ioo k b, 0 ≤ deriv f x) :
    ∀ x ∈ Icc a b, f k ≤ f x := by
  intro x hx
  rcases le_total x k with hxk | hkx
  · have hanti : AntitoneOn f (Icc a k) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc a k)
        (hcont.mono (Icc_subset_Icc le_rfl hkb)) ?_ ?_
      · simpa only [interior_Icc] using hdiffL
      · intro t ht
        rw [interior_Icc] at ht
        exact hL t ht
    exact hanti ⟨hx.1, hxk⟩ ⟨hak, le_rfl⟩ hxk
  · have hmono : MonotoneOn f (Icc k b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc k b)
        (hcont.mono (Icc_subset_Icc hak le_rfl)) ?_ ?_
      · simpa only [interior_Icc] using hdiffR
      · intro t ht
        rw [interior_Icc] at ht
        exact hR t ht
    exact hmono ⟨le_rfl, hkb⟩ ⟨hkx, hx.2⟩ hkx

/-! ## The `gamma4fgcy` y₁-slot fold reduction -/

/-- Derivative of the `y₁`-slice of `gamma4fgcy` at a non-fold point. -/
theorem g4w_gamma4_y1_hasDerivAt {y1 y2 y3 y4 y5 y6 L : ℝ}
    (hy1 : 0 < y1) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6) (hd : 0 < deltaY y1 y2 y3 y4 y5 y6)
    (hf : HasDerivAt lmfun L (y1 / 2)) :
    HasDerivAt (fun t => gamma4fgcy t y2 y3 y4 y5 y6 lmfun)
      (g4dDVolY1 y1 y2 y3 y4 y5 y6 - g4dDVol4f1 y1 y2 y3 y4 y5 y6 L) y1 :=
  gamma4fgcy_hasDerivAt_y1 y1 y2 y3 y4 y5 y6 L hy1 hy2 hy3 hy4 hy5 hy6 hd hf

/-- **Fold reduction for the `y₁`-slot of `gamma4fgcy`** on a `y₁`-range
`[a,b]` that straddles `2·h0`.  The two premises say that the smooth
derivative is nonpositive below the fold and nonnegative above it; then the
minimum of the slice sits at `y₁ = 2·h0`. -/
theorem g4w_gamma4_fold_min_y1 {a b y2 y3 y4 y5 y6 : ℝ}
    (ha : 0 < a) (hy2 : 0 < y2) (hy3 : 0 < y3) (hy4 : 0 < y4)
    (hy5 : 0 < y5) (hy6 : 0 < y6)
    (hd : ∀ t ∈ Ioo a b, 0 < deltaY t y2 y3 y4 y5 y6)
    (hcont : ContinuousOn (fun t => gamma4fgcy t y2 y3 y4 y5 y6 lmfun) (Icc a b))
    (hL : ∀ t ∈ Ioo a (2 * h0),
      g4dDVolY1 t y2 y3 y4 y5 y6 - g4dDVol4f1 t y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0)
    (hR : ∀ t ∈ Ioo (2 * h0) b,
      0 ≤ g4dDVolY1 t y2 y3 y4 y5 y6 - g4dDVol4f1 t y2 y3 y4 y5 y6 0)
    (hak : a ≤ 2 * h0) (hkb : 2 * h0 ≤ b) :
    ∀ t ∈ Icc a b, gamma4fgcy (2 * h0) y2 y3 y4 y5 y6 lmfun ≤
      gamma4fgcy t y2 y3 y4 y5 y6 lmfun := by
  refine g4w_fold_min hak hkb hcont ?_ ?_ ?_ ?_
  · intro t ht
    have htpos : 0 < t := lt_trans ha ht.1
    have hLt : t / 2 < h0 := by linarith [ht.2]
    exact (g4w_gamma4_y1_hasDerivAt htpos hy2 hy3 hy4 hy5 hy6
      (hd t ⟨ht.1, lt_of_lt_of_le ht.2 hkb⟩)
      (g4d_lmfun_hasDerivAt_of_lt hLt)).differentiableAt.differentiableWithinAt
  · intro t ht
    have htpos : 0 < t := by linarith [ha, ht.1]
    exact (g4w_gamma4_y1_hasDerivAt htpos hy2 hy3 hy4 hy5 hy6
      (hd t ⟨lt_of_le_of_lt hak ht.1, ht.2⟩)
      (g4d_lmfun_hasDerivAt_of_gt (by linarith [ht.1]))).differentiableAt.differentiableWithinAt
  · intro t ht
    have hd' := g4w_gamma4_y1_hasDerivAt (lt_trans ha ht.1) hy2 hy3 hy4 hy5 hy6
      (hd t ⟨ht.1, lt_of_lt_of_le ht.2 hkb⟩)
      (g4d_lmfun_hasDerivAt_of_lt (by linarith [ht.2]))
    rw [hd'.deriv]; exact hL t ht
  · intro t ht
    have hd' := g4w_gamma4_y1_hasDerivAt (by linarith [ha, ht.1]) hy2 hy3 hy4 hy5 hy6
      (hd t ⟨lt_of_le_of_lt (by linarith : a ≤ 2 * h0) ht.1, ht.2⟩)
      (g4d_lmfun_hasDerivAt_of_gt (by linarith [ht.1]))
    rw [hd'.deriv]; exact hR t ht

/-! ## Axiom audit (house style) -/

#print axioms g4w_lmfun_div2_of_le
#print axioms g4w_lmfun_div2_of_ge
#print axioms g4w_lmfun_div2_bounds_of_le
#print axioms g4w_lmfun_div2_at_fold
#print axioms g4w_deriv_lmfun_div2_left
#print axioms g4w_deriv_lmfun_div2_right
#print axioms g4w_fold_min
#print axioms g4w_gamma4_fold_min_y1

end Kepler.Text
