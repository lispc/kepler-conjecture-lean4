/-
Kepler.NliBanks11 — lane `nli-banks-close`, T2 (`nliCell3QZECFICwt0sqrt8`) reduction kit.

Self-contained: this file re-states the small `matan`/walk kit it needs (the
`nb11_*` twins of `Kepler.NliBanks10`'s `nb11_*`), so that each deliverable
module compiles alone under the single-file discipline.

Contents (no bank is proved outright; the residual obligations are the
explicit per-axis monotonicity hypotheses):

* `nb11_matan_le_one`, `nb11_matan_ge` — rational brackets for `matan` on the
  positive branch (`1 - t/3 ≤ matan t ≤ 1` for `t ≥ 0`);
* `nb11_corner_walk` — lower-corner reduction for product boxes;
* `nb11_c3_unfold` — explicit form of `gamma3fXDivSqrtdelta 0 1 1`;
* `c3Main` / `bank_QZECFICwt0sqrt8_of_mono` — T2 (`Assembly:389`) reduced to
  the three `y4,y5,y6` axis hypotheses; the corner value
  `c3Main (2hplus) 2 2` is *proved* `> 0`.

No unproved stub and no extra assumption: every declaration is audited at
the tail.
-/
import Kepler.Text.Gamma4ValCornerKit

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks11
open Kepler.Text

/-! ## 1. Closed brackets for `matan` on `[0, 7/5]` -/

/-- `f` with `f 0 = 0` and `f' ≥ 0` on `[0,∞)` is nonnegative there. -/
private theorem nb11_nonneg_of_deriv {f : ℝ → ℝ}
    (hC : Continuous f) (hD : Differentiable ℝ f) (h0 : f 0 = 0)
    (hd : ∀ x : ℝ, 0 ≤ x → 0 ≤ deriv f x) : ∀ s : ℝ, 0 ≤ s → 0 ≤ f s := by
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hC.continuousOn hD.differentiableOn
      (fun x hx => by
        have hlt : 0 < x := by simpa [interior_Ici, Set.mem_Ioi] using hx
        exact hd x hlt.le)
  intro s hs
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  rwa [h0] at h

/-- `arctan s ≤ s` for `s ≥ 0`. -/
theorem nb11_arctan_le_self {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ s := by
  have h := nb11_nonneg_of_deriv (f := fun x : ℝ => x - Real.arctan x)
    (hC := continuous_id.sub Real.continuous_arctan)
    (hD := differentiable_id.sub Real.differentiable_arctan)
    (h0 := by simp)
    (hd := by
      intro x _
      have hderiv : HasDerivAt (fun y : ℝ => y - Real.arctan y) (1 - 1 / (1 + x ^ 2)) x :=
        (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
      rw [hderiv.deriv]
      have hdpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
      have : 1 - 1 / (1 + x ^ 2) = x ^ 2 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity) s hs
  linarith

/-- `s - s³/3 ≤ arctan s` for `s ≥ 0`. -/
theorem nb11_arctan_ge_sub {s : ℝ} (hs : 0 ≤ s) :
    s - s ^ 3 / 3 ≤ Real.arctan s := by
  have h := nb11_nonneg_of_deriv (f := fun x : ℝ => Real.arctan x - x + x ^ 3 / 3)
    (hC := Real.continuous_arctan.sub continuous_id |>.add (continuous_pow 3 |>.div_const 3))
    (hD := Real.differentiable_arctan.sub differentiable_id |>.add (differentiable_pow 3 |>.div_const 3))
    (h0 := by simp)
    (hd := by
      intro x _
      have hderiv : HasDerivAt (fun y : ℝ => Real.arctan y - y + y ^ 3 / 3)
          (1 / (1 + x ^ 2) - 1 + x ^ 2) x := by
        have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
          have := (hasDerivAt_pow 3 x).div_const 3
          simpa [pow_succ] using this
        exact ((Real.hasDerivAt_arctan x).sub (hasDerivAt_id x)).add h3
      rw [hderiv.deriv]
      have : 1 / (1 + x ^ 2) - 1 + x ^ 2 = x ^ 4 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity) s hs
  linarith

/-- **Upper bracket**: `matan t ≤ 1` for `t ≥ 0`. -/
theorem nb11_matan_le_one {t : ℝ} (ht : 0 ≤ t) : matan t ≤ 1 := by
  rcases eq_or_lt_of_le ht with h | ht'
  · rw [← h]
    unfold matan
    rw [if_pos rfl]
  · have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht'
    unfold matan
    rw [if_neg (ne_of_gt ht'), if_pos ht']
    rw [div_le_one hs]
    exact nb11_arctan_le_self hs.le

/-- **Lower bracket**: `1 - t/3 ≤ matan t` for `t ≥ 0` (no upper range needed). -/
theorem nb11_matan_ge {t : ℝ} (ht : 0 ≤ t) : 1 - t / 3 ≤ matan t := by
  rcases eq_or_lt_of_le ht with h | ht'
  · rw [← h]
    unfold matan
    rw [if_pos rfl]
    norm_num
  · have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht'
    have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
    unfold matan
    rw [if_neg (ne_of_gt ht'), if_pos ht']
    rw [le_div_iff₀ hs]
    have hge : Real.sqrt t - Real.sqrt t ^ 3 / 3 ≤ Real.arctan (Real.sqrt t) :=
      nb11_arctan_ge_sub hs.le
    have hcube : Real.sqrt t ^ 3 = Real.sqrt t * t := by
      calc Real.sqrt t ^ 3 = Real.sqrt t * Real.sqrt t ^ 2 := by ring
        _ = Real.sqrt t * t := by rw [hs2]
    rw [hcube] at hge
    calc (1 - t / 3) * Real.sqrt t = Real.sqrt t - Real.sqrt t * t / 3 := by ring
      _ ≤ Real.arctan (Real.sqrt t) := hge

/-- `√4 = 2`. -/
theorem nb11_sqrt_4 : Real.sqrt (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√16 = 4`. -/
theorem nb11_sqrt_16 : Real.sqrt (4 * 4 : ℝ) = 4 := by
  rw [show (4 * 4 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ## 2. The corner walk -/

/-- If lowering any single coordinate to its lower bound never increases `f`,
and the box is closed under those single-coordinate lowerings, then `f` at the
lower corner is a lower bound for `f` on the box. -/
theorem nb11_corner_walk {n : ℕ} (lo : Fin n → ℝ) (box : (Fin n → ℝ) → Prop)
    (f : (Fin n → ℝ) → ℝ)
    (hbox : ∀ x, box x → ∀ i, box (Function.update x i (lo i)))
    (hstep : ∀ x, box x → ∀ i, f (Function.update x i (lo i)) ≤ f x)
    {x : Fin n → ℝ} (hx : box x) : f lo ≤ f x := by
  classical
  have key : ∀ S : Finset (Fin n), ∃ y : Fin n → ℝ,
      (∀ i ∈ S, y i = lo i) ∧ (∀ i, i ∉ S → y i = x i) ∧ box y ∧ f y ≤ f x := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨x, by simp, by simp, hx, le_rfl⟩
    | insert i S hi ih =>
        obtain ⟨y, hyS, hyout, hybox, hyf⟩ := ih
        refine ⟨Function.update y i (lo i), ?_, ?_, hbox y hybox i, ?_⟩
        · intro j hj
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self]
          · rw [Function.update_apply, if_neg hji]
            exact hyS j (by
              rcases Finset.mem_insert.mp hj with h | h
              · exact absurd h hji
              · exact h)
        · intro j hj
          have hji : j ≠ i := by intro h; exact hj (by simp [h])
          have hjS : j ∉ S := by intro h; exact hj (by simp [h])
          rw [Function.update_apply, if_neg hji]
          exact hyout j hjS
        · calc f (Function.update y i (lo i)) ≤ f y := hstep y hybox i
            _ ≤ f x := hyf
  obtain ⟨y, hy, -, -, hyf⟩ := key Finset.univ
  have hyl : y = lo := by funext i; exact hy i (Finset.mem_univ i)
  rwa [hyl] at hyf

/-- Box-closure for a coordinate box given `lo ≤ x` at every coordinate. -/
theorem nb11_box_update {n : ℕ} (lo hi : Fin n → ℝ) {x : Fin n → ℝ}
    (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i) (i : Fin n) :
    ∀ j, lo j ≤ Function.update x i (lo i) j ∧ Function.update x i (lo i) j ≤ hi j := by
  intro j
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self]
    exact ⟨le_rfl, le_trans (hx j).1 (hx j).2⟩
  · rw [Function.update_apply, if_neg hji]
    exact hx j


/-! ## 3. Per-slot bound helpers -/

/-- `lfun 1 = 1`. -/
theorem nb11_lfun_one : lfun 1 = 1 := by
  norm_num [lfun, h0]

/-- Upper bound for a `solEuler` slot: from `A ≤ a` and `Δ ≥ 0`,
`solEuler ≤ 1/A`. -/
theorem nb11_solEuler_le {x1 x2 x3 x4 x5 x6 A Δ : ℝ}
    (ha : A ≤ Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
        Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2)
    (hA : 0 < A) (hΔ : deltaX x1 x2 x3 x4 x5 x6 = Δ) (hΔ0 : 0 ≤ Δ) :
    solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 ≤ 1 / A := by
  have ha0 : 0 < Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
      Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2 :=
    lt_of_lt_of_le hA ha
  have ht0 : 0 ≤ Δ / (4 * (Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
      Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2) ^ 2) := by
    positivity
  have hm : matan (Δ / (4 * (Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
      Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2) ^ 2)) ≤ 1 :=
    nb11_matan_le_one ht0
  simp only [solEulerXDivSqrtdelta]
  rw [hΔ]
  have hstep : matan (Δ / (4 * (Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
      Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2) ^ 2)) /
      (Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
        Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2) ≤
      1 / (Real.sqrt (x1 * x2 * x3) + Real.sqrt x1 * (x2 + x3 - x4) / 2 +
        Real.sqrt x2 * (x1 + x3 - x5) / 2 + Real.sqrt x3 * (x1 + x2 - x6) / 2) :=
    div_le_div_of_nonneg_right hm ha0.le
  refine le_trans hstep ?_
  exact one_div_le_one_div_of_le hA ha

/-- Lower bound for a `dihDiv` slot: from `Δ, Δ₄` values and `t ≤ t0`,
`(√(4x₁)/Δ₄)·(1 - t0/3) ≤ dihDiv`. -/
theorem nb11_dihDiv_ge {x1 x2 x3 x4 x5 x6 d d4 t0 : ℝ}
    (hd : deltaX x1 x2 x3 x4 x5 x6 = d) (hd4 : deltaX4 x1 x2 x3 x4 x5 x6 = d4)
    (hd4pos : 0 < d4) (hx1 : 0 < x1) (hd0 : 0 ≤ d)
    (_ht0 : 0 ≤ t0) (ht : 4 * x1 * d / d4 ^ 2 ≤ t0) :
    (Real.sqrt (4 * x1) / d4) * (1 - t0 / 3) ≤ dihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by
  have htpos : 0 ≤ 4 * x1 * d / d4 ^ 2 := by positivity
  have hm : 1 - t0 / 3 ≤ matan (4 * x1 * d / d4 ^ 2) := by
    have h := nb11_matan_ge htpos
    linarith
  have hw : 0 ≤ Real.sqrt (4 * x1) / d4 :=
    div_nonneg (Real.sqrt_nonneg _) hd4pos.le
  simp only [dihXDivSqrtdeltaPosbranch]
  rw [hd, hd4]
  exact mul_le_mul_of_nonneg_left hm hw

/-! ## 4. T2 — `bank_QZECFICwt0sqrt8` -/

/-- Explicit form of `gamma3fXDivSqrtdelta 0 1 1` (the `mk456` slots 1–3 are
replaced by `2` before the rotations, so `x1 x2 x3` do not occur; the `m4 = 0`
term is killed). -/
theorem nb11_c3_unfold (x1 x2 x3 x4 x5 x6 : ℝ) :
    gamma3fXDivSqrtdelta 0 1 1 x1 x2 x3 x4 x5 x6 =
      1 / 12 - (2 * mm1 / Real.pi) *
        (solEulerXDivSqrtdelta x5 2 x4 2 x6 2 + solEulerXDivSqrtdelta x6 2 x5 2 x4 2 +
          solEulerXDivSqrtdelta x4 2 x6 2 x5 2) +
        (8 * mm2 / Real.pi) *
          (lfun (Real.sqrt x4 * 0.5) * 0 * dihXDivSqrtdeltaPosbranch x4 2 x6 2 x5 2 +
            lfun (Real.sqrt x5 * 0.5) * 1 * dihXDivSqrtdeltaPosbranch x5 2 x4 2 x6 2 +
            lfun (Real.sqrt x6 * 0.5) * 1 * dihXDivSqrtdeltaPosbranch x6 2 x5 2 x4 2) := by
  simp only [gamma3fXDivSqrtdelta, scalar6, uni, mk456, compose6, projX4, projX5, projX6,
    projY4, projY5, projY6, constant6, two6, rotate4, rotate5, rotate6,
    Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  ring

/-- T2 kernel on the free coordinates. -/
noncomputable def c3Main (y4 y5 y6 : ℝ) : ℝ :=
  yOfX (gamma3fXDivSqrtdelta 0 1 1) 1 1 1 y4 y5 y6

/-- The cell-3 kernel does not depend on `y1,y2,y3` (`mk456` overwrites
`x1,x2,x3` by `2` before rotating). -/
theorem nb11_c3_indep (y1 y2 y3 y4 y5 y6 : ℝ) :
    yOfX (gamma3fXDivSqrtdelta 0 1 1) y1 y2 y3 y4 y5 y6 = c3Main y4 y5 y6 := by
  simp only [c3Main, yOfX, nb11_c3_unfold, one_mul]

private theorem nb11_c3_a1 :
    (24.7 : ℝ) ≤ Real.sqrt ((4:ℝ) * 2 * 7.02674064) +
      Real.sqrt 4 * (2 + 7.02674064 - 2) / 2 +
      Real.sqrt 2 * (4 + 7.02674064 - 4) / 2 +
      Real.sqrt 7.02674064 * (4 + 2 - 2) / 2 := by
  have h1 : (7.49 : ℝ) ≤ Real.sqrt ((4:ℝ) * 2 * 7.02674064) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have h2 : (1.414 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have h4 : Real.sqrt (4:ℝ) = 2 := nb11_sqrt_4
  have hx : Real.sqrt (7.02674064:ℝ) = 2.6508 := by
    rw [show (7.02674064:ℝ) = 2.6508 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, hx]
  nlinarith [h1, h2]

private theorem nb11_c3_a1' :
    (24.7 : ℝ) ≤ Real.sqrt ((7.02674064:ℝ) * 2 * 4) +
      Real.sqrt 7.02674064 * (2 + 4 - 2) / 2 +
      Real.sqrt 2 * (7.02674064 + 4 - 4) / 2 +
      Real.sqrt 4 * (7.02674064 + 2 - 2) / 2 := by
  have h1 : (7.49 : ℝ) ≤ Real.sqrt ((7.02674064:ℝ) * 2 * 4) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have h2 : (1.414 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have h4 : Real.sqrt (4:ℝ) = 2 := nb11_sqrt_4
  have hx : Real.sqrt (7.02674064:ℝ) = 2.6508 := by
    rw [show (7.02674064:ℝ) = 2.6508 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, hx]
  nlinarith [h1, h2]

private theorem nb11_c3_a2 :
    (14.3 : ℝ) ≤ Real.sqrt ((4:ℝ) * 2 * 4) +
      Real.sqrt 4 * (2 + 4 - 2) / 2 +
      Real.sqrt 2 * (4 + 4 - 7.02674064) / 2 +
      Real.sqrt 4 * (4 + 2 - 2) / 2 := by
  have h1 : (5.65 : ℝ) ≤ Real.sqrt ((4:ℝ) * 2 * 4) := Real.le_sqrt_of_sq_le (by norm_num)
  have h2 : (1.414 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have h4 : Real.sqrt (4:ℝ) = 2 := nb11_sqrt_4
  rw [h4]
  nlinarith [h1, h2]

/-- **T2 corner value is positive**: `c3Main (2hplus) 2 2 > 0`
(true value `3.744688e-3`). -/
theorem nb11_c3_corner_pos : 0 < c3Main (2 * hplus) 2 2 := by
  have hx4 : (2 * hplus) * (2 * hplus) = 7.02674064 := by norm_num [hplus]
  simp only [c3Main, yOfX]
  rw [hx4]
  norm_num
  rw [nb11_c3_unfold]
  have hS1 : solEulerXDivSqrtdelta 4 2 7.02674064 2 4 2 ≤ 1 / 24.7 :=
    nb11_solEuler_le (A := 24.7) (Δ := deltaX 4 2 7.02674064 2 4 2) nb11_c3_a1
      (by norm_num) rfl (by norm_num [deltaX])
  have hS2 : solEulerXDivSqrtdelta 4 2 4 2 7.02674064 2 ≤ 1 / 14.3 :=
    nb11_solEuler_le (A := 14.3) (Δ := deltaX 4 2 4 2 7.02674064 2) nb11_c3_a2
      (by norm_num) rfl (by norm_num [deltaX])
  have hS3 : solEulerXDivSqrtdelta 7.02674064 2 4 2 4 2 ≤ 1 / 24.7 :=
    nb11_solEuler_le (A := 24.7) (Δ := deltaX 7.02674064 2 4 2 4 2) nb11_c3_a1'
      (by norm_num) rfl (by norm_num [deltaX])
  have hL1 : (Real.sqrt (4 * (4:ℝ)) / 28.10696256) * (1 - 0.28 / 3) ≤
      dihXDivSqrtdeltaPosbranch 4 2 7.02674064 2 4 2 :=
    nb11_dihDiv_ge (x1 := 4) (x2 := 2) (x3 := 7.02674064) (x4 := 2) (x5 := 4) (x6 := 2)
      (d := deltaX 4 2 7.02674064 2 4 2) (d4 := 28.10696256) (t0 := 0.28)
      rfl (by norm_num [deltaX4]) (by norm_num) (by norm_num) (by norm_num [deltaX])
      (by norm_num) (by norm_num [deltaX, deltaX4])
  have hL2 : (Real.sqrt (4 * (4:ℝ)) / 28.10696256) * (1 - 0.28 / 3) ≤
      dihXDivSqrtdeltaPosbranch 4 2 4 2 7.02674064 2 :=
    nb11_dihDiv_ge (x1 := 4) (x2 := 2) (x3 := 4) (x4 := 2) (x5 := 7.02674064) (x6 := 2)
      (d := deltaX 4 2 4 2 7.02674064 2) (d4 := 28.10696256) (t0 := 0.28)
      rfl (by norm_num [deltaX4]) (by norm_num) (by norm_num) (by norm_num [deltaX])
      (by norm_num) (by norm_num [deltaX, deltaX4])
  have hw : lfun (Real.sqrt (4:ℝ) * 0.5) * 1 = 1 := by
    rw [nb11_sqrt_4]
    norm_num [lfun, h0]
  rw [hw]
  simp only [mul_zero, zero_mul, one_mul]
  obtain ⟨hA1, hA2, hB1, hB2⟩ := g4v_AB_bounds
  have hA0 : (0 : ℝ) ≤ 2 * mm1 / Real.pi := by linarith
  have hB0 : (0 : ℝ) ≤ 8 * mm2 / Real.pi := by linarith
  have hS : solEulerXDivSqrtdelta 4 2 7.02674064 2 4 2 +
      solEulerXDivSqrtdelta 4 2 4 2 7.02674064 2 +
      solEulerXDivSqrtdelta 7.02674064 2 4 2 4 2 ≤ 2 * (1 / 24.7) + 1 / 14.3 := by
    linarith
  have hL : 2 * ((Real.sqrt (4 * (4:ℝ)) / 28.10696256) * (1 - 0.28 / 3)) ≤
      dihXDivSqrtdeltaPosbranch 4 2 7.02674064 2 4 2 +
        dihXDivSqrtdeltaPosbranch 4 2 4 2 7.02674064 2 := by
    linarith
  have hSh0 : (0 : ℝ) ≤ 2 * (1 / 24.7) + 1 / 14.3 := by norm_num
  have hSl0 : (0 : ℝ) ≤ 2 * ((Real.sqrt (4 * (4:ℝ)) / 28.10696256) * (1 - 0.28 / 3)) := by
    rw [nb11_sqrt_16]; norm_num
  have prodA : (2 * mm1 / Real.pi) *
      (solEulerXDivSqrtdelta 4 2 7.02674064 2 4 2 +
        solEulerXDivSqrtdelta 4 2 4 2 7.02674064 2 +
        solEulerXDivSqrtdelta 7.02674064 2 4 2 4 2) ≤
      0.6443107122 * (2 * (1 / 24.7) + 1 / 14.3) := by
    have h1 : (2 * mm1 / Real.pi) * (solEulerXDivSqrtdelta 4 2 7.02674064 2 4 2 +
        solEulerXDivSqrtdelta 4 2 4 2 7.02674064 2 +
        solEulerXDivSqrtdelta 7.02674064 2 4 2 4 2) ≤
        (2 * mm1 / Real.pi) * (2 * (1 / 24.7) + 1 / 14.3) :=
      mul_le_mul_of_nonneg_left hS hA0
    have h2 : (2 * mm1 / Real.pi) * (2 * (1 / 24.7) + 1 / 14.3) ≤
        0.6443107122 * (2 * (1 / 24.7) + 1 / 14.3) :=
      mul_le_mul_of_nonneg_right hA2 hSh0
    linarith
  have prodB : 0.0647174928 * (2 * ((Real.sqrt (4 * (4:ℝ)) / 28.10696256) * (1 - 0.28 / 3))) ≤
      (8 * mm2 / Real.pi) *
        (dihXDivSqrtdeltaPosbranch 4 2 7.02674064 2 4 2 +
          dihXDivSqrtdeltaPosbranch 4 2 4 2 7.02674064 2) :=
    mul_le_mul hB1 hL hSl0 hB0
  have hnum : (0.0166 : ℝ) ≤
      0.0647174928 * (2 * ((Real.sqrt (4 * (4:ℝ)) / 28.10696256) * (1 - 0.28 / 3))) := by
    rw [nb11_sqrt_16]; norm_num
  nlinarith [prodA, prodB, hnum]

/-! ## 5. T2 reduction -/

def c3Lo : Fin 3 → ℝ := ![2 * hplus, 2, 2]

noncomputable def c3Hi : Fin 3 → ℝ := ![Real.sqrt 8, 2 * hminus, 2 * hminus]

def c3Box (v : Fin 3 → ℝ) : Prop := ∀ i, c3Lo i ≤ v i ∧ v i ≤ c3Hi i

noncomputable def c3V (v : Fin 3 → ℝ) : ℝ := c3Main (v 0) (v 1) (v 2)

theorem nb11_c3V_corner : c3V c3Lo = c3Main (2 * hplus) 2 2 := by
  simp [c3V, c3Lo]

/-- **T2**: `bank_QZECFICwt0sqrt8` follows from the three coordinatewise
monotonicities on `y4,y5,y6`.  Statement verbatim; the corner value is proved. -/
theorem bank_QZECFICwt0sqrt8_of_mono
    (hstep : ∀ (v : Fin 3 → ℝ), c3Box v → ∀ i : Fin 3,
      c3V (Function.update v i (c3Lo i)) ≤ c3V v) :
    bank_QZECFICwt0sqrt8 := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  left
  rw [nb11_c3_indep]
  set y : Fin 3 → ℝ := ![y4, y5, y6] with hydef
  have hy0 : c3Lo 0 ≤ y 0 ∧ y 0 ≤ c3Hi 0 := by
    simp [c3Lo, c3Hi, y]; exact ⟨h4, h4'⟩
  have hy1 : c3Lo 1 ≤ y 1 ∧ y 1 ≤ c3Hi 1 := by
    simp [c3Lo, c3Hi, y]; exact ⟨h5, h5'⟩
  have hy2 : c3Lo 2 ≤ y 2 ∧ y 2 ≤ c3Hi 2 := by
    simp [c3Lo, c3Hi, y]; exact ⟨h6, h6'⟩
  have hy : c3Box y := by
    intro i
    fin_cases i
    · exact hy0
    · exact hy1
    · exact hy2
  have hwalk := nb11_corner_walk c3Lo c3Box c3V
    (fun v hv i => nb11_box_update c3Lo c3Hi hv i) hstep hy
  have hc : (0 : ℝ) < c3V c3Lo := by
    rw [nb11_c3V_corner]; exact nb11_c3_corner_pos
  have hye : c3V y = c3Main y4 y5 y6 := by
    simp [c3V, y]
  rw [hye] at hwalk
  exact lt_of_lt_of_le hc hwalk

/-! ## 6. Axiom audit -/

#print axioms nb11_matan_le_one
#print axioms nb11_matan_ge
#print axioms nb11_corner_walk
#print axioms nb11_c3_unfold
#print axioms nb11_c3_indep
#print axioms nb11_c3_corner_pos
#print axioms bank_QZECFICwt0sqrt8_of_mono

end Kepler.NliBanks11
