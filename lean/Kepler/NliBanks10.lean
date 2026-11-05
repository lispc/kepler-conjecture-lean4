/-
Kepler.NliBanks10 — lane `nli-banks-close`, T1 (`nliTskGXSA`) reduction kit.

Contents (no bank is proved outright; the residual obligations are the
explicit per-axis monotonicity hypotheses):

* `nb10_matan_le_one`, `nb10_matan_ge` — closed rational brackets for
  `matan` on the positive branch: `1 - t/3 ≤ matan t ≤ 1` for `0 ≤ t ≤ 7/5`.
  (From `arctan s ≤ s` and `arctan s ≥ s - s³/3` at `s = √t`.)
* `nb10_corner_walk` — the generic "lower every coordinate to the box
  minimum" walk: if no coordinate lowering increases `f`, then `f` at the
  lower corner is a lower bound for `f` on the whole product box.
* `gxsaMain` / `bank_TSKAJXYGXSA_of_mono` — T1 (`nliTskGXSA`, Assembly:913)
  reduced to the six axis hypotheses; the corner value
  `gxsaMain 7.84 4 4 7.84 4 4` is *proved* `> 0` (see
  `gxsaMain_corner_pos`), so the only residual is the six monotonicities.
The T2 (`nliCell3QZECFICwt0sqrt8`) twin is `Kepler.NliBanks11` (self-contained
copy of the kit, so each deliverable file compiles alone).

No unproved stub and no extra assumption: every declaration is audited at
the tail.
-/
import Kepler.Text.Gamma4ValCornerKit

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks10
open Kepler.Text

/-! ## 1. Closed brackets for `matan` on `[0, 7/5]` -/

/-- `f` with `f 0 = 0` and `f' ≥ 0` on `[0,∞)` is nonnegative there. -/
private theorem nb10_nonneg_of_deriv {f : ℝ → ℝ}
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
theorem nb10_arctan_le_self {s : ℝ} (hs : 0 ≤ s) : Real.arctan s ≤ s := by
  have h := nb10_nonneg_of_deriv (f := fun x : ℝ => x - Real.arctan x)
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
theorem nb10_arctan_ge_sub {s : ℝ} (hs : 0 ≤ s) :
    s - s ^ 3 / 3 ≤ Real.arctan s := by
  have h := nb10_nonneg_of_deriv (f := fun x : ℝ => Real.arctan x - x + x ^ 3 / 3)
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
theorem nb10_matan_le_one {t : ℝ} (ht : 0 ≤ t) : matan t ≤ 1 := by
  rcases eq_or_lt_of_le ht with h | ht'
  · rw [← h]
    unfold matan
    rw [if_pos rfl]
  · have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht'
    unfold matan
    rw [if_neg (ne_of_gt ht'), if_pos ht']
    rw [div_le_one hs]
    exact nb10_arctan_le_self hs.le

/-- **Lower bracket**: `1 - t/3 ≤ matan t` for `t ≥ 0` (no upper range needed). -/
theorem nb10_matan_ge {t : ℝ} (ht : 0 ≤ t) : 1 - t / 3 ≤ matan t := by
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
      nb10_arctan_ge_sub hs.le
    have hcube : Real.sqrt t ^ 3 = Real.sqrt t * t := by
      calc Real.sqrt t ^ 3 = Real.sqrt t * Real.sqrt t ^ 2 := by ring
        _ = Real.sqrt t * t := by rw [hs2]
    rw [hcube] at hge
    calc (1 - t / 3) * Real.sqrt t = Real.sqrt t - Real.sqrt t * t / 3 := by ring
      _ ≤ Real.arctan (Real.sqrt t) := hge

/-! ## 2. The corner walk -/

/-- If lowering any single coordinate to its lower bound never increases `f`,
and the box is closed under those single-coordinate lowerings, then `f` at the
lower corner is a lower bound for `f` on the box. -/
theorem nb10_corner_walk {n : ℕ} (lo : Fin n → ℝ) (box : (Fin n → ℝ) → Prop)
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
theorem nb10_box_update {n : ℕ} (lo hi : Fin n → ℝ) {x : Fin n → ℝ}
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
theorem nb10_lfun_one : lfun 1 = 1 := by
  norm_num [lfun, h0]

/-- Upper bound for a `solEuler` slot: from `A ≤ a` and `Δ ≥ 0`,
`solEuler ≤ 1/A`. -/
theorem nb10_solEuler_le {x1 x2 x3 x4 x5 x6 A Δ : ℝ}
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
    nb10_matan_le_one ht0
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
theorem nb10_dihDiv_ge {x1 x2 x3 x4 x5 x6 d d4 t0 : ℝ}
    (hd : deltaX x1 x2 x3 x4 x5 x6 = d) (hd4 : deltaX4 x1 x2 x3 x4 x5 x6 = d4)
    (hd4pos : 0 < d4) (hx1 : 0 < x1) (hd0 : 0 ≤ d)
    (_ht0 : 0 ≤ t0) (ht : 4 * x1 * d / d4 ^ 2 ≤ t0) :
    (Real.sqrt (4 * x1) / d4) * (1 - t0 / 3) ≤ dihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by
  have htpos : 0 ≤ 4 * x1 * d / d4 ^ 2 := by positivity
  have hm : 1 - t0 / 3 ≤ matan (4 * x1 * d / d4 ^ 2) := by
    have h := nb10_matan_ge htpos
    linarith
  have hw : 0 ≤ Real.sqrt (4 * x1) / d4 :=
    div_nonneg (Real.sqrt_nonneg _) hd4pos.le
  simp only [dihXDivSqrtdeltaPosbranch]
  rw [hd, hd4]
  exact mul_le_mul_of_nonneg_left hm hw

/-! ## 4. T1 — `bank_TSKAJXYGXSA` -/

/-- T1 kernel: verbatim the first disjunct of `bank_TSKAJXYGXSA`. -/
noncomputable def gxsaMain (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  1 / 12 - (2 * mm1 / Real.pi) *
      (solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 +
        solEuler345XDivSqrtdelta x1 x2 x3 x4 x5 x6 +
        solEuler156XDivSqrtdelta x1 x2 x3 x4 x5 x6 +
        solEuler246XDivSqrtdelta x1 x2 x3 x4 x5 x6) +
    (8 * mm2 / Real.pi) *
      (ldih2XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
        ldih3XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
        ldih5XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
        ldih6XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6)

theorem nb10_sqrt_784 : Real.sqrt (7.84 : ℝ) = 2.8 := by
  rw [show (7.84 : ℝ) = 2.8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem nb10_sqrt_4 : Real.sqrt (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem nb10_sqrt_16 : Real.sqrt (4 * 4 : ℝ) = 4 := by
  rw [show (4 * 4 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem nb10_sqrt_125_44 : Real.sqrt (7.84 * 4 * 4 : ℝ) = 11.2 := by
  rw [show (7.84 * 4 * 4 : ℝ) = 11.2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem nb10_sqrt_125_44' : Real.sqrt (4 * 4 * 7.84 : ℝ) = 11.2 := by
  rw [show (4 * 4 * 7.84 : ℝ) = 11.2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem nb10_sqrt_125_44'' : Real.sqrt (4 * 7.84 * 4 : ℝ) = 11.2 := by
  rw [show (4 * 7.84 * 4 : ℝ) = 11.2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem nb10_gx_arg0 :
    Real.sqrt ((7.84 : ℝ) * 4 * 4) + Real.sqrt 7.84 * (4 + 4 - 7.84) / 2 +
      Real.sqrt 4 * (7.84 + 4 - 4) / 2 + Real.sqrt 4 * (7.84 + 4 - 4) / 2 = 27.104 := by
  rw [nb10_sqrt_125_44, nb10_sqrt_784, nb10_sqrt_4]
  norm_num

private theorem nb10_gx_arg1 :
    Real.sqrt ((4 : ℝ) * 4 * 7.84) + Real.sqrt 4 * (4 + 7.84 - 4) / 2 +
      Real.sqrt 4 * (4 + 7.84 - 4) / 2 + Real.sqrt 7.84 * (4 + 4 - 7.84) / 2 = 27.104 := by
  rw [nb10_sqrt_125_44', nb10_sqrt_784, nb10_sqrt_4]
  norm_num

private theorem nb10_gx_arg2 :
    Real.sqrt ((4 : ℝ) * 7.84 * 4) + Real.sqrt 4 * (7.84 + 4 - 4) / 2 +
      Real.sqrt 7.84 * (4 + 4 - 7.84) / 2 + Real.sqrt 4 * (4 + 7.84 - 4) / 2 = 27.104 := by
  rw [nb10_sqrt_125_44'', nb10_sqrt_784, nb10_sqrt_4]
  norm_num

/-- T1 corner: the four `solEuler` slots are `≤ 1/27.104`. -/
theorem nb10_gx_sol_le :
    solEulerXDivSqrtdelta 7.84 4 4 7.84 4 4 ≤ 1 / 27.104 ∧
      solEuler345XDivSqrtdelta 7.84 4 4 7.84 4 4 ≤ 1 / 27.104 ∧
      solEuler156XDivSqrtdelta 7.84 4 4 7.84 4 4 ≤ 1 / 27.104 ∧
      solEuler246XDivSqrtdelta 7.84 4 4 7.84 4 4 ≤ 1 / 27.104 := by
  have h0 : solEulerXDivSqrtdelta 7.84 4 4 7.84 4 4 ≤ 1 / 27.104 :=
    nb10_solEuler_le (A := 27.104) (Δ := 19.668992) nb10_gx_arg0.ge (by norm_num)
      (by norm_num [deltaX]) (by norm_num)
  have h1 : solEuler345XDivSqrtdelta 7.84 4 4 7.84 4 4 ≤ 1 / 27.104 := by
    simp only [solEuler345XDivSqrtdelta, rotate5]
    exact nb10_solEuler_le (A := 27.104) (Δ := 19.668992) nb10_gx_arg1.ge (by norm_num)
      (by norm_num [deltaX]) (by norm_num)
  have h2 : solEuler156XDivSqrtdelta 7.84 4 4 7.84 4 4 ≤ 1 / 27.104 := by
    simp only [solEuler156XDivSqrtdelta, rotate6]
    exact nb10_solEuler_le (A := 27.104) (Δ := 19.668992) nb10_gx_arg2.ge (by norm_num)
      (by norm_num [deltaX]) (by norm_num)
  have h3 : solEuler246XDivSqrtdelta 7.84 4 4 7.84 4 4 ≤ 1 / 27.104 := by
    simp only [solEuler246XDivSqrtdelta, rotate4]
    exact nb10_solEuler_le (A := 27.104) (Δ := 19.668992) nb10_gx_arg0.ge (by norm_num)
      (by norm_num [deltaX]) (by norm_num)
  exact ⟨h0, h1, h2, h3⟩

/-- T1 corner: the four `ldih` slots are `≥ (4/61.4656)·(1 - 0.084/3)`. -/
theorem nb10_gx_ldih_ge :
    (Real.sqrt (4 * (4:ℝ)) / 61.4656) * (1 - 0.084 / 3) ≤
        ldih2XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 ∧
      (Real.sqrt (4 * (4:ℝ)) / 61.4656) * (1 - 0.084 / 3) ≤
        ldih3XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 ∧
      (Real.sqrt (4 * (4:ℝ)) / 61.4656) * (1 - 0.084 / 3) ≤
        ldih5XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 ∧
      (Real.sqrt (4 * (4:ℝ)) / 61.4656) * (1 - 0.084 / 3) ≤
        ldih6XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 := by
  have h2 := nb10_dihDiv_ge (x1 := 4) (x2 := 4) (x3 := 7.84) (x4 := 4) (x5 := 4) (x6 := 7.84)
    (d := 19.668992) (d4 := 61.4656) (t0 := 0.084)
    (by norm_num [deltaX]) (by norm_num [deltaX4]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have h3 := nb10_dihDiv_ge (x1 := 4) (x2 := 7.84) (x3 := 4) (x4 := 4) (x5 := 7.84) (x6 := 4)
    (d := 19.668992) (d4 := 61.4656) (t0 := 0.084)
    (by norm_num [deltaX]) (by norm_num [deltaX4]) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simp only [ldih2XDivSqrtdeltaPosbranch, ldih3XDivSqrtdeltaPosbranch,
    ldih5XDivSqrtdeltaPosbranch, ldih6XDivSqrtdeltaPosbranch, rotate2, rotate3, rotate5,
    rotate6, ldihXDivSqrtdeltaPosbranch, nb10_sqrt_4,
    show (2 : ℝ) / 2 = 1 by norm_num, nb10_lfun_one, one_mul]
  exact ⟨h2, h3, h2, h3⟩


/-- **T1 corner value is positive**: `gxsaMain 7.84 4 4 7.84 4 4 > 0`
(certified two-sided arithmetic; true value `4.858275e-3`). -/
theorem nb10_gxsa_corner_pos : 0 < gxsaMain 7.84 4 4 7.84 4 4 := by
  obtain ⟨hS0, hS1, hS2, hS3⟩ := nb10_gx_sol_le
  obtain ⟨hL0, hL1, hL2, hL3⟩ := nb10_gx_ldih_ge
  have hS : solEulerXDivSqrtdelta 7.84 4 4 7.84 4 4 +
      solEuler345XDivSqrtdelta 7.84 4 4 7.84 4 4 +
      solEuler156XDivSqrtdelta 7.84 4 4 7.84 4 4 +
      solEuler246XDivSqrtdelta 7.84 4 4 7.84 4 4 ≤ 4 * (1 / 27.104) := by
    linarith
  have hL : 4 * ((Real.sqrt (4 * (4:ℝ)) / 61.4656) * (1 - 0.084 / 3)) ≤
      ldih2XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 +
        ldih3XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 +
        ldih5XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 +
        ldih6XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 := by
    linarith
  obtain ⟨hA1, hA2, hB1, hB2⟩ := g4v_AB_bounds
  have hA0 : (0 : ℝ) ≤ 2 * mm1 / Real.pi := by linarith
  have hB0 : (0 : ℝ) ≤ 8 * mm2 / Real.pi := by linarith
  have hSh0 : (0 : ℝ) ≤ 4 * (1 / 27.104) := by norm_num
  have hSl0 : (0 : ℝ) ≤ 4 * ((Real.sqrt (4 * (4:ℝ)) / 61.4656) * (1 - 0.084 / 3)) := by
    rw [nb10_sqrt_16]; norm_num
  have prodA : (2 * mm1 / Real.pi) *
      (solEulerXDivSqrtdelta 7.84 4 4 7.84 4 4 +
        solEuler345XDivSqrtdelta 7.84 4 4 7.84 4 4 +
        solEuler156XDivSqrtdelta 7.84 4 4 7.84 4 4 +
        solEuler246XDivSqrtdelta 7.84 4 4 7.84 4 4) ≤
      0.6443107122 * (4 * (1 / 27.104)) := by
    have h1 : (2 * mm1 / Real.pi) * (solEulerXDivSqrtdelta 7.84 4 4 7.84 4 4 +
        solEuler345XDivSqrtdelta 7.84 4 4 7.84 4 4 +
        solEuler156XDivSqrtdelta 7.84 4 4 7.84 4 4 +
        solEuler246XDivSqrtdelta 7.84 4 4 7.84 4 4) ≤
        (2 * mm1 / Real.pi) * (4 * (1 / 27.104)) :=
      mul_le_mul_of_nonneg_left hS hA0
    have h2 : (2 * mm1 / Real.pi) * (4 * (1 / 27.104)) ≤ 0.6443107122 * (4 * (1 / 27.104)) :=
      mul_le_mul_of_nonneg_right hA2 hSh0
    linarith
  have prodB : 0.0647174928 * (4 * ((Real.sqrt (4 * (4:ℝ)) / 61.4656) * (1 - 0.084 / 3))) ≤
      (8 * mm2 / Real.pi) *
        (ldih2XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 +
          ldih3XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 +
          ldih5XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4 +
          ldih6XDivSqrtdeltaPosbranch 7.84 4 4 7.84 4 4) :=
    mul_le_mul hB1 hL hSl0 hB0
  have hnum : (0.0163 : ℝ) ≤
      0.0647174928 * (4 * ((Real.sqrt (4 * (4:ℝ)) / 61.4656) * (1 - 0.084 / 3))) := by
    rw [nb10_sqrt_16]; norm_num
  unfold gxsaMain
  nlinarith [prodA, prodB, hnum]

/-! ## 5. T1 reduction -/

/-- T1 lower corner `(7.84, 4, 4, 7.84, 4, 4)` (the squared lower corner of the
bank box). -/
def gxLo : Fin 6 → ℝ := ![(2.8:ℝ)^2, 4, 4, (2.8:ℝ)^2, 4, 4]

/-- T1 upper corner `(8, 4.0401, 4.0401, 8, 4.0401, 4.0401)`. -/
def gxHi : Fin 6 → ℝ := ![8, (2.01:ℝ)^2, (2.01:ℝ)^2, 8, (2.01:ℝ)^2, (2.01:ℝ)^2]

/-- T1 box predicate. -/
def gxBox (v : Fin 6 → ℝ) : Prop := ∀ i, gxLo i ≤ v i ∧ v i ≤ gxHi i

/-- T1 kernel in vector form. -/
noncomputable def gxV (v : Fin 6 → ℝ) : ℝ :=
  gxsaMain (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)

theorem nb10_gxV_corner : gxV gxLo = gxsaMain 7.84 4 4 7.84 4 4 := by
  have h28 : ((2.8:ℝ))^2 = 7.84 := by norm_num
  simp [gxV, gxLo, h28]

/-- **T1**: `bank_TSKAJXYGXSA` follows from the six coordinatewise
monotonicities (lowering any single coordinate to the box minimum never
increases the kernel).  Statement verbatim; the corner value is proved. -/
theorem bank_TSKAJXYGXSA_of_mono
    (hstep : ∀ (v : Fin 6 → ℝ), gxBox v → ∀ i : Fin 6,
      gxV (Function.update v i (gxLo i)) ≤ gxV v) :
    bank_TSKAJXYGXSA := by
  intro x1 x2 x3 x4 x5 x6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  left
  set x : Fin 6 → ℝ := ![x1, x2, x3, x4, x5, x6] with hxdef
  have hx0 : gxLo 0 ≤ x 0 ∧ x 0 ≤ gxHi 0 := by
    simp [gxLo, gxHi, x]; exact ⟨h1, h1'⟩
  have hx1 : gxLo 1 ≤ x 1 ∧ x 1 ≤ gxHi 1 := by
    simp [gxLo, gxHi, x]; exact ⟨h2, h2'⟩
  have hx2 : gxLo 2 ≤ x 2 ∧ x 2 ≤ gxHi 2 := by
    simp [gxLo, gxHi, x]; exact ⟨h3, h3'⟩
  have hx3 : gxLo 3 ≤ x 3 ∧ x 3 ≤ gxHi 3 := by
    simp [gxLo, gxHi, x]; exact ⟨h4, h4'⟩
  have hx4 : gxLo 4 ≤ x 4 ∧ x 4 ≤ gxHi 4 := by
    simp [gxLo, gxHi, x]; exact ⟨h5, h5'⟩
  have hx5 : gxLo 5 ≤ x 5 ∧ x 5 ≤ gxHi 5 := by
    simp [gxLo, gxHi, x]; exact ⟨h6, h6'⟩
  have hx : gxBox x := by
    intro i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2
    · exact hx3
    · exact hx4
    · exact hx5
  have hwalk := nb10_corner_walk gxLo gxBox gxV
    (fun v hv i => nb10_box_update gxLo gxHi hv i) hstep hx
  have hc : (0 : ℝ) < gxV gxLo := by
    rw [nb10_gxV_corner]; exact nb10_gxsa_corner_pos
  have hxe : gxV x = gxsaMain x1 x2 x3 x4 x5 x6 := by
    simp [gxV, x]
  rw [hxe] at hwalk
  exact le_trans hc.le hwalk

/-! ## 6. Axiom audit -/

#print axioms nb10_arctan_le_self
#print axioms nb10_arctan_ge_sub
#print axioms nb10_matan_le_one
#print axioms nb10_matan_ge
#print axioms nb10_corner_walk
#print axioms nb10_gxsa_corner_pos
#print axioms bank_TSKAJXYGXSA_of_mono

end Kepler.NliBanks10
