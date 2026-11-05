/-
  Kepler.T11Proofs — lane `mnt11-rolling` M1.

  Cert-free proof of one T0 named statement of
  `main_nonlinear_terminal_v11`:
  `mainEstimate_6843920790` (`num1 e1 e2 e3 a2 b2 c2 > 0`).

  Route (verified by probe /tmp/mnt11m0/probes/P_num1_6843.lean):
  * arithmetic brick `sol0 / π < 1/5` from `sin 0.32 < 1/3` and
    Mathlib's `pi_gt_d2` / `pi_lt_d2`;
  * `num1` is linear in `e1 e2 e3`; decompose it as
    `4 * (A*e1 + C*e3 + D*(e2-e3))` with
    `A = a2*(16-a2)`, `C = a2*(b2+c2-16)`, `D = a2*(b2-8) - 8*(b2-c2)`;
  * four sign cases of `C` and `D`, each closed by a quadratic
    `nlinarith` over the box.

  Statements are NOT touched: this file imports `Kepler.Text.LocalAuto1`
  read-only.  No placeholder proofs and no extra axioms.
-/
import Kepler.Text.LocalAuto1
import Kepler.Interval.Cases.C8405387449

namespace Kepler.Text
namespace T11Proofs

/-- `arccos(1/3) < π/2 - 0.32`, from `sin 0.32 < 1/3`. -/
theorem arccos_third_lt_m1 : Real.arccos (1 / 3 : ℝ) < Real.pi / 2 - 0.32 := by
  have ht : Real.cos (Real.pi / 2 - 0.32) = Real.sin 0.32 := by
    rw [Real.cos_pi_div_two_sub]
  have hsin : Real.sin 0.32 < (1 / 3 : ℝ) := by
    have h1 : Real.sin 0.32 < 0.32 := Real.sin_lt (by norm_num)
    linarith
  have harg : Real.cos (Real.pi / 2 - 0.32) < (1 / 3 : ℝ) := by rw [ht]; exact hsin
  have hlt : Real.arccos (1 / 3 : ℝ) < Real.arccos (Real.cos (Real.pi / 2 - 0.32)) :=
    Real.arccos_lt_arccos (Real.neg_one_le_cos _) harg (by norm_num)
  rwa [Real.arccos_cos (by linarith [Real.pi_gt_d2]) (by linarith [Real.pi_pos])] at hlt

/-- `sol0 / π < 1/5`. -/
theorem sol0_div_pi_lt_m1 : sol0 / Real.pi < 1 / 5 := by
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have h1 : sol0 < 0.615 := by
    have h2 : Real.arccos (1 / 3 : ℝ) < Real.pi / 2 - 0.32 := arccos_third_lt_m1
    unfold sol0
    linarith [Real.pi_lt_d2]
  have h3 : (0.615 : ℝ) / Real.pi < 1 / 5 := by
    rw [div_lt_iff₀ hpi0]
    nlinarith [Real.pi_gt_d2]
  exact lt_trans (div_lt_div_of_pos_right h1 hpi0) h3

/-- On the `e`-box `[1, 1+sol0/π]`, every slot is at most `1.2`. -/
theorem e_le_6_5_m1 {e : ℝ} (h : e ≤ 1 + sol0 / Real.pi) : e ≤ 1.2 := by
  have hs : sol0 / Real.pi < 1 / 5 := sol0_div_pi_lt_m1
  linarith

set_option maxHeartbeats 1000000 in
/-- HOL `Main_estimate` `6843920790`: `num1 > 0` on its registry box. -/
theorem t11_6843920790 : mainEstimate_6843920790 := by
  intro e1 e2 e3 a2 b2 c2 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have h1u : e1 ≤ 1.2 := e_le_6_5_m1 h1'
  have h2u : e2 ≤ 1.2 := e_le_6_5_m1 h2'
  have h3u : e3 ≤ 1.2 := e_le_6_5_m1 h3'
  have h4lo : (2.5 : ℝ) ≤ a2 := by
    have hh : (2.5 : ℝ) ≤ ((2 : ℝ) / h0) ^ 2 := by norm_num [h0]
    linarith
  have h4hi : a2 ≤ 9.0601 := by
    have hh : (((3.01 : ℝ) ^ 2) : ℝ) = 9.0601 := by norm_num
    linarith
  have h5lo : (5.66 : ℝ) ≤ b2 := by
    have hh : (((2.38 : ℝ) ^ 2) : ℝ) = 5.6644 := by norm_num
    linarith
  have h6lo : (5.66 : ℝ) ≤ c2 := by
    have hh : (((2.38 : ℝ) ^ 2) : ℝ) = 5.6644 := by norm_num
    linarith
  set A : ℝ := a2 * (16 - a2) with hAdef
  set C : ℝ := a2 * (b2 + c2 - 16) with hCdef
  set D : ℝ := a2 * (b2 - 8) - 8 * (b2 - c2) with hDdef
  have hdecomp : num1 e1 e2 e3 a2 b2 c2
      = 4 * (A * e1 + C * e3 + D * (e2 - e3)) := by
    rw [hAdef, hCdef, hDdef]; unfold num1; ring
  have hA : 0 < A := by rw [hAdef]; nlinarith
  have hdlo : (-1 / 5 : ℝ) ≤ e2 - e3 := by linarith
  have hdhi : e2 - e3 ≤ 1 / 5 := by linarith
  have hq1 : 0 ≤ C → 0 < A + C - (1 / 5) * D := by
    intro hC
    rw [hCdef, hDdef] at *
    nlinarith [h4lo, h4hi, h5lo, h5', h6lo, h6']
  have hq2 : 0 ≤ C → D < 0 → 0 < A + C + (1 / 5) * D := by
    intro hC hD
    rw [hCdef, hDdef] at *
    nlinarith [h4lo, h4hi, h5lo, h5', h6lo, h6']
  have hq3 : C < 0 → 0 ≤ D → 0 < A + (6 / 5) * C - (1 / 5) * D := by
    intro hC hD
    rw [hCdef, hDdef] at *
    nlinarith [h4lo, h4hi, h5lo, h5', h6lo, h6']
  have hq4 : C < 0 → D < 0 → 0 < A + (6 / 5) * C + (1 / 5) * D := by
    intro hC hD
    rw [hCdef, hDdef] at *
    nlinarith [h4lo, h4hi, h5lo, h5', h6lo, h6']
  rw [hdecomp]
  by_cases hC : 0 ≤ C
  · by_cases hD : 0 ≤ D
    · have := hq1 hC; nlinarith [h1, h1u, h2, h2u, h3, h3u, hdlo, hdhi, hD]
    · push_neg at hD
      have := hq2 hC hD; nlinarith [h1, h1u, h2, h2u, h3, h3u, hdlo, hdhi, hD.le]
  · push_neg at hC
    by_cases hD : 0 ≤ D
    · have := hq3 hC hD; nlinarith [h1, h1u, h2, h2u, h3, h3u, hdlo, hdhi, hD]
    · push_neg at hD
      have := hq4 hC hD; nlinarith [h1, h1u, h2, h2u, h3, h3u, hdlo, hdhi, hD.le]

/-! ## `8405387449` — glued from `Kepler.Interval.Cases.C8405387449` -/

open Kepler.Interval

set_option maxHeartbeats 2000000 in
private theorem eval_C8405387449 (ρ : Fin 6 → ℝ) :
    (Kepler.Interval.Cases.C8405387449Expr).evalReal ρ
      = -(4 * (ρ 0 * deltaX (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5))
          + (-193 / 50 : ℝ) * (deltaX4 (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5)) ^ 2) := by
  dsimp only [Kepler.Interval.Cases.C8405387449Expr, IExpr.evalReal, deltaX, deltaX4]
  simp only [Dyadic.toReal_def]
  norm_num
  ring

set_option maxHeartbeats 2000000 in
/-- HOL `Main_estimate` `8405387449`: `4·x1Δy < 3.86·Δ₄y² ∨ Δy < 0` on its box. -/
theorem t11_8405387449 : mainEstimate_8405387449 := by
  intro y1 y2 y3 y4 y5 y6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  let ρ : Fin 6 → ℝ := ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6]
  have hv0 : ρ 0 = y1 * y1 := rfl
  have hv1 : ρ 1 = y2 * y2 := rfl
  have hv2 : ρ 2 = y3 * y3 := rfl
  have hv3 : ρ 3 = y4 * y4 := rfl
  have hv4 : ρ 4 = y5 * y5 := rfl
  have hv5 : ρ 5 = y6 * y6 := rfl
  have h6l : (2.52 : ℝ) ≤ y6 := by
    have h : (2 : ℝ) * Kepler.Text.h0 = 2.52 := by norm_num [Kepler.Text.h0]
    linarith
  have hρ0 : boxMem Kepler.Interval.Cases.C8405387449Box
      ![y1 * y1, y2 * y2, y3 * y3, y4 * y4, y5 * y5, y6 * y6] := by
    intro i
    fin_cases i
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y1 * y1)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h1, h1']
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y2 * y2)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h2, h2']
    · show (⟨⟨4, 0⟩, ⟨213084065, -25⟩⟩ : DInterval).mem (y3 * y3)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h3, h3']
    · show (⟨⟨4, 0⟩, ⟨4, 0⟩⟩ : DInterval).mem (y4 * y4)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h4, h4']
    · show (⟨⟨9728208299, -30⟩, ⟨13531831337, -30⟩⟩ : DInterval).mem (y5 * y5)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h5, h5']
    · show (⟨⟨6818690079, -30⟩, ⟨2432052075, -28⟩⟩ : DInterval).mem (y6 * y6)
      constructor <;> rw [Dyadic.toReal_def] <;> norm_num <;> nlinarith [h6l, h6']
  have hρ : boxMem Kepler.Interval.Cases.C8405387449Box ρ := hρ0
  obtain ⟨g, hg, hge⟩ := Kepler.Interval.Cases.C8405387449_pos ρ hρ
  simp only [Kepler.Interval.Cases.C8405387449Goals, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp only [DisjGoal.eval] at hge
    change 0 < (Kepler.Interval.Cases.C8405387449Expr).evalReal ρ at hge
    rw [eval_C8405387449] at hge
    rw [hv0, hv1, hv2, hv3, hv4, hv5] at hge
    left
    unfold x1DeltaY_t11 delta4SquaredY_t11
    nlinarith
  · simp only [DisjGoal.eval, IExpr.evalReal, Dyadic.toReal_def] at hge
    norm_num at hge
    right
    rw [hv0, hv1, hv2, hv3, hv4, hv5] at hge
    unfold deltaY deltaX
    ring_nf at hge ⊢
    linarith

end T11Proofs
end Kepler.Text
