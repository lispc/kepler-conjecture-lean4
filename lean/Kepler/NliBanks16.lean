/-
Kepler.NliBanks16 — lane `nli-t1-gxsa`, part 2: closes `bank_TSKAJXYGXSA`.

Assembly of the eight slot bounds proved in `Kepler.NliBanks15`:

* four `solEuler` slots `≤ 1/26.799` (each: `nb15_a_p1/p2/p3` + `nb15_deltaX_lo`);
* four `ldih` slots `≥ 0.05622` (each: `nb15_d4_p1/p2` + `nb15_deltaX_lo/hi` + `nb15_lfun_ge`);
* `A = 2mm1/π ∈ [0.6443106485, 0.6443107122]`, `B = 8mm2/π ∈ [0.0647174928, 0.0647175183]`
  (`g4v_AB_bounds`), so

  `1/12 - A·Σsol + B·Σldih ≥ 1/12 - 0.6443107122·(4/26.799) + 0.0647174928·(4·0.05622)`
  `= 1.7176e-3 > 0`.

No `sorry`, no `axiom`, statement untouched (this proves the *first* disjunct on the whole
box; the `deltaX < 0` branch is never used).
-/
import Kepler.NliBanks15

namespace Kepler.NliBanks16
open Kepler.Text
open Kepler.NliBanks10
open Kepler.NliBanks15

set_option maxHeartbeats 4000000

/-! ## 1. Slot bounds -/

/-- A `solEuler` slot is `≤ 1/A` when `A > 0` bounds `nb15_eulerA` below and `deltaX ≥ 0`. -/
theorem nb16_sol_le {x1 x2 x3 x4 x5 x6 A : ℝ}
    (hA : 0 < A) (ha : A ≤ nb15_eulerA x1 x2 x3 x4 x5 x6)
    (hΔ : 0 ≤ deltaX x1 x2 x3 x4 x5 x6) :
    solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 ≤ 1 / A := by
  rw [nb15_solEuler_eq]
  have ha0 : 0 < nb15_eulerA x1 x2 x3 x4 x5 x6 := lt_of_lt_of_le hA ha
  have ht0 : (0:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 / (4 * nb15_eulerA x1 x2 x3 x4 x5 x6 ^ 2) :=
    div_nonneg hΔ (by positivity)
  have hm := nb10_matan_le_one ht0
  have h1 : matan (deltaX x1 x2 x3 x4 x5 x6 / (4 * nb15_eulerA x1 x2 x3 x4 x5 x6 ^ 2)) /
      nb15_eulerA x1 x2 x3 x4 x5 x6 ≤ 1 / nb15_eulerA x1 x2 x3 x4 x5 x6 :=
    div_le_div_of_nonneg_right hm ha0.le
  have h2 : (1:ℝ) / nb15_eulerA x1 x2 x3 x4 x5 x6 ≤ 1 / A :=
    one_div_le_one_div_of_le hA ha
  linarith

/-- An `ldih` slot is `≥ 0.05622` from the box brackets. -/
theorem nb16_ldih_ge {x1 x2 x3 x4 x5 x6 : ℝ}
    (h1 : 4 ≤ x1) (h1' : x1 ≤ 4.0401)
    (hΔ0 : 0 ≤ deltaX x1 x2 x3 x4 x5 x6)
    (hΔhi : deltaX x1 x2 x3 x4 x5 x6 ≤ 29.52807424)
    (hd4 : (58.9:ℝ) ≤ deltaX4 x1 x2 x3 x4 x5 x6)
    (hd4' : deltaX4 x1 x2 x3 x4 x5 x6 ≤ 66.57) :
    (0.05622:ℝ) ≤ ldihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by
  have hx1 : (0:ℝ) < x1 := by linarith
  have hd4pos : (0:ℝ) < deltaX4 x1 x2 x3 x4 x5 x6 := by linarith
  have hsq : (0:ℝ) < deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 := by positivity
  -- `4·x1·Δ ≤ 477.186`
  have hnum : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 ≤ 477.186 := by
    have h4x : 4 * x1 ≤ 16.1604 := by linarith
    have h := nb15_mulm h4x hΔhi (show (0:ℝ) ≤ 4 * x1 by linarith) hΔ0
    have hc : (16.1604:ℝ) * 29.52807424 ≤ 477.186 := by norm_num
    linarith
  -- `Δ₄² ≥ 3469.21`
  have hden : (3469.21:ℝ) ≤ deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 := by
    have h : (0:ℝ) ≤ (deltaX4 x1 x2 x3 x4 x5 x6 - 58.9) *
        (deltaX4 x1 x2 x3 x4 x5 x6 + 58.9) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hu0 : (0:ℝ) ≤ 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 / deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 :=
    div_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * x1) hΔ0) hsq.le
  have hu : 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 / deltaX4 x1 x2 x3 x4 x5 x6 ^ 2 ≤ 0.137552 := by
    rw [div_le_iff₀ hsq]
    nlinarith
  have hlfun := nb15_lfun_ge h1 h1'
  have hW : (4 / 66.57 : ℝ) ≤ Real.sqrt (4 * x1) / deltaX4 x1 x2 x3 x4 x5 x6 := by
    have hs4 : (4:ℝ) ≤ Real.sqrt (4 * x1) := by
      have h := Real.sqrt_le_sqrt (show (16:ℝ) ≤ 4 * x1 by linarith)
      rwa [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
    have h1' : (4 / 66.57 : ℝ) ≤ 4 / deltaX4 x1 x2 x3 x4 x5 x6 := by
      have h : (1:ℝ) / 66.57 ≤ 1 / deltaX4 x1 x2 x3 x4 x5 x6 :=
        one_div_le_one_div_of_le hd4pos hd4'
      calc (4 / 66.57 : ℝ) = 4 * (1 / 66.57) := by ring
        _ ≤ 4 * (1 / deltaX4 x1 x2 x3 x4 x5 x6) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 4 / deltaX4 x1 x2 x3 x4 x5 x6 := by ring
    have h2' : (4:ℝ) / deltaX4 x1 x2 x3 x4 x5 x6 ≤
        Real.sqrt (4 * x1) / deltaX4 x1 x2 x3 x4 x5 x6 :=
      div_le_div_of_nonneg_right hs4 hd4pos.le
    linarith
  have hm : (0.95414933:ℝ) ≤ matan (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 /
      deltaX4 x1 x2 x3 x4 x5 x6 ^ 2) := by
    have h := nb10_matan_ge hu0
    linarith
  have hW0 : (0:ℝ) ≤ Real.sqrt (4 * x1) / deltaX4 x1 x2 x3 x4 x5 x6 :=
    div_nonneg (Real.sqrt_nonneg _) hd4pos.le
  have hm0 : (0:ℝ) ≤ matan (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 /
      deltaX4 x1 x2 x3 x4 x5 x6 ^ 2) := by linarith
  have hlfun0 : (0:ℝ) ≤ lfun (Real.sqrt x1 / 2) := by linarith
  have hstep1 : (0.9807:ℝ) * (4 / 66.57) ≤
      lfun (Real.sqrt x1 / 2) * (Real.sqrt (4 * x1) / deltaX4 x1 x2 x3 x4 x5 x6) :=
    nb15_mulm hlfun hW (by norm_num) (by norm_num)
  have hstep2 : (0.9807:ℝ) * (4 / 66.57) * 0.95414933 ≤
      (lfun (Real.sqrt x1 / 2) * (Real.sqrt (4 * x1) / deltaX4 x1 x2 x3 x4 x5 x6)) *
        matan (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 / deltaX4 x1 x2 x3 x4 x5 x6 ^ 2) :=
    nb15_mulm hstep1 hm (by norm_num) (by linarith : (0:ℝ) ≤ 0.95414933)
  have hmul : lfun (Real.sqrt x1 / 2) * (Real.sqrt (4 * x1) / deltaX4 x1 x2 x3 x4 x5 x6) *
        matan (4 * x1 * deltaX x1 x2 x3 x4 x5 x6 / deltaX4 x1 x2 x3 x4 x5 x6 ^ 2) =
      ldihXDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by
    unfold ldihXDivSqrtdeltaPosbranch dihXDivSqrtdeltaPosbranch
    ring
  rw [← hmul]
  nlinarith


/-! ## 2. `deltaX` is invariant under the sphere.hl rotations -/

theorem nb16_deltaX_rot2 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x2 x3 x1 x5 x6 x4 = deltaX x1 x2 x3 x4 x5 x6 := by
  unfold deltaX; ring

theorem nb16_deltaX_rot3 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x3 x1 x2 x6 x4 x5 = deltaX x1 x2 x3 x4 x5 x6 := by
  unfold deltaX; ring

theorem nb16_deltaX_rot4 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x4 x2 x6 x1 x5 x3 = deltaX x1 x2 x3 x4 x5 x6 := by
  unfold deltaX; ring

theorem nb16_deltaX_rot5 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x5 x3 x4 x2 x6 x1 = deltaX x1 x2 x3 x4 x5 x6 := by
  unfold deltaX; ring

theorem nb16_deltaX_rot6 (x1 x2 x3 x4 x5 x6 : ℝ) :
    deltaX x6 x1 x5 x3 x4 x2 = deltaX x1 x2 x3 x4 x5 x6 := by
  unfold deltaX; ring

/-! ## 3. The eight slot bounds on the bank box -/

/-- The T1 kernel is nonnegative on the whole bank box. -/
theorem nb16_gxsaMain_nonneg {x1 x2 x3 x4 x5 x6 : ℝ}
    (h1 : (7.84:ℝ) ≤ x1) (h1' : x1 ≤ 8) (h2 : 4 ≤ x2) (h2' : x2 ≤ 4.0401)
    (h3 : 4 ≤ x3) (h3' : x3 ≤ 4.0401) (h4 : (7.84:ℝ) ≤ x4) (h4' : x4 ≤ 8)
    (h5 : 4 ≤ x5) (h5' : x5 ≤ 4.0401) (h6 : 4 ≤ x6) (h6' : x6 ≤ 4.0401) :
    (0:ℝ) ≤ gxsaMain x1 x2 x3 x4 x5 x6 := by
  have h24 : (4:ℝ) ≤ x4 := by linarith
  have h14 : (4:ℝ) ≤ x1 := by linarith
  have hΔ : (0:ℝ) ≤ deltaX x1 x2 x3 x4 x5 x6 :=
    nb15_deltaX_lo h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have hΔhi : deltaX x1 x2 x3 x4 x5 x6 ≤ 29.52807424 :=
    nb15_deltaX_hi h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  -- four `solEuler` slots (identity, rotate5, rotate6, rotate4)
  have hS1 : solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 ≤ (1 / 26.799 : ℝ) :=
    nb16_sol_le (by norm_num) (nb15_a_p1 h1 h2 h3 h3' h24 h4' h5 h5' h6 h6') hΔ
  have hS2 : solEuler345XDivSqrtdelta x1 x2 x3 x4 x5 x6 ≤ (1 / 26.799 : ℝ) := by
    simp only [solEuler345XDivSqrtdelta, rotate5]
    refine nb16_sol_le (by norm_num)
      (nb15_a_p2 (y1 := x5) (y2 := x3) (y3 := x4) (y4 := x2) (y5 := x6) (y6 := x1)
        h5 h5' h3 h3' h4 h4' h2 h2' h6 h6' h1 h1') ?_
    rw [nb16_deltaX_rot5]; exact hΔ
  have hS3 : solEuler156XDivSqrtdelta x1 x2 x3 x4 x5 x6 ≤ (1 / 26.799 : ℝ) := by
    simp only [solEuler156XDivSqrtdelta, rotate6]
    refine nb16_sol_le (by norm_num)
      (nb15_a_p3 (y1 := x6) (y2 := x1) (y3 := x5) (y4 := x3) (y5 := x4) (y6 := x2)
        h6 h6' h1 h1' h5 h5' h3 h3' h4 h4' h2 h2') ?_
    rw [nb16_deltaX_rot6]; exact hΔ
  have hS4 : solEuler246XDivSqrtdelta x1 x2 x3 x4 x5 x6 ≤ (1 / 26.799 : ℝ) := by
    simp only [solEuler246XDivSqrtdelta, rotate4]
    refine nb16_sol_le (by norm_num)
      (nb15_a_p1 (x1 := x4) (x2 := x2) (x3 := x6) (x4 := x1) (x5 := x5) (x6 := x3)
        h4 h2 h6 h6' h14 h1' h5 h5' h3 h3') ?_
    rw [nb16_deltaX_rot4]; exact hΔ
  -- four `ldih` slots (rotate2, rotate3, rotate5, rotate6)
  have hL2 : (0.05622:ℝ) ≤ ldih2XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by
    have hD := nb15_d4_p1 (y1 := x2) (y2 := x3) (y3 := x1) (y4 := x5) (y5 := x6) (y6 := x4)
      h2 h2' h3 h3' h1 h1' h5 h5' h6 h6' h4 h4'
    simp only [ldih2XDivSqrtdeltaPosbranch, rotate2]
    refine nb16_ldih_ge h2 h2' ?_ ?_ hD.1 hD.2
    · rw [nb16_deltaX_rot2]; exact hΔ
    · rw [nb16_deltaX_rot2]; exact hΔhi
  have hL3 : (0.05622:ℝ) ≤ ldih3XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by
    have hD := nb15_d4_p2 (y1 := x3) (y2 := x1) (y3 := x2) (y4 := x6) (y5 := x4) (y6 := x5)
      h3 h3' h1 h1' h2 h2' h6 h6' h4 h4' h5 h5'
    simp only [ldih3XDivSqrtdeltaPosbranch, rotate3]
    refine nb16_ldih_ge h3 h3' ?_ ?_ hD.1 hD.2
    · rw [nb16_deltaX_rot3]; exact hΔ
    · rw [nb16_deltaX_rot3]; exact hΔhi
  have hL5 : (0.05622:ℝ) ≤ ldih5XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by
    have hD := nb15_d4_p1 (y1 := x5) (y2 := x3) (y3 := x4) (y4 := x2) (y5 := x6) (y6 := x1)
      h5 h5' h3 h3' h4 h4' h2 h2' h6 h6' h1 h1'
    simp only [ldih5XDivSqrtdeltaPosbranch, rotate5]
    refine nb16_ldih_ge h5 h5' ?_ ?_ hD.1 hD.2
    · rw [nb16_deltaX_rot5]; exact hΔ
    · rw [nb16_deltaX_rot5]; exact hΔhi
  have hL6 : (0.05622:ℝ) ≤ ldih6XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by
    have hD := nb15_d4_p2 (y1 := x6) (y2 := x1) (y3 := x5) (y4 := x3) (y5 := x4) (y6 := x2)
      h6 h6' h1 h1' h5 h5' h3 h3' h4 h4' h2 h2'
    simp only [ldih6XDivSqrtdeltaPosbranch, rotate6]
    refine nb16_ldih_ge h6 h6' ?_ ?_ hD.1 hD.2
    · rw [nb16_deltaX_rot6]; exact hΔ
    · rw [nb16_deltaX_rot6]; exact hΔhi
  -- assembly
  have hSsum : solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 +
      solEuler345XDivSqrtdelta x1 x2 x3 x4 x5 x6 +
      solEuler156XDivSqrtdelta x1 x2 x3 x4 x5 x6 +
      solEuler246XDivSqrtdelta x1 x2 x3 x4 x5 x6 ≤ 4 * (1 / 26.799 : ℝ) := by linarith
  have hLsum : 4 * (0.05622:ℝ) ≤
      ldih2XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
        ldih3XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
        ldih5XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
        ldih6XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 := by linarith
  obtain ⟨hA1, hA2, hB1, hB2⟩ := g4v_AB_bounds
  have hA0 : (0:ℝ) ≤ 2 * mm1 / Real.pi := by linarith
  have hB0 : (0:ℝ) ≤ 8 * mm2 / Real.pi := by linarith
  have hS0 : (0:ℝ) ≤ 4 * (1 / 26.799 : ℝ) := by norm_num
  have hL0 : (0:ℝ) ≤ 4 * (0.05622:ℝ) := by norm_num
  set S := solEulerXDivSqrtdelta x1 x2 x3 x4 x5 x6 +
    solEuler345XDivSqrtdelta x1 x2 x3 x4 x5 x6 +
    solEuler156XDivSqrtdelta x1 x2 x3 x4 x5 x6 +
    solEuler246XDivSqrtdelta x1 x2 x3 x4 x5 x6 with hSdef
  set L := ldih2XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
    ldih3XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
    ldih5XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 +
    ldih6XDivSqrtdeltaPosbranch x1 x2 x3 x4 x5 x6 with hLdef
  have hLnn : (0:ℝ) ≤ L := by rw [hLdef]; linarith
  have prodA : (2 * mm1 / Real.pi) * S ≤ 0.6443107122 * (4 * (1 / 26.799 : ℝ)) :=
    le_trans (mul_le_mul_of_nonneg_left (by rw [hSdef]; exact hSsum) hA0)
      (mul_le_mul_of_nonneg_right hA2 hS0)
  have prodB : 0.0647174928 * (4 * (0.05622:ℝ)) ≤ (8 * mm2 / Real.pi) * L :=
    le_trans (mul_le_mul_of_nonneg_left (by rw [hLdef]; exact hLsum) (by norm_num))
      (mul_le_mul_of_nonneg_right hB1 hLnn)
  unfold gxsaMain
  rw [← hSdef, ← hLdef]
  nlinarith [prodA, prodB]

/-! ## 4. The bank -/

/-- **T1 closed**: `bank_TSKAJXYGXSA` (`Assembly:913`, `PackingAuto21:268`).
The first disjunct holds on the whole box; the `deltaX < 0` branch is never used. -/
theorem bank_TSKAJXYGXSA_proved : bank_TSKAJXYGXSA := by
  intro x1 x2 x3 x4 x5 x6 h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'
  have h28 : (2.8:ℝ) ^ 2 = 7.84 := by norm_num
  have h201 : (2.01:ℝ) ^ 2 = 4.0401 := by norm_num
  left
  show (0:ℝ) ≤ gxsaMain x1 x2 x3 x4 x5 x6
  exact nb16_gxsaMain_nonneg (by linarith) h1' h2 (by linarith) h3 (by linarith)
    (by linarith) h4' h5 (by linarith) h6 (by linarith)

end Kepler.NliBanks16
