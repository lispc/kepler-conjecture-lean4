import Kepler.NliBanks18
import Kepler.Text.Gamma4ValArctan
set_option maxHeartbeats 8000000
namespace Kepler.NliWt0Corner
open Kepler.Text
noncomputable def wt0A1 : ℝ := (161202 + 120801 * Real.sqrt 2) / 20000
noncomputable def wt0A2 : ℝ := (160000 + 119599 * Real.sqrt 2) / 20000
noncomputable def wt0T1 : ℝ := (682803 - 482002 * Real.sqrt 2) / 39599
noncomputable def wt0T2 : ℝ :=
  (43361914944031278399 - 30614266937792160000 * Real.sqrt 2) / 2261777775680481601
noncomputable def wt0G1 : ℝ := 80000 / 39599
noncomputable def wt0G2 : ℝ := 79198 / 40401
noncomputable def wt0W1 : ℝ := 2000000 / 7959399
noncomputable def wt0W2 : ℝ := 10000 / 40401
/-- Convert two-sided rational brackets of `sqrt t` and endpoint arctangents
into a two-sided bracket of the positive `matan` branch. -/
theorem wt0_matan_pos_of_sqrt_bounds {t slo shi alo ahi : ℝ}
    (hslo : slo ≤ Real.sqrt t) (hshi : Real.sqrt t ≤ shi) (hs0 : 0 < slo)
    (halo : alo ≤ Real.arctan slo) (hahi : Real.arctan shi ≤ ahi)
    (ha0 : 0 ≤ alo) (ha1 : 0 ≤ ahi) :
    alo / shi ≤ matan t ∧ matan t ≤ ahi / slo := by
  have hspos : 0 < Real.sqrt t := lt_of_lt_of_le hs0 hslo
  have hshipos : 0 < shi := lt_of_lt_of_le hs0 (hslo.trans hshi)
  have htpos : 0 < t := Real.sqrt_pos.mp hspos
  have hm : matan t = Real.arctan (Real.sqrt t) / Real.sqrt t := by
    unfold matan
    rw [if_neg (ne_of_gt htpos), if_pos htpos]
  rw [hm]
  constructor
  · rw [le_div_iff₀ hspos]
    have hmul : (alo / shi) * Real.sqrt t ≤ alo := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hshipos]
      exact mul_le_mul_of_nonneg_left hshi ha0
    exact hmul.trans (le_trans halo (Real.arctan_mono hslo))
  · rw [div_le_iff₀ hspos]
    have hmul : ahi ≤ (ahi / slo) * Real.sqrt t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hs0]
      exact mul_le_mul_of_nonneg_left hslo ha1
    exact (le_trans (Real.arctan_mono hshi) hahi).trans hmul
theorem wt0_k1_tight :
    (0.6443106 : ℝ) ≤ 2 * mm1 / Real.pi ∧ 2 * mm1 / Real.pi ≤ 0.6443108 := by
  have hm := g4v_mm1_bounds
  have hp := g4v_pi_bounds_d8
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · rw [le_div_iff₀ hpi]
    nlinarith [hm.1, hp.2]
  · rw [div_le_iff₀ hpi]
    nlinarith [hm.2, hp.1]
theorem wt0_k2_tight :
    (0.0647174 : ℝ) ≤ 8 * mm2 / Real.pi ∧ 8 * mm2 / Real.pi ≤ 0.0647176 := by
  have hm := g4v_mm2_bounds
  have hp := g4v_pi_bounds_d8
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · rw [le_div_iff₀ hpi]
    nlinarith [hm.1, hp.2]
  · rw [div_le_iff₀ hpi]
    nlinarith [hm.2, hp.1]
theorem wt0_sqrt2_tight : (1.41421356237 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 1.41421356238 := by
  constructor
  · exact Real.lt_sqrt_of_sq_lt (by norm_num)
  · exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
theorem wt0_A1_bounds : (16.60202060 : ℝ) ≤ wt0A1 ∧ wt0A1 ≤ 16.60202065 := by
  have hs := wt0_sqrt2_tight
  have hd : (0 : ℝ) < 20000 := by norm_num
  constructor
  · unfold wt0A1
    rw [le_div_iff₀ hd]
    norm_num
    nlinarith [hs.1, hs.2]
  · unfold wt0A1
    rw [div_le_iff₀ hd]
    norm_num
    nlinarith [hs.1, hs.2]
theorem wt0_A2_bounds : (16.45692637 : ℝ) ≤ wt0A2 ∧ wt0A2 ≤ 16.45692641 := by
  have hs := wt0_sqrt2_tight
  have hd : (0 : ℝ) < 20000 := by norm_num
  constructor
  · unfold wt0A2
    rw [le_div_iff₀ hd]
    norm_num
    nlinarith [hs.1, hs.2]
  · unfold wt0A2
    rw [div_le_iff₀ hd]
    norm_num
    nlinarith [hs.1, hs.2]
theorem wt0_sqrt_t1_bounds :
    (0.17035787 : ℝ) ≤ Real.sqrt wt0T1 ∧ Real.sqrt wt0T1 ≤ 0.17035788 := by
  have hs := wt0_sqrt2_tight
  have hd : (0 : ℝ) < 39599 := by norm_num
  constructor
  · apply Real.le_sqrt_of_sq_le
    unfold wt0T1
    rw [le_div_iff₀ hd]
    norm_num
    nlinarith [hs.1, hs.2]
  · apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 0.17035788)).mpr
    unfold wt0T1
    rw [div_le_iff₀ hd]
    norm_num
    nlinarith [hs.1, hs.2]
theorem wt0_sqrt_t2_bounds :
    (0.17185985 : ℝ) ≤ Real.sqrt wt0T2 ∧ Real.sqrt wt0T2 ≤ 0.17185986 := by
  have hs := wt0_sqrt2_tight
  have hd : (0 : ℝ) < 2261777775680481601 := by norm_num
  constructor
  · apply Real.le_sqrt_of_sq_le
    unfold wt0T2
    rw [le_div_iff₀ hd]
    norm_num
    nlinarith [hs.1, hs.2]
  · apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 0.17185986)).mpr
    unfold wt0T2
    rw [div_le_iff₀ hd]
    norm_num
    nlinarith [hs.1, hs.2]
theorem wt0_sqrt_g1_bounds :
    (1.42135605 : ℝ) ≤ Real.sqrt wt0G1 ∧ Real.sqrt wt0G1 ≤ 1.42135606 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num [wt0G1]
  · apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1.42135606)).mpr
    norm_num [wt0G1]
theorem wt0_sqrt_g2_bounds :
    (1.40010642 : ℝ) ≤ Real.sqrt wt0G2 ∧ Real.sqrt wt0G2 ≤ 1.40010643 := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num [wt0G2]
  · apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1.40010643)).mpr
    norm_num [wt0G2]
theorem wt0_matan_t1_bracket :
    (0.16873795 / 0.17035788 : ℝ) ≤ matan wt0T1 ∧
      matan wt0T1 ≤ 0.16873798 / 0.17035787 := by
  have hlo : (0.16873795 : ℝ) ≤ Real.arctan 0.17035787 ∧
      Real.arctan 0.17035787 ≤ 0.16873798 := by
    exact g4v_atan_pos_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hhi : (0.16873795 : ℝ) ≤ Real.arctan 0.17035788 ∧
      Real.arctan 0.17035788 ≤ 0.16873798 := by
    exact g4v_atan_pos_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  exact wt0_matan_pos_of_sqrt_bounds wt0_sqrt_t1_bounds.1 wt0_sqrt_t1_bounds.2
    (by norm_num) hlo.1 hhi.2 (by norm_num) (by norm_num)
theorem wt0_matan_t2_bracket :
    (0.17019720 / 0.17185986 : ℝ) ≤ matan wt0T2 ∧
      matan wt0T2 ≤ 0.17019723 / 0.17185985 := by
  have hlo : (0.17019720 : ℝ) ≤ Real.arctan 0.17185985 ∧
      Real.arctan 0.17185985 ≤ 0.17019723 := by
    exact g4v_atan_pos_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hhi : (0.17019720 : ℝ) ≤ Real.arctan 0.17185986 ∧
      Real.arctan 0.17185986 ≤ 0.17019723 := by
    exact g4v_atan_pos_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  exact wt0_matan_pos_of_sqrt_bounds wt0_sqrt_t2_bounds.1 wt0_sqrt_t2_bounds.2
    (by norm_num) hlo.1 hhi.2 (by norm_num) (by norm_num)
theorem wt0_matan_g1_bracket :
    (0.95768943 / 1.42135606 : ℝ) ≤ matan wt0G1 ∧
      matan wt0G1 ≤ 0.95768947 / 1.42135605 := by
  have hzlo : (0.61310686 : ℝ) ≤ Real.arctan (1.42135605⁻¹) ∧
      Real.arctan (1.42135605⁻¹) ≤ 0.61310689 := by
    exact g4v_atan_pos_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hzhi : (0.61310686 : ℝ) ≤ Real.arctan (1.42135606⁻¹) ∧
      Real.arctan (1.42135606⁻¹) ≤ 0.61310689 := by
    exact g4v_atan_pos_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hlo : (0.95768943 : ℝ) ≤ Real.arctan 1.42135605 ∧
      Real.arctan 1.42135605 ≤ 0.95768947 := by
    have hi := Real.arctan_inv_of_pos (x := (1.42135605 : ℝ)) (by norm_num)
    have hp := g4v_pi_bounds_d8
    constructor <;> nlinarith [hzlo.1, hzlo.2, hp.1, hp.2]
  have hhi : (0.95768943 : ℝ) ≤ Real.arctan 1.42135606 ∧
      Real.arctan 1.42135606 ≤ 0.95768947 := by
    have hi := Real.arctan_inv_of_pos (x := (1.42135606 : ℝ)) (by norm_num)
    have hp := g4v_pi_bounds_d8
    constructor <;> nlinarith [hzhi.1, hzhi.2, hp.1, hp.2]
  exact wt0_matan_pos_of_sqrt_bounds wt0_sqrt_g1_bounds.1 wt0_sqrt_g1_bounds.2
    (by norm_num) hlo.1 hhi.2 (by norm_num) (by norm_num)
theorem wt0_matan_g2_bracket :
    (0.95058277 / 1.40010643 : ℝ) ≤ matan wt0G2 ∧
      matan wt0G2 ≤ 0.95058281 / 1.40010642 := by
  have hzlo : (0.62021352 : ℝ) ≤ Real.arctan (1.40010642⁻¹) ∧
      Real.arctan (1.40010642⁻¹) ≤ 0.62021355 := by
    exact g4v_atan_pos_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hzhi : (0.62021352 : ℝ) ≤ Real.arctan (1.40010643⁻¹) ∧
      Real.arctan (1.40010643⁻¹) ≤ 0.62021355 := by
    exact g4v_atan_pos_bounds (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hlo : (0.95058277 : ℝ) ≤ Real.arctan 1.40010642 ∧
      Real.arctan 1.40010642 ≤ 0.95058281 := by
    have hi := Real.arctan_inv_of_pos (x := (1.40010642 : ℝ)) (by norm_num)
    have hp := g4v_pi_bounds_d8
    constructor <;> nlinarith [hzlo.1, hzlo.2, hp.1, hp.2]
  have hhi : (0.95058277 : ℝ) ≤ Real.arctan 1.40010643 ∧
      Real.arctan 1.40010643 ≤ 0.95058281 := by
    have hi := Real.arctan_inv_of_pos (x := (1.40010643 : ℝ)) (by norm_num)
    have hp := g4v_pi_bounds_d8
    constructor <;> nlinarith [hzhi.1, hzhi.2, hp.1, hp.2]
  exact wt0_matan_pos_of_sqrt_bounds wt0_sqrt_g2_bounds.1 wt0_sqrt_g2_bounds.2
    (by norm_num) hlo.1 hhi.2 (by norm_num) (by norm_num)
theorem wt0_sqrt_r : Real.sqrt ((201 / 100 : ℝ) * (201 / 100)) = 201 / 100 := by
  rw [show (201 / 100 : ℝ) * (201 / 100) = (201 / 100) ^ 2 by ring]
  exact Real.sqrt_sq (x := (201 / 100 : ℝ)) (by norm_num)
theorem wt0_sqrt_r2 : Real.sqrt ((201 / 100 : ℝ) ^ 2) = 201 / 100 :=
  Real.sqrt_sq (x := (201 / 100 : ℝ)) (by norm_num)
theorem wt0_sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
theorem wt0_sqrt_four_r2 : Real.sqrt (4 * (201 / 100 : ℝ) ^ 2) = 2 * (201 / 100) := by
  rw [show 4 * (201 / 100 : ℝ) ^ 2 = (2 * (201 / 100)) ^ 2 by ring]
  exact Real.sqrt_sq (x := 2 * (201 / 100 : ℝ)) (by positivity)
theorem wt0_sqrt_eight_r2 :
    Real.sqrt (4 * 2 * (201 / 100 : ℝ) ^ 2) = 2 * (201 / 100) * Real.sqrt 2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [show 4 * 2 * (201 / 100 : ℝ) ^ 2 = (2 * (201 / 100) * Real.sqrt 2) ^ 2 by
    ring_nf
    rw [hs2]
    ring]
  exact Real.sqrt_sq (x := 2 * (201 / 100 : ℝ) * Real.sqrt 2) (by positivity)
theorem wt0_sqrt_sixteen : Real.sqrt (4 * (4 : ℝ)) = 4 := by
  rw [show (4 : ℝ) * 4 = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
theorem wt0_se1_slot :
    solEulerXDivSqrtdelta 4 2 ((201 / 100 : ℝ) ^ 2) 2 4 2 = matan wt0T1 / wt0A1 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hD : deltaX 4 2 ((201 / 100 : ℝ) ^ 2) 2 4 2 =
      2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) := by
    norm_num [deltaX]
  have ha : Real.sqrt (4 * 2 * (201 / 100 : ℝ) ^ 2) +
      Real.sqrt 4 * (2 + (201 / 100 : ℝ) ^ 2 - 2) / 2 +
      Real.sqrt 2 * (4 + (201 / 100 : ℝ) ^ 2 - 4) / 2 +
      Real.sqrt ((201 / 100 : ℝ) ^ 2) * (4 + 2 - 2) / 2 = wt0A1 := by
    rw [wt0_sqrt_eight_r2, wt0_sqrt_four, wt0_sqrt_r2]
    unfold wt0A1
    ring
  have ht : 2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) /
      (4 * wt0A1 ^ 2) = wt0T1 := by
    unfold wt0A1 wt0T1
    have hs3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
        _ = 2 * Real.sqrt 2 := by rw [hs2]
    field_simp
    ring_nf
    rw [hs2, hs3]
    ring
  unfold solEulerXDivSqrtdelta
  dsimp only
  rw [hD, ha, ht]
theorem wt0_se2_slot :
    solEulerXDivSqrtdelta 4 2 4 2 ((201 / 100 : ℝ) ^ 2) 2 = matan wt0T2 / wt0A2 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hD : deltaX 4 2 4 2 ((201 / 100 : ℝ) ^ 2) 2 =
      2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) := by
    norm_num [deltaX]
  have ha : Real.sqrt (4 * 2 * 4) + Real.sqrt 4 * (2 + 4 - 2) / 2 +
      Real.sqrt 2 * (4 + 4 - (201 / 100 : ℝ) ^ 2) / 2 +
      Real.sqrt 4 * (4 + 2 - 2) / 2 = wt0A2 := by
    rw [show Real.sqrt (4 * 2 * (4 : ℝ)) = 4 * Real.sqrt 2 by
      rw [show (4 : ℝ) * 2 * 4 = 16 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
        show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], wt0_sqrt_four]
    unfold wt0A2
    ring
  have ht : 2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) /
      (4 * wt0A2 ^ 2) = wt0T2 := by
    unfold wt0A2 wt0T2
    have hs3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
        _ = 2 * Real.sqrt 2 := by rw [hs2]
    field_simp
    ring_nf
    rw [hs2, hs3]
    ring
  unfold solEulerXDivSqrtdelta
  dsimp only
  rw [hD, ha, ht]
theorem wt0_se3_slot :
    solEulerXDivSqrtdelta ((201 / 100 : ℝ) ^ 2) 2 4 2 4 2 = matan wt0T1 / wt0A1 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hD : deltaX ((201 / 100 : ℝ) ^ 2) 2 4 2 4 2 =
      2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) := by
    norm_num [deltaX]
  have ha : Real.sqrt ((201 / 100 : ℝ) ^ 2 * 2 * 4) +
      Real.sqrt ((201 / 100 : ℝ) ^ 2) * (2 + 4 - 2) / 2 +
      Real.sqrt 2 * ((201 / 100 : ℝ) ^ 2 + 4 - 4) / 2 +
      Real.sqrt 4 * ((201 / 100 : ℝ) ^ 2 + 2 - 2) / 2 = wt0A1 := by
    rw [show Real.sqrt ((201 / 100 : ℝ) ^ 2 * 2 * 4) =
      Real.sqrt (4 * 2 * (201 / 100 : ℝ) ^ 2) by ring_nf,
      wt0_sqrt_eight_r2, wt0_sqrt_r2, wt0_sqrt_four]
    unfold wt0A1
    ring
  have ht : 2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) /
      (4 * wt0A1 ^ 2) = wt0T1 := by
    unfold wt0A1 wt0T1
    have hs3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      calc
        Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
        _ = 2 * Real.sqrt 2 := by rw [hs2]
    field_simp
    ring_nf
    rw [hs2, hs3]
    ring
  unfold solEulerXDivSqrtdelta
  dsimp only
  rw [hD, ha, ht]
/-- The three dihedral slots likewise collapse to two distinct atoms. -/
theorem wt0_dp1_slot :
    dihXDivSqrtdeltaPosbranch ((201 / 100 : ℝ) ^ 2) 2 4 2 4 2 = wt0W1 * matan wt0G1 := by
  have hD4 : deltaX4 ((201 / 100 : ℝ) ^ 2) 2 4 2 4 2 =
      (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) := by
    norm_num [deltaX4]
  have hD : deltaX ((201 / 100 : ℝ) ^ 2) 2 4 2 4 2 =
      2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) := by
    norm_num [deltaX]
  have hW : 2 * (201 / 100 : ℝ) / ((201 / 100 : ℝ) ^ 2 *
      (8 - (201 / 100 : ℝ) ^ 2)) = wt0W1 := by
    unfold wt0W1
    field_simp
    ring
  have hG : 4 * (201 / 100 : ℝ) ^ 2 *
      (2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2)) /
      ((201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2)) ^ 2 = wt0G1 := by
    unfold wt0G1
    field_simp
    ring
  unfold dihXDivSqrtdeltaPosbranch
  dsimp only
  rw [hD4, hD, wt0_sqrt_four_r2, hW, hG]
theorem wt0_dp2_slot :
    dihXDivSqrtdeltaPosbranch 4 2 ((201 / 100 : ℝ) ^ 2) 2 4 2 = wt0W2 * matan wt0G2 := by
  have hD4 : deltaX4 4 2 ((201 / 100 : ℝ) ^ 2) 2 4 2 = 4 * (201 / 100 : ℝ) ^ 2 := by
    norm_num [deltaX4]
  have hD : deltaX 4 2 ((201 / 100 : ℝ) ^ 2) 2 4 2 =
      2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) := by
    norm_num [deltaX]
  have hW : (4 : ℝ) / (4 * (201 / 100 : ℝ) ^ 2) = wt0W2 := by
    unfold wt0W2
    field_simp
    ring
  have hG : 4 * 4 * (2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2)) /
      (4 * (201 / 100 : ℝ) ^ 2) ^ 2 = wt0G2 := by
    unfold wt0G2
    field_simp
    ring
  unfold dihXDivSqrtdeltaPosbranch
  dsimp only
  rw [hD4, hD, wt0_sqrt_sixteen, hW, hG]
theorem wt0_dp3_slot :
    dihXDivSqrtdeltaPosbranch 4 2 4 2 ((201 / 100 : ℝ) ^ 2) 2 = wt0W2 * matan wt0G2 := by
  have hD4 : deltaX4 4 2 4 2 ((201 / 100 : ℝ) ^ 2) 2 = 4 * (201 / 100 : ℝ) ^ 2 := by
    norm_num [deltaX4]
  have hD : deltaX 4 2 4 2 ((201 / 100 : ℝ) ^ 2) 2 =
      2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2) := by
    norm_num [deltaX]
  have hW : (4 : ℝ) / (4 * (201 / 100 : ℝ) ^ 2) = wt0W2 := by
    unfold wt0W2
    field_simp
    ring
  have hG : 4 * 4 * (2 * (201 / 100 : ℝ) ^ 2 * (8 - (201 / 100 : ℝ) ^ 2)) /
      (4 * (201 / 100 : ℝ) ^ 2) ^ 2 = wt0G2 := by
    unfold wt0G2
    field_simp
    ring
  unfold dihXDivSqrtdeltaPosbranch
  dsimp only
  rw [hD4, hD, wt0_sqrt_sixteen, hW, hG]
/-- Public-definition expansion of the corner kernel into the six slot values. -/
theorem wt0_pc3_corner : Kepler.NliBanks18.pc3 (201 / 100) 2 2 =
    1 / 12 - (2 * mm1 / Real.pi) *
      (matan wt0T1 / wt0A1 + matan wt0T2 / wt0A2 + matan wt0T1 / wt0A1) +
      (8 * mm2 / Real.pi) * ((51 / 52 : ℝ) * (wt0W1 * matan wt0G1) +
        wt0W2 * matan wt0G2 + wt0W2 * matan wt0G2) := by
  have e4 : Real.sqrt ((201 / 100 : ℝ) * (201 / 100)) = 201 / 100 := wt0_sqrt_r
  have e1 := Kepler.NliBanks18.nb18_indep 1 1 1 (201 / 100 : ℝ) 2 2
  rw [← e1]
  simp only [yOfX, Kepler.NliBanks18.nb18_unfold, mul_one]
  rw [e4]
  simp only [show (2 : ℝ) * 2 = 4 by norm_num, wt0_sqrt_four,
    show (201 / 100 : ℝ) * (201 / 100) = (201 / 100) ^ 2 by ring,
    show (201 / 100 : ℝ) * 0.5 = (201 / 100) / 2 from by ring,
    show (2 : ℝ) * 0.5 = 1 from by norm_num]
  rw [wt0_se1_slot, wt0_se2_slot, wt0_se3_slot, wt0_dp1_slot, wt0_dp2_slot, wt0_dp3_slot]
  have hl : lfun ((201 / 100 : ℝ) / 2) = 51 / 52 := by
    show (h0 - (201 / 100 : ℝ) / 2) / (h0 - 1) = 51 / 52
    rw [show h0 = (1.26 : ℝ) from rfl]
    norm_num
  rw [hl, Kepler.NliBanks11.nb11_lfun_one]
  ring
theorem wt0_se_upper : matan wt0T1 / wt0A1 + matan wt0T2 / wt0A2 + matan wt0T1 / wt0A1 ≤
    0.17949862 := by
  have hA1 := wt0_A1_bounds
  have hA2 := wt0_A2_bounds
  have h1p : 0 < wt0A1 := lt_of_lt_of_le (by norm_num) hA1.1
  have h2p : 0 < wt0A2 := lt_of_lt_of_le (by norm_num) hA2.1
  have h1 : matan wt0T1 / wt0A1 ≤ 0.05966089 := by
    calc
      matan wt0T1 / wt0A1 ≤ (0.16873798 / 0.17035787) / wt0A1 :=
        div_le_div_of_nonneg_right wt0_matan_t1_bracket.2 h1p.le
      _ ≤ (0.16873798 / 0.17035787) / 16.60202060 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hA1.1
      _ ≤ 0.05966089 := by norm_num
  have h2 : matan wt0T2 / wt0A2 ≤ 0.06017684 := by
    calc
      matan wt0T2 / wt0A2 ≤ (0.17019723 / 0.17185985) / wt0A2 :=
        div_le_div_of_nonneg_right wt0_matan_t2_bracket.2 h2p.le
      _ ≤ (0.17019723 / 0.17185985) / 16.45692637 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hA2.1
      _ ≤ 0.06017684 := by norm_num
  nlinarith

theorem wt0_dp_lower : 0.50214841 ≤ (51 / 52 : ℝ) * (wt0W1 * matan wt0G1) +
    wt0W2 * matan wt0G2 + wt0W2 * matan wt0G2 := by
  have h1 : 0.16604979 ≤ (51 / 52 : ℝ) * (wt0W1 * matan wt0G1) := by
    have h := mul_le_mul_of_nonneg_left wt0_matan_g1_bracket.1
      (by norm_num [wt0W1] : (0 : ℝ) ≤ (51 / 52) * wt0W1)
    norm_num [wt0W1] at h ⊢
    nlinarith [h]
  have h2 : 0.16804931 ≤ wt0W2 * matan wt0G2 := by
    have h := mul_le_mul_of_nonneg_left wt0_matan_g2_bracket.1
      (by norm_num [wt0W2] : (0 : ℝ) ≤ wt0W2)
    norm_num [wt0W2] at h ⊢
    nlinarith [h]
  nlinarith

theorem wt0_corner_pos : (17 / 100000 : ℝ) < Kepler.NliBanks18.pc3 (201 / 100) 2 2 := by
  rw [wt0_pc3_corner]
  have hse := wt0_se_upper
  have hdp := wt0_dp_lower
  have hk1 := wt0_k1_tight
  have hk2 := wt0_k2_tight
  have h1p : 0 < wt0A1 := lt_of_lt_of_le (by norm_num) wt0_A1_bounds.1
  have h2p : 0 < wt0A2 := lt_of_lt_of_le (by norm_num) wt0_A2_bounds.1
  have hs0 : 0 ≤ matan wt0T1 / wt0A1 + matan wt0T2 / wt0A2 + matan wt0T1 / wt0A1 := by
    have h1 : 0 ≤ matan wt0T1 / wt0A1 :=
      div_nonneg (le_trans (by norm_num) wt0_matan_t1_bracket.1) h1p.le
    have h2 : 0 ≤ matan wt0T2 / wt0A2 :=
      div_nonneg (le_trans (by norm_num) wt0_matan_t2_bracket.1) h2p.le
    nlinarith
  have hd0 : 0 ≤ (51 / 52 : ℝ) * (wt0W1 * matan wt0G1) +
      wt0W2 * matan wt0G2 + wt0W2 * matan wt0G2 := by linarith
  have h1 := mul_le_mul_of_nonneg_right hk1.2 hs0
  have h2 := mul_le_mul_of_nonneg_left hse (by norm_num : (0 : ℝ) ≤ 0.6443108)
  have h3 := mul_le_mul_of_nonneg_right hk2.1 hd0
  have h4 := mul_le_mul_of_nonneg_left hdp (by norm_num : (0 : ℝ) ≤ 0.0647174)
  nlinarith

end Kepler.NliWt0Corner
