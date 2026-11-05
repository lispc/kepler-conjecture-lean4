import Kepler.NliBanks3

/-!
Kepler.NliBanks4 — W2 lane `nli-unknown-w2`, task W2-1 (remaining `rad2` banks).

Five `ZTGIJCF4` instances.  The `H` telescoping kit and the `deltaX ≥ 100`
concavity bound live in `Kepler.NliBanks3` / `Kepler.NliHminus`; the critical
slot edge `x ≥ 6.0650528` is the W2-0 envelope `hminus ≥ 1.2313664`.
-/

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks4
open Kepler.Text
open Kepler.NliBanks3
open Kepler.NliHminus

/-- W2-1: `nliRestZTGIJCF4_1_1_1_1` (rad2 branch; ZTGIJCF4 1 1 1 1). -/
theorem nliRestZTGIJCF4_1_1_1_1 : bank_ZTGIJCF4_1_1_1_1 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h3l' : 2 * hminus ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3h' : y3 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h3h
  have h4l' : 2 * hminus ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4h' : y4 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h4h
  have h5l' : 2 * hminus ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5h' : y5 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h5h
  have h6l' : 2 * hminus ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6h' : y6 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h6h
  right
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (4:ℝ) ≤ y2*y2 := sq_ge_4 y2 h2l
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith) (le_sqrt8 y2 h2h)
  have hx3l : (6.0650528:ℝ) ≤ y3*y3 := by
    have h := sq_ge_hminus y3 h3l'
    linarith
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith [mi_hminus_prop.1]) h3h'
  have hx4l : (6.0650528:ℝ) ≤ y4*y4 := by
    have h := sq_ge_hminus y4 h4l'
    linarith
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith [mi_hminus_prop.1]) h4h'
  have hx5l : (6.0650528:ℝ) ≤ y5*y5 := by
    have h := sq_ge_hminus y5 h5l'
    linarith
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith [mi_hminus_prop.1]) h5h'
  have hx6l : (6.0650528:ℝ) ≤ y6*y6 := by
    have h := sq_ge_hminus y6 h6l'
    linarith
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith [mi_hminus_prop.1]) h6h'
  have hx2w : (4:ℝ) ≤ y2*y2 := by linarith [hx2l]
  have hx3w : (5.76:ℝ) ≤ y3*y3 := by linarith [hx3l]
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have hx5w : (4:ℝ) ≤ y5*y5 := by linarith [hx5l]
  have hx6w : (4:ℝ) ≤ y6*y6 := by linarith [hx6l]
  have s6 := H_mono_6 6.0650528 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx6l hx6h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h hx5w hx5h
  have s5 := H_mono_5 6.0650528 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 6.0650528 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx5l hx5h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s4 := H_mono_4 6.0650528 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 6.0650528 6.0650528 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx4l hx4h
    hx1l hx1h hx2w hx2h hx3w hx3h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s3 := H_mono_3 6.0650528 (y3*y3) (y1*y1) (y2*y2) 6.0650528 6.0650528 6.0650528 (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) hx3l hx3h
    hx1l hx1h hx2w hx2h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s2 := H_mono_2 4 (y2*y2) (y1*y1) 6.0650528 6.0650528 6.0650528 6.0650528 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx2l hx2h
    hx1l hx1h (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s1 := H_mono_1 6.0650528 (y1*y1) 4 6.0650528 6.0650528 6.0650528 6.0650528 (by norm_num : (6.0650528:ℝ) ≤ (6.0650528:ℝ)) hx1l hx1h
    (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have hcorner : (226:ℝ) ≤ rhoX 6.0650528 4 6.0650528 6.0650528 6.0650528 6.0650528 - 8 * deltaX 6.0650528 4 6.0650528 6.0650528 6.0650528 6.0650528 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd100 : (100:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge _ _ _ _ _ _ (by linarith) hx1h (by linarith) hx2h (by linarith) hx3h (by linarith) hx4h (by linarith) hx5h (by linarith) hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

/-- W2-1: `nliRestZTGIJCF4_1_1_1_0` (rad2 branch; ZTGIJCF4 1 1 1 0). -/
theorem nliRestZTGIJCF4_1_1_1_0 : bank_ZTGIJCF4_1_1_1_0 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h3l' : 2 * hminus ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3h' : y3 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h3h
  have h4l' : 2 * hminus ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4h' : y4 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h4h
  have h5l' : 2 * hminus ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5h' : y5 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h5h
  have h6l' : 2 ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6h' : y6 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h6h
  right
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (4:ℝ) ≤ y2*y2 := sq_ge_4 y2 h2l
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith) (le_sqrt8 y2 h2h)
  have hx3l : (6.0650528:ℝ) ≤ y3*y3 := by
    have h := sq_ge_hminus y3 h3l'
    linarith
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith [mi_hminus_prop.1]) h3h'
  have hx4l : (6.0650528:ℝ) ≤ y4*y4 := by
    have h := sq_ge_hminus y4 h4l'
    linarith
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith [mi_hminus_prop.1]) h4h'
  have hx5l : (6.0650528:ℝ) ≤ y5*y5 := by
    have h := sq_ge_hminus y5 h5l'
    linarith
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith [mi_hminus_prop.1]) h5h'
  have hx6l : (4:ℝ) ≤ y6*y6 := sq_ge_4 y6 h6l'
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith) (le_sqrt8 y6 h6h')
  have hx2w : (4:ℝ) ≤ y2*y2 := by linarith [hx2l]
  have hx3w : (5.76:ℝ) ≤ y3*y3 := by linarith [hx3l]
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have hx5w : (4:ℝ) ≤ y5*y5 := by linarith [hx5l]
  have hx6w : (4:ℝ) ≤ y6*y6 := by linarith [hx6l]
  have s6 := H_mono_6 4 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx6l hx6h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h hx5w hx5h
  have s5 := H_mono_5 6.0650528 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 4 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx5l hx5h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s4 := H_mono_4 6.0650528 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 6.0650528 4 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx4l hx4h
    hx1l hx1h hx2w hx2h hx3w hx3h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s3 := H_mono_3 6.0650528 (y3*y3) (y1*y1) (y2*y2) 6.0650528 6.0650528 4 (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) hx3l hx3h
    hx1l hx1h hx2w hx2h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s2 := H_mono_2 4 (y2*y2) (y1*y1) 6.0650528 6.0650528 6.0650528 4 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx2l hx2h
    hx1l hx1h (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s1 := H_mono_1 6.0650528 (y1*y1) 4 6.0650528 6.0650528 6.0650528 4 (by norm_num : (6.0650528:ℝ) ≤ (6.0650528:ℝ)) hx1l hx1h
    (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have hcorner : (69:ℝ) ≤ rhoX 6.0650528 4 6.0650528 6.0650528 6.0650528 4 - 8 * deltaX 6.0650528 4 6.0650528 6.0650528 6.0650528 4 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd100 : (100:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge _ _ _ _ _ _ (by linarith) hx1h (by linarith) hx2h (by linarith) hx3h (by linarith) hx4h (by linarith) hx5h (by linarith) hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

/-- W2-1: `nliRestZTGIJCF4_1_1_0_1` (rad2 branch; ZTGIJCF4 1 1 0 1). -/
theorem nliRestZTGIJCF4_1_1_0_1 : bank_ZTGIJCF4_1_1_0_1 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h3l' : 2 * hminus ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3h' : y3 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h3h
  have h4l' : 2 * hminus ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4h' : y4 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h4h
  have h5l' : 2 ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5h' : y5 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h5h
  have h6l' : 2 * hminus ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6h' : y6 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h6h
  right
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (4:ℝ) ≤ y2*y2 := sq_ge_4 y2 h2l
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith) (le_sqrt8 y2 h2h)
  have hx3l : (6.0650528:ℝ) ≤ y3*y3 := by
    have h := sq_ge_hminus y3 h3l'
    linarith
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith [mi_hminus_prop.1]) h3h'
  have hx4l : (6.0650528:ℝ) ≤ y4*y4 := by
    have h := sq_ge_hminus y4 h4l'
    linarith
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith [mi_hminus_prop.1]) h4h'
  have hx5l : (4:ℝ) ≤ y5*y5 := sq_ge_4 y5 h5l'
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith) (le_sqrt8 y5 h5h')
  have hx6l : (6.0650528:ℝ) ≤ y6*y6 := by
    have h := sq_ge_hminus y6 h6l'
    linarith
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith [mi_hminus_prop.1]) h6h'
  have hx2w : (4:ℝ) ≤ y2*y2 := by linarith [hx2l]
  have hx3w : (5.76:ℝ) ≤ y3*y3 := by linarith [hx3l]
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have hx5w : (4:ℝ) ≤ y5*y5 := by linarith [hx5l]
  have hx6w : (4:ℝ) ≤ y6*y6 := by linarith [hx6l]
  have s6 := H_mono_6 6.0650528 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx6l hx6h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h hx5w hx5h
  have s5 := H_mono_5 4 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 6.0650528 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx5l hx5h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s4 := H_mono_4 6.0650528 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 4 6.0650528 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx4l hx4h
    hx1l hx1h hx2w hx2h hx3w hx3h (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s3 := H_mono_3 6.0650528 (y3*y3) (y1*y1) (y2*y2) 6.0650528 4 6.0650528 (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) hx3l hx3h
    hx1l hx1h hx2w hx2h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s2 := H_mono_2 4 (y2*y2) (y1*y1) 6.0650528 6.0650528 4 6.0650528 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx2l hx2h
    hx1l hx1h (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s1 := H_mono_1 6.0650528 (y1*y1) 4 6.0650528 6.0650528 4 6.0650528 (by norm_num : (6.0650528:ℝ) ≤ (6.0650528:ℝ)) hx1l hx1h
    (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have hcorner : (16:ℝ) ≤ rhoX 6.0650528 4 6.0650528 6.0650528 4 6.0650528 - 8 * deltaX 6.0650528 4 6.0650528 6.0650528 4 6.0650528 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd100 : (100:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge _ _ _ _ _ _ (by linarith) hx1h (by linarith) hx2h (by linarith) hx3h (by linarith) hx4h (by linarith) hx5h (by linarith) hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

/-- W2-1: `nliRestZTGIJCF4_1_0_1_1` (rad2 branch; ZTGIJCF4 1 0 1 1). -/
theorem nliRestZTGIJCF4_1_0_1_1 : bank_ZTGIJCF4_1_0_1_1 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h3l' : 2 * hminus ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3h' : y3 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h3h
  have h4l' : 2 ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4h' : y4 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h4h
  have h5l' : 2 * hminus ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5h' : y5 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h5h
  have h6l' : 2 * hminus ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6h' : y6 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h6h
  right
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (4:ℝ) ≤ y2*y2 := sq_ge_4 y2 h2l
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith) (le_sqrt8 y2 h2h)
  have hx3l : (6.0650528:ℝ) ≤ y3*y3 := by
    have h := sq_ge_hminus y3 h3l'
    linarith
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith [mi_hminus_prop.1]) h3h'
  have hx4l : (4:ℝ) ≤ y4*y4 := sq_ge_4 y4 h4l'
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith) (le_sqrt8 y4 h4h')
  have hx5l : (6.0650528:ℝ) ≤ y5*y5 := by
    have h := sq_ge_hminus y5 h5l'
    linarith
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith [mi_hminus_prop.1]) h5h'
  have hx6l : (6.0650528:ℝ) ≤ y6*y6 := by
    have h := sq_ge_hminus y6 h6l'
    linarith
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith [mi_hminus_prop.1]) h6h'
  have hx2w : (4:ℝ) ≤ y2*y2 := by linarith [hx2l]
  have hx3w : (5.76:ℝ) ≤ y3*y3 := by linarith [hx3l]
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have hx5w : (4:ℝ) ≤ y5*y5 := by linarith [hx5l]
  have hx6w : (4:ℝ) ≤ y6*y6 := by linarith [hx6l]
  have s6 := H_mono_6 6.0650528 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx6l hx6h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h hx5w hx5h
  have s5 := H_mono_5 6.0650528 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 6.0650528 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx5l hx5h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s4 := H_mono_4 4 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 6.0650528 6.0650528 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx4l hx4h
    hx1l hx1h hx2w hx2h hx3w hx3h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s3 := H_mono_3 6.0650528 (y3*y3) (y1*y1) (y2*y2) 4 6.0650528 6.0650528 (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) hx3l hx3h
    hx1l hx1h hx2w hx2h (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s2 := H_mono_2 4 (y2*y2) (y1*y1) 6.0650528 4 6.0650528 6.0650528 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx2l hx2h
    hx1l hx1h (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have s1 := H_mono_1 6.0650528 (y1*y1) 4 6.0650528 4 6.0650528 6.0650528 (by norm_num : (6.0650528:ℝ) ≤ (6.0650528:ℝ)) hx1l hx1h
    (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ))
  have hcorner : (69:ℝ) ≤ rhoX 6.0650528 4 6.0650528 4 6.0650528 6.0650528 - 8 * deltaX 6.0650528 4 6.0650528 4 6.0650528 6.0650528 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd100 : (100:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge _ _ _ _ _ _ (by linarith) hx1h (by linarith) hx2h (by linarith) hx3h (by linarith) hx4h (by linarith) hx5h (by linarith) hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin

/-- W2-1: `nliRestZTGIJCF4_1_0_1_0` (rad2 branch; ZTGIJCF4 1 0 1 0). -/
theorem nliRestZTGIJCF4_1_0_1_0 : bank_ZTGIJCF4_1_0_1_0 := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have h3l' : 2 * hminus ≤ y3 := by simpa [bank_ZTGIJCF4lo] using h3l
  have h3h' : y3 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h3h
  have h4l' : 2 ≤ y4 := by simpa [bank_ZTGIJCF4lo] using h4l
  have h4h' : y4 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h4h
  have h5l' : 2 * hminus ≤ y5 := by simpa [bank_ZTGIJCF4lo] using h5l
  have h5h' : y5 ≤ Real.sqrt 8 := by simpa [bank_ZTGIJCF4hi] using h5h
  have h6l' : 2 ≤ y6 := by simpa [bank_ZTGIJCF4lo] using h6l
  have h6h' : y6 ≤ 2 * hminus := by simpa [bank_ZTGIJCF4hi] using h6h
  right
  have hx1l : (6.0650528:ℝ) ≤ y1*y1 := by
    have h := sq_ge_hminus y1 h1l
    linarith
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (4:ℝ) ≤ y2*y2 := sq_ge_4 y2 h2l
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith) (le_sqrt8 y2 h2h)
  have hx3l : (6.0650528:ℝ) ≤ y3*y3 := by
    have h := sq_ge_hminus y3 h3l'
    linarith
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith [mi_hminus_prop.1]) h3h'
  have hx4l : (4:ℝ) ≤ y4*y4 := sq_ge_4 y4 h4l'
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith) (le_sqrt8 y4 h4h')
  have hx5l : (6.0650528:ℝ) ≤ y5*y5 := by
    have h := sq_ge_hminus y5 h5l'
    linarith
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith [mi_hminus_prop.1]) h5h'
  have hx6l : (4:ℝ) ≤ y6*y6 := sq_ge_4 y6 h6l'
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith) (le_sqrt8 y6 h6h')
  have hx2w : (4:ℝ) ≤ y2*y2 := by linarith [hx2l]
  have hx3w : (5.76:ℝ) ≤ y3*y3 := by linarith [hx3l]
  have hx4w : (4:ℝ) ≤ y4*y4 := by linarith [hx4l]
  have hx5w : (4:ℝ) ≤ y5*y5 := by linarith [hx5l]
  have hx6w : (4:ℝ) ≤ y6*y6 := by linarith [hx6l]
  have s6 := H_mono_6 4 (y6*y6) (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx6l hx6h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h hx5w hx5h
  have s5 := H_mono_5 6.0650528 (y5*y5) (y1*y1) (y2*y2) (y3*y3) (y4*y4) 4 (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) hx5l hx5h
    hx1l hx1h hx2w hx2h hx3w hx3h hx4w hx4h (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s4 := H_mono_4 4 (y4*y4) (y1*y1) (y2*y2) (y3*y3) 6.0650528 4 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx4l hx4h
    hx1l hx1h hx2w hx2h hx3w hx3h (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s3 := H_mono_3 6.0650528 (y3*y3) (y1*y1) (y2*y2) 4 6.0650528 4 (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) hx3l hx3h
    hx1l hx1h hx2w hx2h (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s2 := H_mono_2 4 (y2*y2) (y1*y1) 6.0650528 4 6.0650528 4 (by norm_num : (4:ℝ) ≤ (4:ℝ)) hx2l hx2h
    hx1l hx1h (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have s1 := H_mono_1 6.0650528 (y1*y1) 4 6.0650528 4 6.0650528 4 (by norm_num : (6.0650528:ℝ) ≤ (6.0650528:ℝ)) hx1l hx1h
    (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (5.76:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (6.0650528:ℝ)) (by norm_num : (6.0650528:ℝ) ≤ (8:ℝ)) (by norm_num : (4:ℝ) ≤ (4:ℝ)) (by norm_num : (4:ℝ) ≤ (8:ℝ))
  have hcorner : (19:ℝ) ≤ rhoX 6.0650528 4 6.0650528 4 6.0650528 4 - 8 * deltaX 6.0650528 4 6.0650528 4 6.0650528 4 := by
    norm_num [rhoX, deltaX]
  have hH : (0:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) -
      8 * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    linarith [hcorner, s1, s2, s3, s4, s5, s6]
  have hd100 : (100:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    dX_box_ge _ _ _ _ _ _ (by linarith) hx1h (by linarith) hx2h (by linarith) hx3h (by linarith) hx4h (by linarith) hx5h (by linarith) hx6h
  have hfin : (2:ℝ) < rhoX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) /
      (deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4) := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) * 4)]
    nlinarith
  unfold yOfX rad2X
  exact hfin
#print axioms Kepler.NliBanks4.nliRestZTGIJCF4_1_1_1_1
#print axioms Kepler.NliBanks4.nliRestZTGIJCF4_1_1_1_0
#print axioms Kepler.NliBanks4.nliRestZTGIJCF4_1_1_0_1
#print axioms Kepler.NliBanks4.nliRestZTGIJCF4_1_0_1_1
#print axioms Kepler.NliBanks4.nliRestZTGIJCF4_1_0_1_0

end Kepler.NliBanks4
