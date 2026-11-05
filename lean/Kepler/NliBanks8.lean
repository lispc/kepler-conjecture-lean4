import Kepler.NliBanks7

/-!
Kepler.NliBanks8 — W3 lane `nli-unknown-w3`, task 3 (GCKBQEA), part 3.

Core positivity of `gckbP = 4·x1·deltaX − (0.6936)²·(deltaX4)²` on the box
(concavity in `x2 … x6` reduces to the 32 vertex lines of `Kepler.NliBanks6`),
the three `dihXf` branch lemmas, and `nliRestGCKBQEA`.
-/

set_option maxHeartbeats 4000000

namespace Kepler.NliBanks8
open Kepler.Text
open Kepler.NliBanks3
open Kepler.NliBanks6
open Kepler.NliBanks7

/-- `gckbP > 0` on `x1 ∈ [6.06883225, 7.02674064]`, `x2 … x6 ∈ [4, 8]`. -/
theorem gckbP_pos (x1 x2 x3 x4 x5 x6 : ℝ)
    (h1l : (6.06883225:ℝ) ≤ x1) (h1h : x1 ≤ 7.02674064)
    (h2 : (4:ℝ) ≤ x2) (h2h : x2 ≤ 8) (h3 : (4:ℝ) ≤ x3) (h3h : x3 ≤ 8)
    (h4 : (4:ℝ) ≤ x4) (h4h : x4 ≤ 8) (h5 : (4:ℝ) ≤ x5) (h5h : x5 ≤ 8)
    (h6 : (4:ℝ) ≤ x6) (h6h : x6 ≤ 8) :
    (0:ℝ) < gckbP x1 x2 x3 x4 x5 x6 := by
  refine lt_of_lt_of_le ?_ (P_concave_2 x1 x3 x4 x5 x6 h1l h1h h3 h3h h4 h4h h5 h5h h6 h6h 4 8 x2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h2 h2h)
  refine lt_min ?_ ?_
  ·
    refine lt_of_lt_of_le ?_ (P_concave_3 x1 4 x4 x5 x6 h1l h1h (by norm_num) (by norm_num) h4 h4h h5 h5h h6 h6h 4 8 x3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3 h3h)
    refine lt_min ?_ ?_
    ·
      refine lt_of_lt_of_le ?_ (P_concave_4 x1 4 4 x5 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h h6 h6h 4 8 x4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h4 h4h)
      refine lt_min ?_ ?_
      ·
        refine lt_of_lt_of_le ?_ (P_concave_5 x1 4 4 4 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h 4 8 x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h)
        refine lt_min ?_ ?_
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 4 4 4 4 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_44444 x1 h1l h1h
          ·
            exact line_44448 x1 h1l h1h
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 4 4 4 8 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_44484 x1 h1l h1h
          ·
            exact line_44488 x1 h1l h1h
      ·
        refine lt_of_lt_of_le ?_ (P_concave_5 x1 4 4 8 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h 4 8 x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h)
        refine lt_min ?_ ?_
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 4 4 8 4 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_44844 x1 h1l h1h
          ·
            exact line_44848 x1 h1l h1h
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 4 4 8 8 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_44884 x1 h1l h1h
          ·
            exact line_44888 x1 h1l h1h
    ·
      refine lt_of_lt_of_le ?_ (P_concave_4 x1 4 8 x5 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h h6 h6h 4 8 x4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h4 h4h)
      refine lt_min ?_ ?_
      ·
        refine lt_of_lt_of_le ?_ (P_concave_5 x1 4 8 4 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h 4 8 x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h)
        refine lt_min ?_ ?_
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 4 8 4 4 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_48444 x1 h1l h1h
          ·
            exact line_48448 x1 h1l h1h
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 4 8 4 8 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_48484 x1 h1l h1h
          ·
            exact line_48488 x1 h1l h1h
      ·
        refine lt_of_lt_of_le ?_ (P_concave_5 x1 4 8 8 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h 4 8 x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h)
        refine lt_min ?_ ?_
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 4 8 8 4 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_48844 x1 h1l h1h
          ·
            exact line_48848 x1 h1l h1h
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 4 8 8 8 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_48884 x1 h1l h1h
          ·
            exact line_48888 x1 h1l h1h
  ·
    refine lt_of_lt_of_le ?_ (P_concave_3 x1 8 x4 x5 x6 h1l h1h (by norm_num) (by norm_num) h4 h4h h5 h5h h6 h6h 4 8 x3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h3 h3h)
    refine lt_min ?_ ?_
    ·
      refine lt_of_lt_of_le ?_ (P_concave_4 x1 8 4 x5 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h h6 h6h 4 8 x4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h4 h4h)
      refine lt_min ?_ ?_
      ·
        refine lt_of_lt_of_le ?_ (P_concave_5 x1 8 4 4 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h 4 8 x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h)
        refine lt_min ?_ ?_
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 8 4 4 4 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_84444 x1 h1l h1h
          ·
            exact line_84448 x1 h1l h1h
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 8 4 4 8 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_84484 x1 h1l h1h
          ·
            exact line_84488 x1 h1l h1h
      ·
        refine lt_of_lt_of_le ?_ (P_concave_5 x1 8 4 8 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h 4 8 x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h)
        refine lt_min ?_ ?_
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 8 4 8 4 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_84844 x1 h1l h1h
          ·
            exact line_84848 x1 h1l h1h
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 8 4 8 8 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_84884 x1 h1l h1h
          ·
            exact line_84888 x1 h1l h1h
    ·
      refine lt_of_lt_of_le ?_ (P_concave_4 x1 8 8 x5 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h h6 h6h 4 8 x4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h4 h4h)
      refine lt_min ?_ ?_
      ·
        refine lt_of_lt_of_le ?_ (P_concave_5 x1 8 8 4 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h 4 8 x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h)
        refine lt_min ?_ ?_
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 8 8 4 4 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_88444 x1 h1l h1h
          ·
            exact line_88448 x1 h1l h1h
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 8 8 4 8 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_88484 x1 h1l h1h
          ·
            exact line_88488 x1 h1l h1h
      ·
        refine lt_of_lt_of_le ?_ (P_concave_5 x1 8 8 8 x6 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h 4 8 x5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h5 h5h)
        refine lt_min ?_ ?_
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 8 8 8 4 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_88844 x1 h1l h1h
          ·
            exact line_88848 x1 h1l h1h
        ·
          refine lt_of_lt_of_le ?_ (P_concave_6 x1 8 8 8 8 h1l h1h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 8 x6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h6 h6h)
          refine lt_min ?_ ?_
          ·
            exact line_88884 x1 h1l h1h
          ·
            exact line_88888 x1 h1l h1h

/-! ## `dihXf` branch lemmas -/

theorem dihXf_gt_pi_div_two {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) (h4 : deltaX4 x1 x2 x3 x4 x5 x6 < 0) :
    Real.pi / 2 < dihXf x1 x2 x3 x4 x5 x6 := by
  have hX : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (by positivity)
  have hY : (0:ℝ) < -(deltaX4 x1 x2 x3 x4 x5 x6) := by linarith
  unfold dihXf
  have hpos : (0:ℝ) < atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6)) := by
    rw [atn2]
    by_cases hc : |(-(deltaX4 x1 x2 x3 x4 x5 x6))| < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
    · rw [if_pos hc]
      exact Real.arctan_pos.mpr (div_pos hY hX)
    · rw [if_neg hc, if_pos hY]
      have := Real.arctan_lt_pi_div_two (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) /
        (-(deltaX4 x1 x2 x3 x4 x5 x6)))
      linarith
  linarith

theorem dihXf_ge_pi_div_four {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6) (h4 : 0 ≤ deltaX4 x1 x2 x3 x4 x5 x6)
    (hle : deltaX4 x1 x2 x3 x4 x5 x6 ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) :
    Real.pi / 4 ≤ dihXf x1 x2 x3 x4 x5 x6 := by
  have hX : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (by positivity)
  unfold dihXf
  have hlow : -(Real.pi / 4) ≤ atn2 (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
      (-(deltaX4 x1 x2 x3 x4 x5 x6)) := by
    rw [atn2]
    by_cases hc : |(-(deltaX4 x1 x2 x3 x4 x5 x6))| < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
    · rw [if_pos hc]
      have harg : (-(1:ℝ)) ≤ (-(deltaX4 x1 x2 x3 x4 x5 x6)) /
          Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
        have h2 : deltaX4 x1 x2 x3 x4 x5 x6 /
            Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) ≤ 1 := by
          rw [div_le_one hX]; exact hle
        rw [neg_div]
        linarith
      have := Real.arctan_le_arctan_iff.mpr harg
      rwa [Real.arctan_neg, Real.arctan_one] at this
    · rw [if_neg hc]
      push_neg at hc
      have hAX : deltaX4 x1 x2 x3 x4 x5 x6 = Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
        have h2 : |(-(deltaX4 x1 x2 x3 x4 x5 x6))| = deltaX4 x1 x2 x3 x4 x5 x6 := by
          rw [abs_neg, abs_of_nonneg h4]
        rw [h2] at hc
        linarith
      have hY0 : ¬ (0:ℝ) < -(deltaX4 x1 x2 x3 x4 x5 x6) := by
        rw [hAX]; linarith
      rw [if_neg hY0]
      have hYneg : -(deltaX4 x1 x2 x3 x4 x5 x6) < 0 := by rw [hAX]; linarith
      rw [if_pos hYneg]
      have hratio : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) /
          (-(deltaX4 x1 x2 x3 x4 x5 x6)) = -1 := by
        rw [hAX]
        field_simp
      rw [hratio, Real.arctan_neg, Real.arctan_one]
      linarith
  linarith

theorem dihXf_eq_arctan {x1 x2 x3 x4 x5 x6 : ℝ} (h1 : 0 < x1)
    (hd : 0 < deltaX x1 x2 x3 x4 x5 x6)
    (hlt : Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) < deltaX4 x1 x2 x3 x4 x5 x6) :
    dihXf x1 x2 x3 x4 x5 x6 =
      Real.arctan (Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) / deltaX4 x1 x2 x3 x4 x5 x6) := by
  have hX : (0:ℝ) < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) :=
    Real.sqrt_pos.mpr (by positivity)
  have hA : (0:ℝ) < deltaX4 x1 x2 x3 x4 x5 x6 := by linarith
  unfold dihXf
  rw [atn2]
  rw [if_neg (by rw [abs_neg, abs_of_pos hA]; linarith)]
  rw [if_neg (by linarith : ¬ (0:ℝ) < -(deltaX4 x1 x2 x3 x4 x5 x6))]
  rw [if_pos (by linarith : -(deltaX4 x1 x2 x3 x4 x5 x6) < 0)]
  rw [show Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) / (-(deltaX4 x1 x2 x3 x4 x5 x6))
      = -(Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) / deltaX4 x1 x2 x3 x4 x5 x6) by
    field_simp]
  rw [Real.arctan_neg]
  ring

/-! ## GCKBQEA -/

/-- W3-3: `nliRestGCKBQEA` (`dihY > 0.606` on `[2hmin,2hplus]×[2,√8]⁵`). -/
theorem nliRestGCKBQEA : bank_GCKBQEA := by
  intro y1 y2 y3 y4 y5 y6 h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  have hm : (1.23175:ℝ) ≤ hminus := hminus_ge_123175
  have hx1l : (6.06883225:ℝ) ≤ y1*y1 := by
    have h2 : (2*1.23175:ℝ) ≤ y1 := by linarith
    nlinarith [sq_nonneg (y1 - 2*1.23175)]
  have hx1h : y1*y1 ≤ 7.02674064 := sq_le_hplus y1 (by linarith [mi_hminus_prop.1, h1l]) h1h
  have hx2l : (4:ℝ) ≤ y2*y2 := sq_ge_4 y2 h2l
  have hx2h : y2*y2 ≤ 8 := sq_le_8 y2 (by linarith) h2h
  have hx3l : (4:ℝ) ≤ y3*y3 := sq_ge_4 y3 h3l
  have hx3h : y3*y3 ≤ 8 := sq_le_8 y3 (by linarith) h3h
  have hx4l : (4:ℝ) ≤ y4*y4 := sq_ge_4 y4 h4l
  have hx4h : y4*y4 ≤ 8 := sq_le_8 y4 (by linarith) h4h
  have hx5l : (4:ℝ) ≤ y5*y5 := sq_ge_4 y5 h5l
  have hx5h : y5*y5 ≤ 8 := sq_le_8 y5 (by linarith) h5h
  have hx6l : (4:ℝ) ≤ y6*y6 := sq_ge_4 y6 h6l
  have hx6h : y6*y6 ≤ 8 := sq_le_8 y6 (by linarith) h6h
  have hΔ : (50:ℝ) ≤ deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    Kepler.NliBanks5.dX_box_ge_wide _ _ _ _ _ _ (by linarith) hx1h hx2l hx2h hx3l hx3h
      hx4l hx4h hx5l hx5h hx6l hx6h
  have hP : (0:ℝ) < gckbP (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    gckbP_pos _ _ _ _ _ _ hx1l hx1h hx2l hx2h hx3l hx3h hx4l hx4h hx5l hx5h hx6l hx6h
  set X := Real.sqrt (4 * (y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) with hXdef
  have hXsq : X^2 = 4 * (y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) :=
    Real.sq_sqrt (by positivity)
  have hXpos : (0:ℝ) < X := Real.sqrt_pos.mpr (by positivity)
  have hP' : (0.6936:ℝ)^2 * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))^2
      < 4 * (y1*y1) * deltaX (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
    have := hP
    unfold gckbP at this
    linarith
  have hlt : (0.6936:ℝ) * |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)| < X := by
    have hsq : ((0.6936:ℝ) * |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)|)^2 < X^2 := by
      rw [hXsq]
      have e : ((0.6936:ℝ) * |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)|)^2
          = (0.6936:ℝ)^2 * (deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6))^2 := by
        rw [mul_pow, sq_abs]
      rw [e]
      exact hP'
    have hnn : (0:ℝ) ≤ (0.6936:ℝ) * |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)| :=
      mul_nonneg (by norm_num) (abs_nonneg _)
    nlinarith [hsq, hnn, hXpos]
  have h1 : (0:ℝ) < y1*y1 := by linarith
  by_cases hneg : deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) < 0
  · have hb := dihXf_gt_pi_div_two h1 (by linarith) hneg
    unfold dihY
    linarith [Real.pi_gt_d2]
  · push_neg at hneg
    by_cases hle : deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) ≤ X
    · have hb := dihXf_ge_pi_div_four h1 (by linarith) hneg hle
      unfold dihY
      linarith [Real.pi_gt_d2]
    · push_neg at hle
      have heq := dihXf_eq_arctan h1 (by linarith) hle
      have hApos : (0:ℝ) < deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
        linarith [hXpos]
      have hratio : (0.6936:ℝ) < X / deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := by
        rw [lt_div_iff₀ hApos]
        have habs : |deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)|
            = deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6) := abs_of_pos hApos
        rw [habs] at hlt
        linarith
      have hmem : (0.606:ℝ) ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) :=
        ⟨by linarith [Real.pi_gt_d2], by linarith [Real.pi_gt_d2]⟩
      have hmono := Real.strictMonoOn_tan.lt_iff_lt hmem
        (Real.arctan_mem_Ioo (X / deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)))
      rw [Real.tan_arctan] at hmono
      have harc : (0.606:ℝ) < Real.arctan (X / deltaX4 (y1*y1) (y2*y2) (y3*y3) (y4*y4) (y5*y5) (y6*y6)) :=
        hmono.mp (by linarith [tan0606_lt, hratio])
      unfold dihY
      rw [heq]
      exact harc

#print axioms Kepler.NliBanks8.nliRestGCKBQEA

end Kepler.NliBanks8
