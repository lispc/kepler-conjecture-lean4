/-
Explicit-hstep residual consumers of the rational gamma4 corner tables.
The slice signs are assumptions of these theorems, not asserted facts.
-/
import Kepler.Text.ZTGG4Corners
import Kepler.Text.ZTGG4SliceKit
import Kepler.NliBanksZTGIJCF4Dih

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

noncomputable def ztg4Lo1100 : Fin 6 → ℝ := ![2.4635, 2, 2.4635, 2.4635, 2, 2]
noncomputable def ztg4Hi1100 : Fin 6 → ℝ := ![2.6508, 2.46352, Real.sqrt 8, Real.sqrt 8, 2.46352, 2.46352]
noncomputable def ztg4Cands1100 : Fin 6 → Finset ℝ := ![{2.4635, 2.52}, {2}, {2.4635, 2.52}, {2.4635, 2.52}, {2}, {2}]

noncomputable def ztg4Lo0110 : Fin 6 → ℝ := ![2.4635, 2, 2, 2.4635, 2.4635, 2]
noncomputable def ztg4Hi0110 : Fin 6 → ℝ := ![2.6508, 2.46352, 2.46352, Real.sqrt 8, Real.sqrt 8, 2.46352]
noncomputable def ztg4Cands0110 : Fin 6 → Finset ℝ := ![{2.4635, 2.52}, {2}, {2}, {2.4635, 2.52}, {2.4635, 2.52}, {2}]

noncomputable def ztg4Lo0101 : Fin 6 → ℝ := ![2.4635, 2, 2, 2.4635, 2, 2.4635]
noncomputable def ztg4Hi0101 : Fin 6 → ℝ := ![2.6508, 2.46352, 2.46352, Real.sqrt 8, 2.46352, Real.sqrt 8]
noncomputable def ztg4Cands0101 : Fin 6 → Finset ℝ := ![{2.4635, 2.52}, {2}, {2}, {2.4635, 2.52}, {2}, {2.4635, 2.52}]

noncomputable def ztg4Lo0011 : Fin 6 → ℝ := ![2.4635, 2, 2, 2, 2.4635, 2.4635]
noncomputable def ztg4Hi0011 : Fin 6 → ℝ := ![2.6508, 2.46352, 2.46352, 2.46352, Real.sqrt 8, Real.sqrt 8]
noncomputable def ztg4Cands0011 : Fin 6 → Finset ℝ := ![{2.4635, 2.52}, {2}, {2}, {2}, {2.4635, 2.52}, {2.4635, 2.52}]

/-! ## 1_1_0_0 -/

theorem ztg_g4_1_1_0_0_of_steps
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (ztg4Lo1100 j) (ztg4Hi1100 j)) →
      ∃ c ∈ ztg4Cands1100 i, ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x) :
    ∀ y1 y2 y3 y4 y5 y6, ztgBox 1 1 0 0 y1 y2 y3 y4 y5 y6 →
      (0.05 : ℝ) ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  intro y1 y2 y3 y4 y5 y6 hb
  rcases hb with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have hm := Kepler.NliBanks17.nb17_two_hminus_bounds
  norm_num [bank_ZTGIJCF4lo, bank_ZTGIJCF4hi] at h3l h3h h4l h4h h5l h5h h6l h6h
  have hne : ∀ i, (ztg4Cands1100 i).Nonempty := by
    intro i; fin_cases i <;> simp [ztg4Cands1100]
  have hsub : ∀ i, ∀ c ∈ ztg4Cands1100 i, c ∈ Set.Icc (ztg4Lo1100 i) (ztg4Hi1100 i) := by
    have hsqrtH : (2.4635 : ℝ) ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
    intro i c hc
    fin_cases i
    · simp [ztg4Cands1100] at hc
      rcases hc with rfl | rfl <;> norm_num [ztg4Lo1100, ztg4Hi1100]
    · simp [ztg4Cands1100] at hc
      obtain rfl := hc
      norm_num [ztg4Lo1100, ztg4Hi1100]
    · simp [ztg4Cands1100] at hc
      rcases hc with rfl | rfl
      · norm_num [ztg4Lo1100, ztg4Hi1100]
        norm_num at hsqrtH ⊢
        exact hsqrtH
      · norm_num [ztg4Lo1100, ztg4Hi1100]
        have hk := ztg_kink_le_sqrt8
        norm_num at hk ⊢
        exact hk
    · simp [ztg4Cands1100] at hc
      rcases hc with rfl | rfl
      · norm_num [ztg4Lo1100, ztg4Hi1100]
        norm_num at hsqrtH ⊢
        exact hsqrtH
      · norm_num [ztg4Lo1100, ztg4Hi1100]
        have hk := ztg_kink_le_sqrt8
        norm_num at hk ⊢
        exact hk
    · simp [ztg4Cands1100] at hc
      obtain rfl := hc
      norm_num [ztg4Lo1100, ztg4Hi1100]
    · simp [ztg4Cands1100] at hc
      obtain rfl := hc
      norm_num [ztg4Lo1100, ztg4Hi1100]
  have hcorner :
      ∀ c0 ∈ ztg4Cands1100 0,
      ∀ c1 ∈ ztg4Cands1100 1,
      ∀ c2 ∈ ztg4Cands1100 2,
      ∀ c3 ∈ ztg4Cands1100 3,
      ∀ c4 ∈ ztg4Cands1100 4,
      ∀ c5 ∈ ztg4Cands1100 5,
        (0.05 : ℝ) ≤ gamma4fgcy c0 c1 c2 c3 c4 c5 lmfun := by
    intro c0 hc0 c1 hc1 c2 hc2 c3 hc3 c4 hc4 c5 hc5
    simp [ztg4Cands1100, Finset.mem_insert, Finset.mem_singleton] at hc0 hc1 hc2 hc3 hc4 hc5
    obtain rfl := hc1
    obtain rfl := hc4
    obtain rfl := hc5
    rcases hc0 with rfl | rfl <;> rcases hc2 with rfl | rfl <;> rcases hc3 with rfl | rfl
    · have h := ztg4c_1100_0
      norm_num at h ⊢
      exact h
    · have h := ztg4c_1100_1
      norm_num at h ⊢
      exact h
    · have h := ztg4c_1100_2
      norm_num at h ⊢
      exact h
    · have h := ztg4c_1100_3
      norm_num at h ⊢
      exact h
    · have h := ztg4c_1100_4
      norm_num at h ⊢
      exact h
    · have h := ztg4c_1100_5
      norm_num at h ⊢
      exact h
    · have h := ztg4c_1100_6
      norm_num at h ⊢
      exact h
    · have h := ztg4c_1100_7
      norm_num at h ⊢
      exact h
  have hx0 : y1 ∈ Set.Icc (2.4635) (2.6508) := ⟨by linarith [hm.1, h1l], by norm_num [hplus] at h1h ⊢; exact h1h⟩
  have hx1 : y2 ∈ Set.Icc (2) (2.46352) := ⟨h2l, by linarith [hm.2, h2h]⟩
  have hx2 : y3 ∈ Set.Icc (2.4635) (Real.sqrt 8) := ⟨by linarith [hm.1, h3l], h3h⟩
  have hx3 : y4 ∈ Set.Icc (2.4635) (Real.sqrt 8) := ⟨by linarith [hm.1, h4l], h4h⟩
  have hx4 : y5 ∈ Set.Icc (2) (2.46352) := ⟨h5l, by linarith [hm.2, h5h]⟩
  have hx5 : y6 ∈ Set.Icc (2) (2.46352) := ⟨h6l, by linarith [hm.2, h6h]⟩
  have hmain := ztg_g4_lower_of_slice_corners (0.05 : ℝ)
    ztg4Lo1100 ztg4Hi1100 ztg4Cands1100 hne hsub hstep hcorner
  have hx : ∀ j, (![y1, y2, y3, y4, y5, y6] j) ∈
      Set.Icc (ztg4Lo1100 j) (ztg4Hi1100 j) := by
    intro j; fin_cases j
    · simpa [ztg4Lo1100, ztg4Hi1100] using hx0
    · simpa [ztg4Lo1100, ztg4Hi1100] using hx1
    · simpa [ztg4Lo1100, ztg4Hi1100] using hx2
    · simpa [ztg4Lo1100, ztg4Hi1100] using hx3
    · simpa [ztg4Lo1100, ztg4Hi1100] using hx4
    · simpa [ztg4Lo1100, ztg4Hi1100] using hx5
  have h := hmain ![y1, y2, y3, y4, y5, y6] hx
  simpa [ztg_g4_fun] using h

theorem bank_1_1_0_0_of_steps
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (ztg4Lo1100 j) (ztg4Hi1100 j)) →
      ∃ c ∈ ztg4Cands1100 i, ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x) :
    bank_ZTGIJCF4_1_1_0_0 := by
  refine ztg_of_global_bounds 1 1 0 0 0.05 1.008 (ztg_g4_1_1_0_0_of_steps hstep) ?_ ?_
  · intro y1 y2 y3 y4 y5 y6 hb
    rcases hb with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
    exact Kepler.NliBanksZTGIJCF4Dih.ztg_dihY_1_1_0_0
      h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-! ## 0_1_1_0 -/

theorem ztg_g4_0_1_1_0_of_steps
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (ztg4Lo0110 j) (ztg4Hi0110 j)) →
      ∃ c ∈ ztg4Cands0110 i, ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x) :
    ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 1 1 0 y1 y2 y3 y4 y5 y6 →
      (0.05 : ℝ) ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  intro y1 y2 y3 y4 y5 y6 hb
  rcases hb with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have hm := Kepler.NliBanks17.nb17_two_hminus_bounds
  norm_num [bank_ZTGIJCF4lo, bank_ZTGIJCF4hi] at h3l h3h h4l h4h h5l h5h h6l h6h
  have hne : ∀ i, (ztg4Cands0110 i).Nonempty := by
    intro i; fin_cases i <;> simp [ztg4Cands0110]
  have hsub : ∀ i, ∀ c ∈ ztg4Cands0110 i, c ∈ Set.Icc (ztg4Lo0110 i) (ztg4Hi0110 i) := by
    have hsqrtH : (2.4635 : ℝ) ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
    intro i c hc
    fin_cases i
    · simp [ztg4Cands0110] at hc
      rcases hc with rfl | rfl <;> norm_num [ztg4Lo0110, ztg4Hi0110]
    · simp [ztg4Cands0110] at hc
      obtain rfl := hc
      norm_num [ztg4Lo0110, ztg4Hi0110]
    · simp [ztg4Cands0110] at hc
      obtain rfl := hc
      norm_num [ztg4Lo0110, ztg4Hi0110]
    · simp [ztg4Cands0110] at hc
      rcases hc with rfl | rfl
      · norm_num [ztg4Lo0110, ztg4Hi0110]
        norm_num at hsqrtH ⊢
        exact hsqrtH
      · norm_num [ztg4Lo0110, ztg4Hi0110]
        have hk := ztg_kink_le_sqrt8
        norm_num at hk ⊢
        exact hk
    · simp [ztg4Cands0110] at hc
      rcases hc with rfl | rfl
      · norm_num [ztg4Lo0110, ztg4Hi0110]
        norm_num at hsqrtH ⊢
        exact hsqrtH
      · norm_num [ztg4Lo0110, ztg4Hi0110]
        have hk := ztg_kink_le_sqrt8
        norm_num at hk ⊢
        exact hk
    · simp [ztg4Cands0110] at hc
      obtain rfl := hc
      norm_num [ztg4Lo0110, ztg4Hi0110]
  have hcorner :
      ∀ c0 ∈ ztg4Cands0110 0,
      ∀ c1 ∈ ztg4Cands0110 1,
      ∀ c2 ∈ ztg4Cands0110 2,
      ∀ c3 ∈ ztg4Cands0110 3,
      ∀ c4 ∈ ztg4Cands0110 4,
      ∀ c5 ∈ ztg4Cands0110 5,
        (0.05 : ℝ) ≤ gamma4fgcy c0 c1 c2 c3 c4 c5 lmfun := by
    intro c0 hc0 c1 hc1 c2 hc2 c3 hc3 c4 hc4 c5 hc5
    simp [ztg4Cands0110, Finset.mem_insert, Finset.mem_singleton] at hc0 hc1 hc2 hc3 hc4 hc5
    obtain rfl := hc1
    obtain rfl := hc2
    obtain rfl := hc5
    rcases hc0 with rfl | rfl <;> rcases hc3 with rfl | rfl <;> rcases hc4 with rfl | rfl
    · have h := ztg4c_0110_0
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0110_1
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0110_2
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0110_3
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0110_4
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0110_5
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0110_6
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0110_7
      norm_num at h ⊢
      exact h
  have hx0 : y1 ∈ Set.Icc (2.4635) (2.6508) := ⟨by linarith [hm.1, h1l], by norm_num [hplus] at h1h ⊢; exact h1h⟩
  have hx1 : y2 ∈ Set.Icc (2) (2.46352) := ⟨h2l, by linarith [hm.2, h2h]⟩
  have hx2 : y3 ∈ Set.Icc (2) (2.46352) := ⟨h3l, by linarith [hm.2, h3h]⟩
  have hx3 : y4 ∈ Set.Icc (2.4635) (Real.sqrt 8) := ⟨by linarith [hm.1, h4l], h4h⟩
  have hx4 : y5 ∈ Set.Icc (2.4635) (Real.sqrt 8) := ⟨by linarith [hm.1, h5l], h5h⟩
  have hx5 : y6 ∈ Set.Icc (2) (2.46352) := ⟨h6l, by linarith [hm.2, h6h]⟩
  have hmain := ztg_g4_lower_of_slice_corners (0.05 : ℝ)
    ztg4Lo0110 ztg4Hi0110 ztg4Cands0110 hne hsub hstep hcorner
  have hx : ∀ j, (![y1, y2, y3, y4, y5, y6] j) ∈
      Set.Icc (ztg4Lo0110 j) (ztg4Hi0110 j) := by
    intro j; fin_cases j
    · simpa [ztg4Lo0110, ztg4Hi0110] using hx0
    · simpa [ztg4Lo0110, ztg4Hi0110] using hx1
    · simpa [ztg4Lo0110, ztg4Hi0110] using hx2
    · simpa [ztg4Lo0110, ztg4Hi0110] using hx3
    · simpa [ztg4Lo0110, ztg4Hi0110] using hx4
    · simpa [ztg4Lo0110, ztg4Hi0110] using hx5
  have h := hmain ![y1, y2, y3, y4, y5, y6] hx
  simpa [ztg_g4_fun] using h

theorem bank_0_1_1_0_of_steps
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (ztg4Lo0110 j) (ztg4Hi0110 j)) →
      ∃ c ∈ ztg4Cands0110 i, ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x) :
    bank_ZTGIJCF4_0_1_1_0 := by
  refine ztg_of_global_bounds 0 1 1 0 0.05 1.008 (ztg_g4_0_1_1_0_of_steps hstep) ?_ ?_
  · intro y1 y2 y3 y4 y5 y6 hb
    rcases hb with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
    exact Kepler.NliBanksZTGIJCF4Dih.ztg_dihY_0_1_1_0
      h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-! ## 0_1_0_1 -/

theorem ztg_g4_0_1_0_1_of_steps
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (ztg4Lo0101 j) (ztg4Hi0101 j)) →
      ∃ c ∈ ztg4Cands0101 i, ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x) :
    ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 1 0 1 y1 y2 y3 y4 y5 y6 →
      (0.05 : ℝ) ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  intro y1 y2 y3 y4 y5 y6 hb
  rcases hb with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have hm := Kepler.NliBanks17.nb17_two_hminus_bounds
  norm_num [bank_ZTGIJCF4lo, bank_ZTGIJCF4hi] at h3l h3h h4l h4h h5l h5h h6l h6h
  have hne : ∀ i, (ztg4Cands0101 i).Nonempty := by
    intro i; fin_cases i <;> simp [ztg4Cands0101]
  have hsub : ∀ i, ∀ c ∈ ztg4Cands0101 i, c ∈ Set.Icc (ztg4Lo0101 i) (ztg4Hi0101 i) := by
    have hsqrtH : (2.4635 : ℝ) ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
    intro i c hc
    fin_cases i
    · simp [ztg4Cands0101] at hc
      rcases hc with rfl | rfl <;> norm_num [ztg4Lo0101, ztg4Hi0101]
    · simp [ztg4Cands0101] at hc
      obtain rfl := hc
      norm_num [ztg4Lo0101, ztg4Hi0101]
    · simp [ztg4Cands0101] at hc
      obtain rfl := hc
      norm_num [ztg4Lo0101, ztg4Hi0101]
    · simp [ztg4Cands0101] at hc
      rcases hc with rfl | rfl
      · norm_num [ztg4Lo0101, ztg4Hi0101]
        norm_num at hsqrtH ⊢
        exact hsqrtH
      · norm_num [ztg4Lo0101, ztg4Hi0101]
        have hk := ztg_kink_le_sqrt8
        norm_num at hk ⊢
        exact hk
    · simp [ztg4Cands0101] at hc
      obtain rfl := hc
      norm_num [ztg4Lo0101, ztg4Hi0101]
    · simp [ztg4Cands0101] at hc
      rcases hc with rfl | rfl
      · norm_num [ztg4Lo0101, ztg4Hi0101]
        norm_num at hsqrtH ⊢
        exact hsqrtH
      · norm_num [ztg4Lo0101, ztg4Hi0101]
        have hk := ztg_kink_le_sqrt8
        norm_num at hk ⊢
        exact hk
  have hcorner :
      ∀ c0 ∈ ztg4Cands0101 0,
      ∀ c1 ∈ ztg4Cands0101 1,
      ∀ c2 ∈ ztg4Cands0101 2,
      ∀ c3 ∈ ztg4Cands0101 3,
      ∀ c4 ∈ ztg4Cands0101 4,
      ∀ c5 ∈ ztg4Cands0101 5,
        (0.05 : ℝ) ≤ gamma4fgcy c0 c1 c2 c3 c4 c5 lmfun := by
    intro c0 hc0 c1 hc1 c2 hc2 c3 hc3 c4 hc4 c5 hc5
    simp [ztg4Cands0101, Finset.mem_insert, Finset.mem_singleton] at hc0 hc1 hc2 hc3 hc4 hc5
    obtain rfl := hc1
    obtain rfl := hc2
    obtain rfl := hc4
    rcases hc0 with rfl | rfl <;> rcases hc3 with rfl | rfl <;> rcases hc5 with rfl | rfl
    · have h := ztg4c_0101_0
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0101_1
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0101_2
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0101_3
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0101_4
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0101_5
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0101_6
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0101_7
      norm_num at h ⊢
      exact h
  have hx0 : y1 ∈ Set.Icc (2.4635) (2.6508) := ⟨by linarith [hm.1, h1l], by norm_num [hplus] at h1h ⊢; exact h1h⟩
  have hx1 : y2 ∈ Set.Icc (2) (2.46352) := ⟨h2l, by linarith [hm.2, h2h]⟩
  have hx2 : y3 ∈ Set.Icc (2) (2.46352) := ⟨h3l, by linarith [hm.2, h3h]⟩
  have hx3 : y4 ∈ Set.Icc (2.4635) (Real.sqrt 8) := ⟨by linarith [hm.1, h4l], h4h⟩
  have hx4 : y5 ∈ Set.Icc (2) (2.46352) := ⟨h5l, by linarith [hm.2, h5h]⟩
  have hx5 : y6 ∈ Set.Icc (2.4635) (Real.sqrt 8) := ⟨by linarith [hm.1, h6l], h6h⟩
  have hmain := ztg_g4_lower_of_slice_corners (0.05 : ℝ)
    ztg4Lo0101 ztg4Hi0101 ztg4Cands0101 hne hsub hstep hcorner
  have hx : ∀ j, (![y1, y2, y3, y4, y5, y6] j) ∈
      Set.Icc (ztg4Lo0101 j) (ztg4Hi0101 j) := by
    intro j; fin_cases j
    · simpa [ztg4Lo0101, ztg4Hi0101] using hx0
    · simpa [ztg4Lo0101, ztg4Hi0101] using hx1
    · simpa [ztg4Lo0101, ztg4Hi0101] using hx2
    · simpa [ztg4Lo0101, ztg4Hi0101] using hx3
    · simpa [ztg4Lo0101, ztg4Hi0101] using hx4
    · simpa [ztg4Lo0101, ztg4Hi0101] using hx5
  have h := hmain ![y1, y2, y3, y4, y5, y6] hx
  simpa [ztg_g4_fun] using h

theorem bank_0_1_0_1_of_steps
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (ztg4Lo0101 j) (ztg4Hi0101 j)) →
      ∃ c ∈ ztg4Cands0101 i, ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x) :
    bank_ZTGIJCF4_0_1_0_1 := by
  refine ztg_of_global_bounds 0 1 0 1 0.05 1.008 (ztg_g4_0_1_0_1_of_steps hstep) ?_ ?_
  · intro y1 y2 y3 y4 y5 y6 hb
    rcases hb with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
    exact Kepler.NliBanksZTGIJCF4Dih.ztg_dihY_0_1_0_1
      h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-! ## 0_0_1_1 -/

theorem ztg_g4_0_0_1_1_of_steps
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (ztg4Lo0011 j) (ztg4Hi0011 j)) →
      ∃ c ∈ ztg4Cands0011 i, ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x) :
    ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 1 1 y1 y2 y3 y4 y5 y6 →
      (0.065 : ℝ) ≤ gamma4fgcy y1 y2 y3 y4 y5 y6 lmfun := by
  intro y1 y2 y3 y4 y5 y6 hb
  rcases hb with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have hm := Kepler.NliBanks17.nb17_two_hminus_bounds
  norm_num [bank_ZTGIJCF4lo, bank_ZTGIJCF4hi] at h3l h3h h4l h4h h5l h5h h6l h6h
  have hne : ∀ i, (ztg4Cands0011 i).Nonempty := by
    intro i; fin_cases i <;> simp [ztg4Cands0011]
  have hsub : ∀ i, ∀ c ∈ ztg4Cands0011 i, c ∈ Set.Icc (ztg4Lo0011 i) (ztg4Hi0011 i) := by
    have hsqrtH : (2.4635 : ℝ) ≤ Real.sqrt 8 := Real.le_sqrt_of_sq_le (by norm_num)
    intro i c hc
    fin_cases i
    · simp [ztg4Cands0011] at hc
      rcases hc with rfl | rfl <;> norm_num [ztg4Lo0011, ztg4Hi0011]
    · simp [ztg4Cands0011] at hc
      obtain rfl := hc
      norm_num [ztg4Lo0011, ztg4Hi0011]
    · simp [ztg4Cands0011] at hc
      obtain rfl := hc
      norm_num [ztg4Lo0011, ztg4Hi0011]
    · simp [ztg4Cands0011] at hc
      obtain rfl := hc
      norm_num [ztg4Lo0011, ztg4Hi0011]
    · simp [ztg4Cands0011] at hc
      rcases hc with rfl | rfl
      · norm_num [ztg4Lo0011, ztg4Hi0011]
        norm_num at hsqrtH ⊢
        exact hsqrtH
      · norm_num [ztg4Lo0011, ztg4Hi0011]
        have hk := ztg_kink_le_sqrt8
        norm_num at hk ⊢
        exact hk
    · simp [ztg4Cands0011] at hc
      rcases hc with rfl | rfl
      · norm_num [ztg4Lo0011, ztg4Hi0011]
        norm_num at hsqrtH ⊢
        exact hsqrtH
      · norm_num [ztg4Lo0011, ztg4Hi0011]
        have hk := ztg_kink_le_sqrt8
        norm_num at hk ⊢
        exact hk
  have hcorner :
      ∀ c0 ∈ ztg4Cands0011 0,
      ∀ c1 ∈ ztg4Cands0011 1,
      ∀ c2 ∈ ztg4Cands0011 2,
      ∀ c3 ∈ ztg4Cands0011 3,
      ∀ c4 ∈ ztg4Cands0011 4,
      ∀ c5 ∈ ztg4Cands0011 5,
        (0.065 : ℝ) ≤ gamma4fgcy c0 c1 c2 c3 c4 c5 lmfun := by
    intro c0 hc0 c1 hc1 c2 hc2 c3 hc3 c4 hc4 c5 hc5
    simp [ztg4Cands0011, Finset.mem_insert, Finset.mem_singleton] at hc0 hc1 hc2 hc3 hc4 hc5
    obtain rfl := hc1
    obtain rfl := hc2
    obtain rfl := hc3
    rcases hc0 with rfl | rfl <;> rcases hc4 with rfl | rfl <;> rcases hc5 with rfl | rfl
    · have h := ztg4c_0011_0
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0011_1
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0011_2
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0011_3
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0011_4
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0011_5
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0011_6
      norm_num at h ⊢
      exact h
    · have h := ztg4c_0011_7
      norm_num at h ⊢
      exact h
  have hx0 : y1 ∈ Set.Icc (2.4635) (2.6508) := ⟨by linarith [hm.1, h1l], by norm_num [hplus] at h1h ⊢; exact h1h⟩
  have hx1 : y2 ∈ Set.Icc (2) (2.46352) := ⟨h2l, by linarith [hm.2, h2h]⟩
  have hx2 : y3 ∈ Set.Icc (2) (2.46352) := ⟨h3l, by linarith [hm.2, h3h]⟩
  have hx3 : y4 ∈ Set.Icc (2) (2.46352) := ⟨h4l, by linarith [hm.2, h4h]⟩
  have hx4 : y5 ∈ Set.Icc (2.4635) (Real.sqrt 8) := ⟨by linarith [hm.1, h5l], h5h⟩
  have hx5 : y6 ∈ Set.Icc (2.4635) (Real.sqrt 8) := ⟨by linarith [hm.1, h6l], h6h⟩
  have hmain := ztg_g4_lower_of_slice_corners (0.065 : ℝ)
    ztg4Lo0011 ztg4Hi0011 ztg4Cands0011 hne hsub hstep hcorner
  have hx : ∀ j, (![y1, y2, y3, y4, y5, y6] j) ∈
      Set.Icc (ztg4Lo0011 j) (ztg4Hi0011 j) := by
    intro j; fin_cases j
    · simpa [ztg4Lo0011, ztg4Hi0011] using hx0
    · simpa [ztg4Lo0011, ztg4Hi0011] using hx1
    · simpa [ztg4Lo0011, ztg4Hi0011] using hx2
    · simpa [ztg4Lo0011, ztg4Hi0011] using hx3
    · simpa [ztg4Lo0011, ztg4Hi0011] using hx4
    · simpa [ztg4Lo0011, ztg4Hi0011] using hx5
  have h := hmain ![y1, y2, y3, y4, y5, y6] hx
  simpa [ztg_g4_fun] using h

theorem bank_0_0_1_1_of_steps
    (hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (ztg4Lo0011 j) (ztg4Hi0011 j)) →
      ∃ c ∈ ztg4Cands0011 i, ztg_g4_fun (Function.update x i c) ≤ ztg_g4_fun x) :
    bank_ZTGIJCF4_0_0_1_1 := by
  refine ztg_of_global_bounds 0 0 1 1 0.065 0.875 (ztg_g4_0_0_1_1_of_steps hstep) ?_ ?_
  · intro y1 y2 y3 y4 y5 y6 hb
    rcases hb with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
    exact Kepler.NliBanksZTGIJCF4Dih.ztg_dihY_0_0_1_1
      h1l h1h h2l h2h h3l h3h h4l h4h h5l h5h h6l h6h
  · norm_num [ztgW, ztgM, bankGenMid, aSpine5, bSpine5, betaBumpLb]

/-! ## Axiom audit -/

#print axioms ztg4Lo1100
#print axioms ztg4Hi1100
#print axioms ztg4Cands1100
#print axioms ztg4Lo0110
#print axioms ztg4Hi0110
#print axioms ztg4Cands0110
#print axioms ztg4Lo0101
#print axioms ztg4Hi0101
#print axioms ztg4Cands0101
#print axioms ztg4Lo0011
#print axioms ztg4Hi0011
#print axioms ztg4Cands0011
#print axioms ztg_g4_1_1_0_0_of_steps
#print axioms bank_1_1_0_0_of_steps
#print axioms ztg_g4_0_1_1_0_of_steps
#print axioms bank_0_1_1_0_of_steps
#print axioms ztg_g4_0_1_0_1_of_steps
#print axioms bank_0_1_0_1_of_steps
#print axioms ztg_g4_0_0_1_1_of_steps
#print axioms bank_0_0_1_1_of_steps

end Kepler.Text
