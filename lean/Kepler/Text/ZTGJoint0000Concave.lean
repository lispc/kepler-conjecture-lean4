import Kepler.Text.ZTGJoint0000Continuous
import Kepler.Text.ZTGJoint0000Bank
import Kepler.Text.Gamma4ConcaveBridge

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

theorem ztg0000_box_of_mem {y : Fin 6 → ℝ}
    (hy : ∀ j, y j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) :
    ztgBox 0 0 0 0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) := by
  have h0 := hy 0
  have h1 := hy 1
  have h2 := hy 2
  have h3 := hy 3
  have h4 := hy 4
  have h5 := hy 5
  simp [ztg0000Lo, ztg0000Hi, Set.mem_Icc] at h0 h1 h2 h3 h4 h5
  exact ⟨h0.1, h0.2, h1.1, h1.2,
    by simpa [bank_ZTGIJCF4lo] using h2.1, by simpa [bank_ZTGIJCF4hi] using h2.2,
    by simpa [bank_ZTGIJCF4lo] using h3.1, by simpa [bank_ZTGIJCF4hi] using h3.2,
    by simpa [bank_ZTGIJCF4lo] using h4.1, by simpa [bank_ZTGIJCF4hi] using h4.2,
    by simpa [bank_ZTGIJCF4lo] using h5.1, by simpa [bank_ZTGIJCF4hi] using h5.2⟩

theorem ztg0000_box_update {x : Fin 6 → ℝ}
    (hx : ∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) (i : Fin 6)
    {t : ℝ} (ht : t ∈ Set.Icc (ztg0000Lo i) (ztg0000Hi i)) :
    ztgBox 0 0 0 0 ((Function.update x i t) 0) ((Function.update x i t) 1)
      ((Function.update x i t) 2) ((Function.update x i t) 3)
      ((Function.update x i t) 4) ((Function.update x i t) 5) := by
  apply ztg0000_box_of_mem
  intro j
  by_cases hji : j = i
  · subst j
    simpa using ht
  · rw [Function.update_apply, if_neg hji]
    exact hx j

theorem ztg_concaveOn_of_hasDerivAt2_open {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hcont : ∀ t ∈ Set.Icc a b, ContinuousAt f t)
    (hf : ∀ t ∈ Set.Ioo a b, HasDerivAt f (f' t) t)
    (hf2 : ∀ t ∈ Set.Ioo a b, HasDerivAt f' (f'' t) t)
    (hneg : ∀ t ∈ Set.Ioo a b, f'' t ≤ 0) :
    ConcaveOn ℝ (Set.Icc a b) f := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (D := Set.Icc a b) (f := f)
    (f' := f') (f'' := f'') (convex_Icc a b) ?_ ?_ ?_ ?_
  · exact fun t ht => (hcont t ht).continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hf t ht).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hf2 t ht).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact hneg t ht

theorem ztg_concave_y1_left_of_nonpos
    (hsign : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y1 ∈ Set.Ioo (2 * hminus) 2.52 → ztgDMainSecond_y1 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc (2 * hminus) 2.52)
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 0 t)) := by
  intro x hx
  have hdirect : ConcaveOn ℝ (Set.Icc (2 * hminus) 2.52) (fun t => ztgMain 0 0 0 0 t (x 1) (x 2) (x 3) (x 4) (x 5)) := by
    apply ztg_concaveOn_of_hasDerivAt2_open
      (f' := fun t => ztgDMainFirst_y1 t (x 1) (x 2) (x 3) (x 4) (x 5) (-1 / (h0 - 1)))
      (f'' := fun t => ztgDMainSecond_y1 t (x 1) (x 2) (x 3) (x 4) (x 5) (-1 / (h0 - 1)))
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 0) (ztg0000Hi 0) := by
        change t ∈ Set.Icc (2 * hminus) (2 * hplus)
        exact ⟨ht.1, ht.2.trans ztg_kink_le_two_hplus⟩
      have hy := ztg0000_box_update hx 0 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      exact (ztg_main_continuousAt_y1 t (x 1) (x 2) (x 3) (x 4) (x 5)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd)
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 0) (ztg0000Hi 0) := by
        change t ∈ Set.Icc (2 * hminus) (2 * hplus)
        exact ⟨ht.1.le, ht.2.le.trans ztg_kink_le_two_hplus⟩
      have hy := ztg0000_box_update hx 0 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        linarith [ht.2]
      exact ztg_main_hasDerivAt_y1 t (x 1) (x 2) (x 3) (x 4) (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 0) (ztg0000Hi 0) := by
        change t ∈ Set.Icc (2 * hminus) (2 * hplus)
        exact ⟨ht.1.le, ht.2.le.trans ztg_kink_le_two_hplus⟩
      have hy := ztg0000_box_update hx 0 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        linarith [ht.2]
      exact ztg_main_hasDerivAt2_y1 t (x 1) (x 2) (x 3) (x 4) (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf hw
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 0) (ztg0000Hi 0) := by
        change t ∈ Set.Icc (2 * hminus) (2 * hplus)
        exact ⟨ht.1.le, ht.2.le.trans ztg_kink_le_two_hplus⟩
      have hy := ztg0000_box_update hx 0 htfull
      simp [Function.update] at hy
      exact hsign t (x 1) (x 2) (x 3) (x 4) (x 5) hy ht
  simpa [ztg_main_fun] using hdirect

theorem ztg_concave_y1_right_of_nonpos
    (hsign : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y1 ∈ Set.Ioo 2.52 (2 * hplus) → ztgDMainSecond_y1 y1 y2 y3 y4 y5 y6 0 ≤ 0) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2.52 (2 * hplus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 0 t)) := by
  intro x hx
  have hdirect : ConcaveOn ℝ (Set.Icc 2.52 (2 * hplus)) (fun t => ztgMain 0 0 0 0 t (x 1) (x 2) (x 3) (x 4) (x 5)) := by
    apply ztg_concaveOn_of_hasDerivAt2_open
      (f' := fun t => ztgDMainFirst_y1 t (x 1) (x 2) (x 3) (x 4) (x 5) 0)
      (f'' := fun t => ztgDMainSecond_y1 t (x 1) (x 2) (x 3) (x 4) (x 5) 0)
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 0) (ztg0000Hi 0) := by
        change t ∈ Set.Icc (2 * hminus) (2 * hplus)
        exact ⟨ztg_two_hminus_le_kink.trans ht.1, ht.2⟩
      have hy := ztg0000_box_update hx 0 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      exact (ztg_main_continuousAt_y1 t (x 1) (x 2) (x 3) (x 4) (x 5)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd)
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 0) (ztg0000Hi 0) := by
        change t ∈ Set.Icc (2 * hminus) (2 * hplus)
        exact ⟨ztg_two_hminus_le_kink.trans ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 0 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun 0 (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_gt
        rw [show h0 = 1.26 from rfl]
        linarith [ht.1]
      exact ztg_main_hasDerivAt_y1 t (x 1) (x 2) (x 3) (x 4) (x 5) 0
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 0) (ztg0000Hi 0) := by
        change t ∈ Set.Icc (2 * hminus) (2 * hplus)
        exact ⟨ztg_two_hminus_le_kink.trans ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 0 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun 0 (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_gt
        rw [show h0 = 1.26 from rfl]
        linarith [ht.1]
      exact ztg_main_hasDerivAt2_y1 t (x 1) (x 2) (x 3) (x 4) (x 5) 0
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf hw
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 0) (ztg0000Hi 0) := by
        change t ∈ Set.Icc (2 * hminus) (2 * hplus)
        exact ⟨ztg_two_hminus_le_kink.trans ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 0 htfull
      simp [Function.update] at hy
      exact hsign t (x 1) (x 2) (x 3) (x 4) (x 5) hy ht
  simpa [ztg_main_fun] using hdirect

theorem ztg_concave_y2_whole_of_nonpos
    (hsign : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y2 ∈ Set.Ioo 2 (2 * hminus) → ztgDMainSecond_y2 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 1 t)) := by
  intro x hx
  have hdirect : ConcaveOn ℝ (Set.Icc 2 (2 * hminus)) (fun t => ztgMain 0 0 0 0 (x 0) t (x 2) (x 3) (x 4) (x 5)) := by
    apply ztg_concaveOn_of_hasDerivAt2_open
      (f' := fun t => ztgDMainFirst_y2 (x 0) t (x 2) (x 3) (x 4) (x 5) (-1 / (h0 - 1)))
      (f'' := fun t => ztgDMainSecond_y2 (x 0) t (x 2) (x 3) (x 4) (x 5) (-1 / (h0 - 1)))
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 1) (ztg0000Hi 1) := by
        exact ht
      have hy := ztg0000_box_update hx 1 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      exact (ztg_main_continuousAt_y2 (x 0) t (x 2) (x 3) (x 4) (x 5)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd)
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 1) (ztg0000Hi 1) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 1 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt_y2 (x 0) t (x 2) (x 3) (x 4) (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 1) (ztg0000Hi 1) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 1 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt2_y2 (x 0) t (x 2) (x 3) (x 4) (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf hw
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 1) (ztg0000Hi 1) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 1 htfull
      simp [Function.update] at hy
      exact hsign (x 0) t (x 2) (x 3) (x 4) (x 5) hy ht
  simpa [ztg_main_fun] using hdirect

theorem ztg_concave_y3_whole_of_nonpos
    (hsign : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y3 ∈ Set.Ioo 2 (2 * hminus) → ztgDMainSecond_y3 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 2 t)) := by
  intro x hx
  have hdirect : ConcaveOn ℝ (Set.Icc 2 (2 * hminus)) (fun t => ztgMain 0 0 0 0 (x 0) (x 1) t (x 3) (x 4) (x 5)) := by
    apply ztg_concaveOn_of_hasDerivAt2_open
      (f' := fun t => ztgDMainFirst_y3 (x 0) (x 1) t (x 3) (x 4) (x 5) (-1 / (h0 - 1)))
      (f'' := fun t => ztgDMainSecond_y3 (x 0) (x 1) t (x 3) (x 4) (x 5) (-1 / (h0 - 1)))
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 2) (ztg0000Hi 2) := by
        exact ht
      have hy := ztg0000_box_update hx 2 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      exact (ztg_main_continuousAt_y3 (x 0) (x 1) t (x 3) (x 4) (x 5)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd)
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 2) (ztg0000Hi 2) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 2 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt_y3 (x 0) (x 1) t (x 3) (x 4) (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 2) (ztg0000Hi 2) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 2 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt2_y3 (x 0) (x 1) t (x 3) (x 4) (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf hw
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 2) (ztg0000Hi 2) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 2 htfull
      simp [Function.update] at hy
      exact hsign (x 0) (x 1) t (x 3) (x 4) (x 5) hy ht
  simpa [ztg_main_fun] using hdirect

theorem ztg_concave_y4_whole_of_nonpos
    (hsign : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y4 ∈ Set.Ioo 2 (2 * hminus) → ztgDMainSecond_y4 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 3 t)) := by
  intro x hx
  have hdirect : ConcaveOn ℝ (Set.Icc 2 (2 * hminus)) (fun t => ztgMain 0 0 0 0 (x 0) (x 1) (x 2) t (x 4) (x 5)) := by
    apply ztg_concaveOn_of_hasDerivAt2_open
      (f' := fun t => ztgDMainFirst_y4 (x 0) (x 1) (x 2) t (x 4) (x 5) (-1 / (h0 - 1)))
      (f'' := fun t => ztgDMainSecond_y4 (x 0) (x 1) (x 2) t (x 4) (x 5) (-1 / (h0 - 1)))
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 3) (ztg0000Hi 3) := by
        exact ht
      have hy := ztg0000_box_update hx 3 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      exact (ztg_main_continuousAt_y4 (x 0) (x 1) (x 2) t (x 4) (x 5)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd)
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 3) (ztg0000Hi 3) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 3 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt_y4 (x 0) (x 1) (x 2) t (x 4) (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 3) (ztg0000Hi 3) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 3 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt2_y4 (x 0) (x 1) (x 2) t (x 4) (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf hw
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 3) (ztg0000Hi 3) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 3 htfull
      simp [Function.update] at hy
      exact hsign (x 0) (x 1) (x 2) t (x 4) (x 5) hy ht
  simpa [ztg_main_fun] using hdirect

theorem ztg_concave_y5_whole_of_nonpos
    (hsign : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y5 ∈ Set.Ioo 2 (2 * hminus) → ztgDMainSecond_y5 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 4 t)) := by
  intro x hx
  have hdirect : ConcaveOn ℝ (Set.Icc 2 (2 * hminus)) (fun t => ztgMain 0 0 0 0 (x 0) (x 1) (x 2) (x 3) t (x 5)) := by
    apply ztg_concaveOn_of_hasDerivAt2_open
      (f' := fun t => ztgDMainFirst_y5 (x 0) (x 1) (x 2) (x 3) t (x 5) (-1 / (h0 - 1)))
      (f'' := fun t => ztgDMainSecond_y5 (x 0) (x 1) (x 2) (x 3) t (x 5) (-1 / (h0 - 1)))
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 4) (ztg0000Hi 4) := by
        exact ht
      have hy := ztg0000_box_update hx 4 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      exact (ztg_main_continuousAt_y5 (x 0) (x 1) (x 2) (x 3) t (x 5)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd)
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 4) (ztg0000Hi 4) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 4 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt_y5 (x 0) (x 1) (x 2) (x 3) t (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 4) (ztg0000Hi 4) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 4 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt2_y5 (x 0) (x 1) (x 2) (x 3) t (x 5) (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf hw
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 4) (ztg0000Hi 4) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 4 htfull
      simp [Function.update] at hy
      exact hsign (x 0) (x 1) (x 2) (x 3) t (x 5) hy ht
  simpa [ztg_main_fun] using hdirect

theorem ztg_concave_y6_whole_of_nonpos
    (hsign : ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      y6 ∈ Set.Ioo 2 (2 * hminus) → ztgDMainSecond_y6 y1 y2 y3 y4 y5 y6 (-1 / (h0 - 1)) ≤ 0) :
    ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 5 t)) := by
  intro x hx
  have hdirect : ConcaveOn ℝ (Set.Icc 2 (2 * hminus)) (fun t => ztgMain 0 0 0 0 (x 0) (x 1) (x 2) (x 3) (x 4) t) := by
    apply ztg_concaveOn_of_hasDerivAt2_open
      (f' := fun t => ztgDMainFirst_y6 (x 0) (x 1) (x 2) (x 3) (x 4) t (-1 / (h0 - 1)))
      (f'' := fun t => ztgDMainSecond_y6 (x 0) (x 1) (x 2) (x 3) (x 4) t (-1 / (h0 - 1)))
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 5) (ztg0000Hi 5) := by
        exact ht
      have hy := ztg0000_box_update hx 5 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      exact (ztg_main_continuousAt_y6 (x 0) (x 1) (x 2) (x 3) (x 4) t
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd)
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 5) (ztg0000Hi 5) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 5 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt_y6 (x 0) (x 1) (x 2) (x 3) (x 4) t (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 5) (ztg0000Hi 5) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 5 htfull
      have hw := ztg0000_wide hy
      have hd := ztg0000_deltaY_pos hy
      have hw0 := hw
      simp [Function.update] at hy hw hd hw0
      rcases hw0 with ⟨h1, h1', h2, h2', h3, h3', h4, h4', h5, h5', h6, h6'⟩
      have hf : HasDerivAt lmfun (-1 / (h0 - 1)) (t / 2) := by
        apply g4d_lmfun_hasDerivAt_of_lt
        rw [show h0 = 1.26 from rfl]
        have ht52 : t < 2.52 := lt_of_lt_of_le ht.2 ztg_two_hminus_le_kink
        linarith [ht.2]
      exact ztg_main_hasDerivAt2_y6 (x 0) (x 1) (x 2) (x 3) (x 4) t (-1 / (h0 - 1))
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hd hf hw
    · intro t ht
      have htfull : t ∈ Set.Icc (ztg0000Lo 5) (ztg0000Hi 5) := by
        exact ⟨ht.1.le, ht.2.le⟩
      have hy := ztg0000_box_update hx 5 htfull
      simp [Function.update] at hy
      exact hsign (x 0) (x 1) (x 2) (x 3) (x 4) t hy ht
  simpa [ztg_main_fun] using hdirect

#print axioms ztg_concaveOn_of_hasDerivAt2_open
#print axioms ztg_concave_y1_left_of_nonpos
#print axioms ztg_concave_y1_right_of_nonpos
#print axioms ztg_concave_y2_whole_of_nonpos
#print axioms ztg_concave_y3_whole_of_nonpos
#print axioms ztg_concave_y4_whole_of_nonpos
#print axioms ztg_concave_y5_whole_of_nonpos
#print axioms ztg_concave_y6_whole_of_nonpos

end Kepler.Text
