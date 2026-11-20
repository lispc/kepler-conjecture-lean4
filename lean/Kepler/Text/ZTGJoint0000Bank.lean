import Kepler.Text.ZTGJoint0000CornersHM
import Kepler.Text.ZTGJoint0000CornersK
import Kepler.Text.ZTGJoint0000CornersP

set_option maxHeartbeats 8000000

namespace Kepler.Text

open Kepler.NliBanksZTGIJCF4Route

noncomputable def ztg0000Lo : Fin 6 → ℝ :=
  ![2 * hminus, 2, 2, 2, 2, 2]

noncomputable def ztg0000Hi : Fin 6 → ℝ :=
  ![2 * hplus, 2 * hminus, 2 * hminus, 2 * hminus, 2 * hminus, 2 * hminus]

noncomputable def ztg0000Cands : Fin 6 → Finset ℝ :=
  ![{2 * hminus, 2.52, 2 * hplus}, {2, 2 * hminus}, {2, 2 * hminus},
    {2, 2 * hminus}, {2, 2 * hminus}, {2, 2 * hminus}]

theorem ztgc0000_kink_pos : 0 < ztgMain 0 0 0 0 2.52 2 2 2 2 2 := by
  rw [show (2.52 : ℝ) = 2 * h0 by rw [show h0 = 1.26 from rfl]; norm_num]
  exact ztgc0000_2h0_pos

theorem ztg0000_cands_ne : ∀ i, (ztg0000Cands i).Nonempty := by
  intro i
  fin_cases i <;> simp [ztg0000Cands]

theorem ztg0000_cands_sub : ∀ i, ∀ c ∈ ztg0000Cands i,
    c ∈ Set.Icc (ztg0000Lo i) (ztg0000Hi i) := by
  intro i c hc
  fin_cases i
  · change c ∈ Set.Icc (2 * hminus) (2 * hplus)
    change c ∈ ({2 * hminus, 2.52, 2 * hplus} : Finset ℝ) at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact ⟨le_rfl, ztg_two_hminus_le_kink.trans ztg_kink_le_two_hplus⟩
    · exact ⟨ztg_two_hminus_le_kink, ztg_kink_le_two_hplus⟩
    · exact ⟨ztg_two_hminus_le_kink.trans ztg_kink_le_two_hplus, le_rfl⟩
  all_goals
    change c ∈ Set.Icc 2 (2 * hminus)
    change c ∈ ({2, 2 * hminus} : Finset ℝ) at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact ⟨le_rfl, Kepler.NliBanksZTGIJCF4Route.two_le_two_hminus⟩
    · exact ⟨Kepler.NliBanksZTGIJCF4Route.two_le_two_hminus, le_rfl⟩

theorem ztg_main_0000_pos_of_concave
    (h0l : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc (2 * hminus) 2.52)
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 0 t)))
    (h0r : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2.52 (2 * hplus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 0 t)))
    (h1 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 1 t)))
    (h2 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 2 t)))
    (h3 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 3 t)))
    (h4 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 4 t)))
    (h5 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 5 t))) :
    ∀ y1 y2 y3 y4 y5 y6, ztgBox 0 0 0 0 y1 y2 y3 y4 y5 y6 →
      0 < ztgMain 0 0 0 0 y1 y2 y3 y4 y5 y6 := by
  have hne : ∀ i, (ztg0000Cands i).Nonempty := ztg0000_cands_ne
  have hsub : ∀ i, ∀ c ∈ ztg0000Cands i,
      c ∈ Set.Icc (ztg0000Lo i) (ztg0000Hi i) := ztg0000_cands_sub
  have hstep : ∀ (i : Fin 6) (x : Fin 6 → ℝ),
      (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ∃ c ∈ ztg0000Cands i, ztg_main_fun 0 0 0 0 (Function.update x i c) ≤
        ztg_main_fun 0 0 0 0 x := by
    intro i x hx
    fin_cases i
    · simpa [ztg0000Cands] using
        ztg_step_of_concave_pair 0 0 0 0 0 x ztg_two_hminus_le_kink
          ztg_kink_le_two_hplus (hx 0) (h0l x hx) (h0r x hx)
    · simpa [ztg0000Cands] using ztg_step_of_concave 0 0 0 0 1 x
        (lo := 2) (hi := 2 * hminus) (by simpa [ztg0000Lo, ztg0000Hi] using hx 1) (h1 x hx)
    · simpa [ztg0000Cands] using ztg_step_of_concave 0 0 0 0 2 x
        (lo := 2) (hi := 2 * hminus) (by simpa [ztg0000Lo, ztg0000Hi] using hx 2) (h2 x hx)
    · simpa [ztg0000Cands] using ztg_step_of_concave 0 0 0 0 3 x
        (lo := 2) (hi := 2 * hminus) (by simpa [ztg0000Lo, ztg0000Hi] using hx 3) (h3 x hx)
    · simpa [ztg0000Cands] using ztg_step_of_concave 0 0 0 0 4 x
        (lo := 2) (hi := 2 * hminus) (by simpa [ztg0000Lo, ztg0000Hi] using hx 4) (h4 x hx)
    · simpa [ztg0000Cands] using ztg_step_of_concave 0 0 0 0 5 x
        (lo := 2) (hi := 2 * hminus) (by simpa [ztg0000Lo, ztg0000Hi] using hx 5) (h5 x hx)
  have hcorner : ∀ c0 ∈ ztg0000Cands 0, ∀ c1 ∈ ztg0000Cands 1,
      ∀ c2 ∈ ztg0000Cands 2, ∀ c3 ∈ ztg0000Cands 3,
      ∀ c4 ∈ ztg0000Cands 4, ∀ c5 ∈ ztg0000Cands 5,
      0 < ztgMain 0 0 0 0 c0 c1 c2 c3 c4 c5 := by
    intro c0 hc0 c1 hc1 c2 hc2 c3 hc3 c4 hc4 c5 hc5
    change c0 ∈ ({2 * hminus, 2.52, 2 * hplus} : Finset ℝ) at hc0
    change c1 ∈ ({2, 2 * hminus} : Finset ℝ) at hc1
    change c2 ∈ ({2, 2 * hminus} : Finset ℝ) at hc2
    change c3 ∈ ({2, 2 * hminus} : Finset ℝ) at hc3
    change c4 ∈ ({2, 2 * hminus} : Finset ℝ) at hc4
    change c5 ∈ ({2, 2 * hminus} : Finset ℝ) at hc5
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc0 hc1 hc2 hc3 hc4 hc5
    rcases hc0 with rfl | rfl | rfl
    · rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
        rcases hc3 with rfl | rfl <;> rcases hc4 with rfl | rfl <;>
        rcases hc5 with rfl | rfl
      all_goals
        first
      | exact ztgc0000_2hminus_pos
      | exact ztgcHM_c0
      | exact ztgcHM_c1
      | exact ztgcHM_c2
      | exact ztgcHM_c3
      | exact ztgcHM_c4
      | exact ztgcHM_c5
      | exact ztgcHM_c6
      | exact ztgcHM_c7
      | exact ztgcHM_c8
      | exact ztgcHM_c9
      | exact ztgcHM_c10
      | exact ztgcHM_c11
      | exact ztgcHM_c12
      | exact ztgcHM_c13
      | exact ztgcHM_c14
      | exact ztgcHM_c15
      | exact ztgcHM_c16
      | exact ztgcHM_c17
      | exact ztgcHM_c18
      | exact ztgcHM_c19
      | exact ztgcHM_c20
      | exact ztgcHM_c21
      | exact ztgcHM_c22
      | exact ztgcHM_c23
      | exact ztgcHM_c24
      | exact ztgcHM_c25
      | exact ztgcHM_c26
      | exact ztgcHM_c27
      | exact ztgcHM_c28
      | exact ztgcHM_c29
      | exact ztgcHM_c30
    · rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
        rcases hc3 with rfl | rfl <;> rcases hc4 with rfl | rfl <;>
        rcases hc5 with rfl | rfl
      all_goals
        first
      | exact ztgc0000_kink_pos
      | exact ztgcK_c0
      | exact ztgcK_c1
      | exact ztgcK_c2
      | exact ztgcK_c3
      | exact ztgcK_c4
      | exact ztgcK_c5
      | exact ztgcK_c6
      | exact ztgcK_c7
      | exact ztgcK_c8
      | exact ztgcK_c9
      | exact ztgcK_c10
      | exact ztgcK_c11
      | exact ztgcK_c12
      | exact ztgcK_c13
      | exact ztgcK_c14
      | exact ztgcK_c15
      | exact ztgcK_c16
      | exact ztgcK_c17
      | exact ztgcK_c18
      | exact ztgcK_c19
      | exact ztgcK_c20
      | exact ztgcK_c21
      | exact ztgcK_c22
      | exact ztgcK_c23
      | exact ztgcK_c24
      | exact ztgcK_c25
      | exact ztgcK_c26
      | exact ztgcK_c27
      | exact ztgcK_c28
      | exact ztgcK_c29
      | exact ztgcK_c30
    · rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
        rcases hc3 with rfl | rfl <;> rcases hc4 with rfl | rfl <;>
        rcases hc5 with rfl | rfl
      all_goals
        first
      | exact ztg_smoke_0000_2hplus_pos
      | exact ztgcP_c0
      | exact ztgcP_c1
      | exact ztgcP_c2
      | exact ztgcP_c3
      | exact ztgcP_c4
      | exact ztgcP_c5
      | exact ztgcP_c6
      | exact ztgcP_c7
      | exact ztgcP_c8
      | exact ztgcP_c9
      | exact ztgcP_c10
      | exact ztgcP_c11
      | exact ztgcP_c12
      | exact ztgcP_c13
      | exact ztgcP_c14
      | exact ztgcP_c15
      | exact ztgcP_c16
      | exact ztgcP_c17
      | exact ztgcP_c18
      | exact ztgcP_c19
      | exact ztgcP_c20
      | exact ztgcP_c21
      | exact ztgcP_c22
      | exact ztgcP_c23
      | exact ztgcP_c24
      | exact ztgcP_c25
      | exact ztgcP_c26
      | exact ztgcP_c27
      | exact ztgcP_c28
      | exact ztgcP_c29
      | exact ztgcP_c30
  intro y1 y2 y3 y4 y5 y6 hy
  rcases hy with ⟨h1l, h1h, h2l, h2h, h3l, h3h, h4l, h4h, h5l, h5h, h6l, h6h⟩
  have hx : ∀ j, (![y1, y2, y3, y4, y5, y6] : Fin 6 → ℝ) j ∈
      Set.Icc (ztg0000Lo j) (ztg0000Hi j) := by
    intro j
    fin_cases j <;>
      simp [ztg0000Lo, ztg0000Hi, bank_ZTGIJCF4lo, bank_ZTGIJCF4hi, Set.mem_Icc] <;>
      constructor <;> assumption
  have hpos := ztg_main_pos_of_slice_corners 0 0 0 0 ztg0000Lo ztg0000Hi
    ztg0000Cands hne hsub hstep hcorner ![y1, y2, y3, y4, y5, y6] hx
  simpa [ztg_main_fun] using hpos

theorem nliRestZTGIJCF4_0_0_0_0_of_concave
    (h0l : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc (2 * hminus) 2.52)
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 0 t)))
    (h0r : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2.52 (2 * hplus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 0 t)))
    (h1 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 1 t)))
    (h2 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 2 t)))
    (h3 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 3 t)))
    (h4 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 4 t)))
    (h5 : ∀ x : Fin 6 → ℝ, (∀ j, x j ∈ Set.Icc (ztg0000Lo j) (ztg0000Hi j)) →
      ConcaveOn ℝ (Set.Icc 2 (2 * hminus))
        (fun t => ztg_main_fun 0 0 0 0 (Function.update x 5 t))) :
    bank_ZTGIJCF4_0_0_0_0 :=
  ztg_of_main 0 0 0 0 (ztg_main_0000_pos_of_concave h0l h0r h1 h2 h3 h4 h5)

#print axioms ztg_main_0000_pos_of_concave
#print axioms nliRestZTGIJCF4_0_0_0_0_of_concave

end Kepler.Text
