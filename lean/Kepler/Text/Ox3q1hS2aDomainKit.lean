import Kepler.Text.ZTGJoint0000Box

open Set Filter Topology

namespace Kepler.Text

/-- Squared-coordinate wide-box membership from bounds on six positive lengths. -/
theorem ox3q1h_g4wBox_of_bounds {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1 : 2 ≤ y1) (h1' : y1 ≤ 2 * hplus)
    (h2 : 2 ≤ y2) (h2' : y2 ≤ 2 * hplus)
    (h3 : 2 ≤ y3) (h3' : y3 ≤ 2 * hplus)
    (h4 : 2 ≤ y4) (h4' : y4 ≤ 2 * hplus)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ 2 * hplus)
    (h6 : 2 ≤ y6) (h6' : y6 ≤ 2 * hplus) :
    g4wBox (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) := by
  rw [hplus] at *
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The common nondegeneracy premise for every Ox3q1h box and all its slot
permutations. -/
theorem ox3q1h_deltaY_pos_of_bounds {y1 y2 y3 y4 y5 y6 : ℝ}
    (h1 : 2 ≤ y1) (h1' : y1 ≤ 2 * hplus)
    (h2 : 2 ≤ y2) (h2' : y2 ≤ 2 * hplus)
    (h3 : 2 ≤ y3) (h3' : y3 ≤ 2 * hplus)
    (h4 : 2 ≤ y4) (h4' : y4 ≤ 2 * hplus)
    (h5 : 2 ≤ y5) (h5' : y5 ≤ 2 * hplus)
    (h6 : 2 ≤ y6) (h6' : y6 ≤ 2 * hplus) :
    0 < deltaY y1 y2 y3 y4 y5 y6 := by
  rw [deltaY]
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 96)
    (g4w_deltaX_bounds (ox3q1h_g4wBox_of_bounds h1 h1' h2 h2' h3 h3' h4 h4' h5 h5' h6 h6'))

/-- The vector-box form of `ox3q1h_deltaY_pos_of_bounds`. -/
theorem ox3q1h_deltaY_pos_of_box {blo bhi y : Fin 6 → ℝ}
    (hlo : ∀ j, 2 ≤ blo j) (hhi : ∀ j, bhi j ≤ 2 * hplus)
    (hy : ∀ j, y j ∈ Set.Icc (blo j) (bhi j)) :
    0 < deltaY (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) := by
  apply ox3q1h_deltaY_pos_of_bounds
  all_goals
    first
      | exact (hlo _).trans (hy _).1
      | exact (hy _).2.trans (hhi _)

/-- Updated points remain in the same coordinate box. -/
theorem ox3q1h_update_mem_box {blo bhi y : Fin 6 → ℝ} {i : Fin 6} {t : ℝ}
    (hy : ∀ j, y j ∈ Set.Icc (blo j) (bhi j))
    (ht : t ∈ Set.Icc (blo i) (bhi i)) :
    ∀ j, Function.update y i t j ∈ Set.Icc (blo j) (bhi j) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using ht
  · rw [Function.update_of_ne hji]
    exact hy j

/-- Nondegeneracy after replacing one coordinate by any point of its axis
interval. -/
theorem ox3q1h_deltaY_pos_update_of_box {blo bhi y : Fin 6 → ℝ} {i : Fin 6} {t : ℝ}
    (hlo : ∀ j, 2 ≤ blo j) (hhi : ∀ j, bhi j ≤ 2 * hplus)
    (hy : ∀ j, y j ∈ Set.Icc (blo j) (bhi j))
    (ht : t ∈ Set.Icc (blo i) (bhi i)) :
    0 < deltaY (Function.update y i t 0) (Function.update y i t 1)
      (Function.update y i t 2) (Function.update y i t 3)
      (Function.update y i t 4) (Function.update y i t 5) :=
  ox3q1h_deltaY_pos_of_box hlo hhi (ox3q1h_update_mem_box hy ht)

#print axioms ox3q1h_g4wBox_of_bounds
#print axioms ox3q1h_deltaY_pos_of_bounds
#print axioms ox3q1h_deltaY_pos_of_box
#print axioms ox3q1h_update_mem_box
#print axioms ox3q1h_deltaY_pos_update_of_box

end Kepler.Text
