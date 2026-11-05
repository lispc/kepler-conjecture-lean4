/-
Kepler.Text.Gamma4ValArctan2 — lane `gamma4-val1e6`, V4 extension.

`arctan` bounds at the three algebraic arguments of the critical
`(2h0, 2,2,2,2,2)` corner (`2h0 = 2.52`, the `lmfun` fold plane) — the
corner where the thinnest B2 banks sit:
`-0.173504125…` (slot 1), `-0.530104749…` (slots 2,3,5,6),
`+0.058499843…` (slot 4).
Same engine as `Gamma4ValArctan` (order-32 alternating Taylor, `1e-11` tail,
8-decimal argument brackets, 10-decimal arctan brackets).
-/
import Kepler.Text.Gamma4ValArctan

set_option maxHeartbeats 4000000

namespace Kepler.Text

theorem g4v_atan_B1_bounds :
    (-0.171793879 : ℝ) ≤ Real.arctan
        ((-(4092039 / 390625)) /
          Real.sqrt (889979284656 / 244140625)) ∧
      Real.arctan ((-(4092039 / 390625)) /
          Real.sqrt (889979284656 / 244140625)) ≤ -0.171793868 := by
  have hp1 : (0.171793868 : ℝ) ≤ Real.arctan 0.17350413 ∧
      Real.arctan 0.17350413 ≤ 0.171793879 := by
    exact g4v_atan_pos_bounds (x := 0.17350413) (lo := 0.171793868)
      (hi := 0.171793879) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hp2 : (0.171793868 : ℝ) ≤ Real.arctan 0.17350412 ∧
      Real.arctan 0.17350412 ≤ 0.171793879 := by
    exact g4v_atan_pos_bounds (x := 0.17350412) (lo := 0.171793868)
      (hi := 0.171793879) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hn1 : (-0.171793879 : ℝ) ≤ Real.arctan (-0.17350413) := by
    rw [Real.arctan_neg]
    exact neg_le_neg_iff.mpr hp1.2
  have hn2 : Real.arctan (-0.17350412) ≤ -0.171793868 := by
    rw [Real.arctan_neg]
    exact neg_le_neg_iff.mpr hp2.1
  have hs1 : (60.3767765 : ℝ) ≤ Real.sqrt (889979284656 / 244140625) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : Real.sqrt (889979284656 / 244140625) ≤ 60.3767766 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have h := g4v_atan_ratio_neg_bounds
    (t := (-(4092039 / 390625)))
    (d := (889979284656 / 244140625))
    (dlo := 60.3767765) (dhi := 60.3767766)
    (ulo := -0.17350413) (uhi := -0.17350412)
    (lo := -0.171793879) (hi := -0.171793868)
    (by norm_num) hs1 hs2 (by norm_num) (by norm_num) (by norm_num) hn1 hn2
  exact h

theorem g4v_atan_B2_bounds :
    (-0.487440355 : ℝ) ≤ Real.arctan
        ((-(15876 / 625)) /
          Real.sqrt (896930496 / 390625)) ∧
      Real.arctan ((-(15876 / 625)) /
          Real.sqrt (896930496 / 390625)) ≤ -0.487440346 := by
  have hp1 : (0.487440346 : ℝ) ≤ Real.arctan 0.53010475 ∧
      Real.arctan 0.53010475 ≤ 0.487440355 := by
    exact g4v_atan_pos_bounds (x := 0.53010475) (lo := 0.487440346)
      (hi := 0.487440355) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hp2 : (0.487440346 : ℝ) ≤ Real.arctan 0.53010474 ∧
      Real.arctan 0.53010474 ≤ 0.487440355 := by
    exact g4v_atan_pos_bounds (x := 0.53010474) (lo := 0.487440346)
      (hi := 0.487440355) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hn1 : (-0.487440355 : ℝ) ≤ Real.arctan (-0.53010475) := by
    rw [Real.arctan_neg]
    exact neg_le_neg_iff.mpr hp1.2
  have hn2 : Real.arctan (-0.53010474) ≤ -0.487440346 := by
    rw [Real.arctan_neg]
    exact neg_le_neg_iff.mpr hp2.1
  have hs1 : (47.9180766 : ℝ) ≤ Real.sqrt (896930496 / 390625) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : Real.sqrt (896930496 / 390625) ≤ 47.9180767 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have h := g4v_atan_ratio_neg_bounds
    (t := (-(15876 / 625)))
    (d := (896930496 / 390625))
    (dlo := 47.9180766) (dhi := 47.9180767)
    (ulo := -0.53010475) (uhi := -0.53010474)
    (lo := -0.487440355) (hi := -0.487440346)
    (by norm_num) hs1 hs2 (by norm_num) (by norm_num) (by norm_num) hn1 hn2
  exact h

theorem g4v_atan_B3_bounds :
    (0.058433243 : ℝ) ≤ Real.arctan
        ((1752 / 625) /
          Real.sqrt (896930496 / 390625)) ∧
      Real.arctan ((1752 / 625) /
          Real.sqrt (896930496 / 390625)) ≤ 0.058433254 := by
  have hp1 : (0.058433243 : ℝ) ≤ Real.arctan 0.05849984 ∧
      Real.arctan 0.05849984 ≤ 0.058433254 := by
    exact g4v_atan_pos_bounds (x := 0.05849984) (lo := 0.058433243)
      (hi := 0.058433254) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hp2 : (0.058433243 : ℝ) ≤ Real.arctan 0.05849985 ∧
      Real.arctan 0.05849985 ≤ 0.058433254 := by
    exact g4v_atan_pos_bounds (x := 0.05849985) (lo := 0.058433243)
      (hi := 0.058433254) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have hs1 : (47.9180766 : ℝ) ≤ Real.sqrt (896930496 / 390625) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hs2 : Real.sqrt (896930496 / 390625) ≤ 47.9180767 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have h := g4v_atan_ratio_pos_bounds
    (t := (1752 / 625))
    (d := (896930496 / 390625))
    (dlo := 47.9180766) (dhi := 47.9180767)
    (ulo := 0.05849984) (uhi := 0.05849985)
    (lo := 0.058433243) (hi := 0.058433254)
    (by norm_num) hs1 hs2 (by norm_num) (by norm_num) (by norm_num) hp1.1 hp2.2
  exact h

#print axioms g4v_atan_B1_bounds
#print axioms g4v_atan_B2_bounds
#print axioms g4v_atan_B3_bounds

end Kepler.Text
