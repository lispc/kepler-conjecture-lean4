/-
Kepler.Text.Wt1TowerSymm — lane `cell3-wt1-tower-build-w1` (2026-11-20),
phase 1 of the wt1 second-order tower (route A′), piece 1 of 3:
the y5 <-> y6 symmetry of the wt1 kernel `w1aF`.

Mathematical content (SCOUT.md §2.3, mechanism confirmed on the build lane):
* `nb21_dih_swap35`: for the wt1 slot shape `(u1, 2, u3, 2, u5, 2)` the
  `dih` slot value is invariant under `u3 <-> u5`.  Both the radical
  factor `sqrt (4 u1)` and the two quotient ingredients are symmetric:
  `deltaX u1 2 u3 2 u5 2` is the symmetric three-coordinate Delta and
  `deltaX4 u1 2 u3 2 u5 2 = u1 * (u3 + u5 - u1)`;
* `nb21_solEuler_perm13`: for the same slot shape the `solEuler` slot
  value is invariant under `u1 <-> u3` (the `pi = (x1 x3)(x4 x6)`
  permutation of `solEuler_x`; the `delta` is symmetric and the Euler
  area `a` is symmetric because `x2 = x4 = x6 = 2`);
* the weighted sums, hence `w1aF` itself, are `y5 <-> y6` symmetric:
  `w1aF y4 y5 y6 = w1aF y4 y6 y5` for nonnegative coordinates.

This is the "M6 is free" input of the tower: y6-concavity follows from
y5-concavity of `w1aF` plus this symmetry.

No `axiom` / `sorry` / `admit` / `native_decide`; audited at the tail.
-/
import Kepler.NliBanks21

set_option maxHeartbeats 2000000

namespace Kepler.Text
open Kepler.NliBanks21

/-! ## 1. The `dih` slot is invariant under `u3 <-> u5` -/

/-- Slot-shape `dih` invariance: `dih(u1, 2, u3, 2, u5, 2)` does not see
the order of `u3` and `u5`. -/
theorem nb21_dih_swap35 (u1 u3 u5 : ℝ) :
    dihXDivSqrtdeltaPosbranch u1 2 u3 2 u5 2 =
      dihXDivSqrtdeltaPosbranch u1 2 u5 2 u3 2 := by
  have hd : deltaX u1 2 u3 2 u5 2 = deltaX u1 2 u5 2 u3 2 := by
    rw [deltaX, deltaX]
    ring
  have h4 : deltaX4 u1 2 u3 2 u5 2 = deltaX4 u1 2 u5 2 u3 2 := by
    rw [deltaX4, deltaX4]
    ring
  simp only [dihXDivSqrtdeltaPosbranch]
  simp only [hd, h4]

/-! ## 2. The `solEuler` slot is invariant under `u1 <-> u3` -/

/-- Slot-shape `solEuler` invariance: `solEuler(u1, 2, u3, 2, u5, 2)` does
not see the order of `u1` and `u3` (the third slot entry `u5` is fixed). -/
theorem nb21_solEuler_perm13 (u1 u3 u5 : ℝ) :
    solEulerXDivSqrtdelta u1 2 u3 2 u5 2 =
      solEulerXDivSqrtdelta u3 2 u1 2 u5 2 := by
  have hd : deltaX u1 2 u3 2 u5 2 = deltaX u3 2 u1 2 u5 2 := by
    rw [deltaX, deltaX]
    ring
  have ha : (Real.sqrt (u1 * 2 * u3) + Real.sqrt u1 * (2 + u3 - 2) / 2 +
      Real.sqrt 2 * (u1 + u3 - u5) / 2 + Real.sqrt u3 * (u1 + 2 - 2) / 2 : ℝ) =
      (Real.sqrt (u3 * 2 * u1) + Real.sqrt u3 * (2 + u1 - 2) / 2 +
      Real.sqrt 2 * (u3 + u1 - u5) / 2 + Real.sqrt u1 * (u3 + 2 - 2) / 2) := by
    rw [show u1 * 2 * u3 = u3 * 2 * u1 by ring]
    ring
  simp only [solEulerXDivSqrtdelta]
  rw [hd]
  simp only [ha]

/-! ## 3. Weighted slot sums and `w1aF` symmetry -/

/-- Euler-slot sum of `w1aG` is `y5 <-> y6` symmetric. -/
theorem nb21_se_sum_symm (y4 y5 y6 : ℝ) :
    solEulerXDivSqrtdelta (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
        solEulerXDivSqrtdelta (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 +
          solEulerXDivSqrtdelta (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 =
      solEulerXDivSqrtdelta (y6 * y6) 2 (y4 * y4) 2 (y5 * y5) 2 +
        solEulerXDivSqrtdelta (y5 * y5) 2 (y6 * y6) 2 (y4 * y4) 2 +
          solEulerXDivSqrtdelta (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 := by
  rw [nb21_solEuler_perm13 (y5 * y5) (y4 * y4) (y6 * y6),
      nb21_solEuler_perm13 (y6 * y6) (y5 * y5) (y4 * y4),
      nb21_solEuler_perm13 (y4 * y4) (y6 * y6) (y5 * y5)]
  ring

/-- Weighted `lfun`-dih sum of `w1aG` is `y5 <-> y6` symmetric. -/
theorem nb21_dih_sum_symm (y4 y5 y6 : ℝ) :
    lfun (y4 * 0.5) * h0cut y4 *
        dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 +
      lfun (y5 * 0.5) * 1 *
        dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y4 * y4) 2 (y6 * y6) 2 +
      lfun (y6 * 0.5) * 1 *
        dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y5 * y5) 2 (y4 * y4) 2 =
      lfun (y4 * 0.5) * h0cut y4 *
          dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 +
        lfun (y6 * 0.5) * 1 *
          dihXDivSqrtdeltaPosbranch (y6 * y6) 2 (y4 * y4) 2 (y5 * y5) 2 +
        lfun (y5 * 0.5) * 1 *
          dihXDivSqrtdeltaPosbranch (y5 * y5) 2 (y6 * y6) 2 (y4 * y4) 2 := by
  rw [nb21_dih_swap35 (y5 * y5) (y4 * y4) (y6 * y6),
      nb21_dih_swap35 (y6 * y6) (y5 * y5) (y4 * y4),
      nb21_dih_swap35 (y4 * y4) (y6 * y6) (y5 * y5)]
  ring

/-- The right kernel slot of `w1aD` is `y5 <-> y6` symmetric. -/
theorem nb21_w1aD_swap (y4 y5 y6 : ℝ) :
    dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y6 * y6) 2 (y5 * y5) 2 =
      dihXDivSqrtdeltaPosbranch (y4 * y4) 2 (y5 * y5) 2 (y6 * y6) 2 :=
  nb21_dih_swap35 (y4 * y4) (y6 * y6) (y5 * y5)

/-- **`w1aF` is `y5 <-> y6` symmetric** on nonnegative coordinates. -/
theorem nb21_w1aF_symm (y4 y5 y6 : ℝ) (h4 : 0 ≤ y4) (h5 : 0 ≤ y5) (h6 : 0 ≤ y6) :
    w1aF y4 y5 y6 = w1aF y4 y6 y5 := by
  unfold w1aF
  rw [nb21_w1aG_explicit y4 y5 y6 h4 h5 h6,
      nb21_w1aG_explicit y4 y6 y5 h4 h6 h5,
      nb21_w1aD_explicit y4 y5 y6,
      nb21_w1aD_explicit y4 y6 y5]
  rw [nb21_se_sum_symm, nb21_dih_sum_symm, nb21_w1aD_swap]

/-! ## 4. Axiom audit -/

#print axioms nb21_dih_swap35
#print axioms nb21_solEuler_perm13
#print axioms nb21_se_sum_symm
#print axioms nb21_dih_sum_symm
#print axioms nb21_w1aD_swap
#print axioms nb21_w1aF_symm

end Kepler.Text
