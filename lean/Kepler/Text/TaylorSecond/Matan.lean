import Kepler.Text.TaylorSecond.Bounds
import Kepler.Text.Wt1MatanDDAnti
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option maxHeartbeats 4000000

namespace Kepler.Text.TaylorSecond

open Filter
open scoped Topology ContDiff

/-- `matanD` is C¹ on the strictly positive branch. -/
theorem contDiffOn_matanD_pos : ContDiffOn ℝ 1 matanD (Set.Ioi 0) := by
  have hcont : ContinuousOn matanDD (Set.Ioi 0) := by
    intro t ht
    exact (matanDD_hasDerivAt_of_pos ht).continuousAt.continuousWithinAt
  have hderiv : ContDiffOn ℝ 0 (deriv matanD) (Set.Ioi 0) := by
    rw [contDiffOn_zero]
    exact hcont.congr (fun t ht => (matanD_hasDerivAt (by linarith [show (0 : ℝ) < t from ht])).deriv)
  rw [show (1 : ℕ∞ω) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, by norm_num, hderiv⟩
  intro t ht
  exact (matanD_hasDerivAt (by linarith [show (0 : ℝ) < t from ht])).differentiableAt.differentiableWithinAt

/-- `matan` is C² on the strictly positive branch. -/
theorem contDiffOn_matan_pos : ContDiffOn ℝ 2 matan (Set.Ioi 0) := by
  have hderiv : ContDiffOn ℝ 1 (deriv matan) (Set.Ioi 0) :=
    contDiffOn_matanD_pos.congr (fun t ht => (matan_hasDerivAt (by linarith [show (0 : ℝ) < t from ht])).deriv)
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, by norm_num, hderiv⟩
  intro t ht
  exact (matan_hasDerivAt (by linarith [show (0 : ℝ) < t from ht])).differentiableAt.differentiableWithinAt

theorem contDiffAt_matan_of_pos {t : ℝ} (ht : 0 < t) : ContDiffAt ℝ 2 matan t :=
  (contDiffOn_matan_pos t (Set.mem_Ioi.mpr ht)).contDiffAt (isOpen_Ioi.mem_nhds ht)

theorem deriv_matan_eq_matanD_of_pos {t : ℝ} (ht : 0 < t) : deriv matan t = matanD t :=
  (matan_hasDerivAt (by linarith)).deriv

theorem deriv_matanD_eq_matanDD_of_pos {t : ℝ} (ht : 0 < t) :
    deriv (deriv matan) t = matanDD t := by
  have he : deriv matan =ᶠ[𝓝 t] matanD := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact deriv_matan_eq_matanD_of_pos hy
  rw [he.deriv_eq]
  exact (matanD_hasDerivAt (by linarith)).deriv

/-- Positive-branch `matan` as a unary C² certificate.  The second derivative
uses the proved antitone endpoint envelope, not the original coarse upper bound. -/
noncomputable def matanUnaryBox (I V D DD : QInterval) (hI : 0 < I.lo)
    (hV : ∀ t, I.mem t → V.mem (matan t))
    (hD : ∀ t, I.mem t → D.mem (matanD t))
    (hDDlo : (DD.lo : ℝ) ≤ matanDD (I.hi : ℝ))
    (hDDhi : matanDD (I.lo : ℝ) ≤ (DD.hi : ℝ)) : UnaryBox matan I where
  firstFun := matanD
  secondFun := matanDD
  value := V
  first := D
  second := DD
  smooth := by
    intro t ht
    have hI' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hI
    exact contDiffAt_matan_of_pos (lt_of_lt_of_le hI' ht.1)
  first_eq := by
    intro t ht
    have hI' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hI
    exact deriv_matan_eq_matanD_of_pos (lt_of_lt_of_le hI' ht.1)
  second_eq := by
    intro t ht
    have hI' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hI
    exact deriv_matanD_eq_matanDD_of_pos (lt_of_lt_of_le hI' ht.1)
  value_mem := hV
  first_mem := hD
  second_mem := by
    intro t ht
    have hI' : (0 : ℝ) < (I.lo : ℝ) := by exact_mod_cast hI
    have hb := matanDD_mem_Icc_of_pos hI' ht.1 ht.2
    exact ⟨le_trans hDDlo hb.1, le_trans hb.2 hDDhi⟩

#print axioms contDiffOn_matanD_pos
#print axioms contDiffOn_matan_pos
#print axioms contDiffAt_matan_of_pos
#print axioms deriv_matan_eq_matanD_of_pos
#print axioms deriv_matanD_eq_matanDD_of_pos
#print axioms matanUnaryBox

end Kepler.Text.TaylorSecond
