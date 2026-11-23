import Kepler.Text.TaylorSecond.Matan
import Kepler.Text.TaylorSecond.Coordinate
import Kepler.Text.Wt1TowerDomain

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Kepler.Text.TaylorSecond

open Kepler.Text
open Kepler.NliBanks21
open Filter
open scoped Topology

/-- The explicit three-variable wt1 expression on the `h0cut = 1` branch. -/
noncomputable def w1FexOpen3 (x : Fin 3 → ℝ) : ℝ :=
  1 / 12
    - (2 * mm1 / Real.pi) *
        (matan (w1tA (x 0) (x 1) (x 2)) / w1aA (x 0) (x 1) (x 2)
          + matan (w1tB (x 0) (x 1) (x 2)) / w1aB (x 0) (x 1) (x 2)
          + matan (w1tC (x 0) (x 1) (x 2)) / w1aC (x 0) (x 1) (x 2))
    + (8 * mm2 / Real.pi) *
        (lfun ((x 0) * 0.5) * (w1WC (x 0) (x 1) (x 2) * matan (w1gC (x 0) (x 1) (x 2)))
          + lfun ((x 1) * 0.5) * (w1WA (x 0) (x 1) (x 2) * matan (w1gA (x 0) (x 1) (x 2)))
          + lfun ((x 2) * 0.5) * (w1WB (x 0) (x 1) (x 2) * matan (w1gB (x 0) (x 1) (x 2))))
    - 0.008 * (w1WC (x 0) (x 1) (x 2) * matan (w1gC (x 0) (x 1) (x 2)))

/-- Full three-variable C² of the explicit `h0cut = 1` branch. -/
theorem contDiffAt_w1FexOpen3 (x : Fin 3 → ℝ)
    (hA0 : w1aA (x 0) (x 1) (x 2) ≠ 0) (hB0 : w1aB (x 0) (x 1) (x 2) ≠ 0)
    (hC0 : w1aC (x 0) (x 1) (x 2) ≠ 0)
    (hdA0 : w1d4A (x 0) (x 1) (x 2) ≠ 0) (hdB0 : w1d4B (x 0) (x 1) (x 2) ≠ 0)
    (hdC0 : w1d4C (x 0) (x 1) (x 2) ≠ 0)
    (htA : 0 < w1tA (x 0) (x 1) (x 2)) (htB : 0 < w1tB (x 0) (x 1) (x 2))
    (htC : 0 < w1tC (x 0) (x 1) (x 2)) (hgA : 0 < w1gA (x 0) (x 1) (x 2))
    (hgB : 0 < w1gB (x 0) (x 1) (x 2)) (hgC : 0 < w1gC (x 0) (x 1) (x 2)) :
    ContDiffAt ℝ 2 w1FexOpen3 x := by
  have htA2 : ContDiffAt ℝ 2 (fun z : Fin 3 → ℝ => w1tA (z 0) (z 1) (z 2)) x := by
    unfold w1aA at hA0
    have hA0sq : 4 * (w1aA (x 0) (x 1) (x 2)) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hA0)
    unfold w1tA w1tOf w1Dlt w1aA
    fun_prop (disch := assumption)
  have htB2 : ContDiffAt ℝ 2 (fun z : Fin 3 → ℝ => w1tB (z 0) (z 1) (z 2)) x := by
    unfold w1aB at hB0
    have hB0sq : 4 * (w1aB (x 0) (x 1) (x 2)) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hB0)
    unfold w1tB w1tOf w1Dlt w1aB
    fun_prop (disch := assumption)
  have htC2 : ContDiffAt ℝ 2 (fun z : Fin 3 → ℝ => w1tC (z 0) (z 1) (z 2)) x := by
    unfold w1aC at hC0
    have hC0sq : 4 * (w1aC (x 0) (x 1) (x 2)) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hC0)
    unfold w1tC w1tOf w1Dlt w1aC
    fun_prop (disch := assumption)
  have hgA2 : ContDiffAt ℝ 2 (fun z : Fin 3 → ℝ => w1gA (z 0) (z 1) (z 2)) x := by
    unfold w1d4A at hdA0
    have hdA0sq : (w1d4A (x 0) (x 1) (x 2)) ^ 2 ≠ 0 := pow_ne_zero 2 hdA0
    unfold w1gA w1gOf w1Dlt w1d4A
    fun_prop (disch := assumption)
  have hgB2 : ContDiffAt ℝ 2 (fun z : Fin 3 → ℝ => w1gB (z 0) (z 1) (z 2)) x := by
    unfold w1d4B at hdB0
    have hdB0sq : (w1d4B (x 0) (x 1) (x 2)) ^ 2 ≠ 0 := pow_ne_zero 2 hdB0
    unfold w1gB w1gOf w1Dlt w1d4B
    fun_prop (disch := assumption)
  have hgC2 : ContDiffAt ℝ 2 (fun z : Fin 3 → ℝ => w1gC (z 0) (z 1) (z 2)) x := by
    unfold w1d4C at hdC0
    have hdC0sq : (w1d4C (x 0) (x 1) (x 2)) ^ 2 ≠ 0 := pow_ne_zero 2 hdC0
    unfold w1gC w1gOf w1Dlt w1d4C
    fun_prop (disch := assumption)
  have hWA2 : ContDiffAt ℝ 2 (fun z : Fin 3 → ℝ => w1WA (z 0) (z 1) (z 2)) x := by
    unfold w1WA w1WOf w1d4A
    fun_prop (disch := assumption)
  have hWB2 : ContDiffAt ℝ 2 (fun z : Fin 3 → ℝ => w1WB (z 0) (z 1) (z 2)) x := by
    unfold w1WB w1WOf w1d4B
    fun_prop (disch := assumption)
  have hWC2 : ContDiffAt ℝ 2 (fun z : Fin 3 → ℝ => w1WC (z 0) (z 1) (z 2)) x := by
    unfold w1WC w1WOf w1d4C
    fun_prop (disch := assumption)
  have hmA := (contDiffAt_matan_of_pos htA).comp x htA2
  have hmB := (contDiffAt_matan_of_pos htB).comp x htB2
  have hmC := (contDiffAt_matan_of_pos htC).comp x htC2
  have hmgA := (contDiffAt_matan_of_pos hgA).comp x hgA2
  have hmgB := (contDiffAt_matan_of_pos hgB).comp x hgB2
  have hmgC := (contDiffAt_matan_of_pos hgC).comp x hgC2
  unfold w1FexOpen3 lfun w1aA w1aB w1aC
  fun_prop (disch := assumption)

/-- On the rational wt1 box and the `h0cut = 1` branch, the original `w1aF`
has exactly the explicit three-variable expression above. -/
theorem w1aF_eq_w1FexOpen3 (x : Fin 3 → ℝ)
    (hbox : (2.4635 : ℝ) ≤ x 0 ∧ x 0 ≤ 2.6508 ∧
      (2 : ℝ) ≤ x 1 ∧ x 1 ≤ 2.46352 ∧ (2 : ℝ) ≤ x 2 ∧ x 2 ≤ 2.46352)
    (hcut : x 0 ≤ 2 * h0) : w1aF (x 0) (x 1) (x 2) = w1FexOpen3 x := by
  have h4 : 0 ≤ x 0 := by linarith [hbox.1]
  have h5 : 0 < x 1 := by linarith [hbox.2.2.1]
  have h6 : 0 ≤ x 2 := by linarith [hbox.2.2.2.2.1]
  unfold w1aF
  rw [nb21_w1aG_explicit (x 0) (x 1) (x 2) h4 h5.le h6,
    nb21_w1aD_explicit]
  rw [w1_seA_unfold (x 0) (x 1) (x 2) h4 h5.le,
    w1_seB_unfold (x 0) (x 1) (x 2) h4 h5.le h6,
    w1_seC_unfold (x 0) (x 1) (x 2) h4 h5.le h6,
    w1_dihA_unfold (x 0) (x 1) (x 2) h5.le,
    w1_dihB_unfold (x 0) (x 1) (x 2) h6,
    w1_dihC_unfold (x 0) (x 1) (x 2) h4]
  unfold w1FexOpen3 h0cut
  rw [if_pos hcut]
  ring

/-- The original function read as a function of three coordinates. -/
noncomputable def w1F3 (x : Fin 3 → ℝ) : ℝ := w1aF (x 0) (x 1) (x 2)

/-- An open neighborhood on which all side conditions of the explicit wt1 C²
expression and the existing y5 derivative chain hold simultaneously. -/
structure Wt1C2Data (U : Set (Fin 3 → ℝ)) where
  isOpen : IsOpen U
  box : ∀ x ∈ U, (2.4635 : ℝ) ≤ x 0 ∧ x 0 ≤ 2.6508 ∧
    (2 : ℝ) ≤ x 1 ∧ x 1 ≤ 2.46352 ∧ (2 : ℝ) ≤ x 2 ∧ x 2 ≤ 2.46352
  cut : ∀ x ∈ U, x 0 ≤ 2 * h0
  area_ne : ∀ x ∈ U, w1aA (x 0) (x 1) (x 2) ≠ 0 ∧
    w1aB (x 0) (x 1) (x 2) ≠ 0 ∧ w1aC (x 0) (x 1) (x 2) ≠ 0
  d4_ne : ∀ x ∈ U, w1d4A (x 0) (x 1) (x 2) ≠ 0 ∧
    w1d4B (x 0) (x 1) (x 2) ≠ 0 ∧ w1d4C (x 0) (x 1) (x 2) ≠ 0
  t_pos : ∀ x ∈ U, 0 < w1tA (x 0) (x 1) (x 2) ∧
    0 < w1tB (x 0) (x 1) (x 2) ∧ 0 < w1tC (x 0) (x 1) (x 2)
  g_pos : ∀ x ∈ U, 0 < w1gA (x 0) (x 1) (x 2) ∧
    0 < w1gB (x 0) (x 1) (x 2) ∧ 0 < w1gC (x 0) (x 1) (x 2)

/-- Full three-variable C² of the original wt1 function on a certified open set. -/
theorem contDiffAt_w1F3_of_data {U : Set (Fin 3 → ℝ)} (data : Wt1C2Data U)
    (x : Fin 3 → ℝ) (hx : x ∈ U) : ContDiffAt ℝ 2 w1F3 x := by
  have ha := data.area_ne x hx
  have hd := data.d4_ne x hx
  have ht := data.t_pos x hx
  have hg := data.g_pos x hx
  have hOpen := contDiffAt_w1FexOpen3 x ha.1 ha.2.1 ha.2.2
    hd.1 hd.2.1 hd.2.2 ht.1 ht.2.1 ht.2.2 hg.1 hg.2.1 hg.2.2
  refine hOpen.congr_of_eventuallyEq ?_
  filter_upwards [data.isOpen.mem_nhds hx] with y hy
  exact w1aF_eq_w1FexOpen3 y (data.box y hy) (data.cut y hy)

/-- Identify the `(y5,y5)` entry of the genuine three-dimensional Hessian with
the existing `w1F2`, using both existing y5 derivative theorems. -/
theorem partial2_w1F3_eq_w1F2_of_data {U : Set (Fin 3 → ℝ)} (data : Wt1C2Data U)
    (x : Fin 3 → ℝ) (hx : x ∈ U) :
    partial2 1 1 w1F3 x = w1F2 (x 0) (x 1) (x 2) := by
  rw [partial2_eq_deriv_update (contDiffAt_w1F3_of_data data x hx) 1 1]
  have hpre : ∀ᶠ t in 𝓝 (x 1), Function.update x 1 t ∈ U := by
    have hmem : Function.update x 1 (x 1) ∈ U := by simpa using hx
    exact (hasDerivAt_update x 1 (x 1)).continuousAt (data.isOpen.mem_nhds hmem)
  have he : (fun t => partial1 1 w1F3 (Function.update x 1 t)) =ᶠ[𝓝 (x 1)]
      (fun t => w1F1 (x 0) t (x 2)) := by
    filter_upwards [hpre] with t ht
    have hC2 := contDiffAt_w1F3_of_data data (Function.update x 1 t) ht
    rw [partial1_eq_deriv_update (hC2.of_le (by norm_num)) 1]
    have hb := data.box (Function.update x 1 t) ht
    have hd := w1aF_hasDerivAt_y5_box (x 0) t (x 2)
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
    simpa [w1F3, Function.update_idem] using hd.deriv
  rw [he.deriv_eq]
  have hb := data.box x hx
  exact (w1aF_hasDerivAt2_y5_box (x 0) (x 1) (x 2)
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2).deriv

#print axioms contDiffAt_w1FexOpen3
#print axioms w1aF_eq_w1FexOpen3
#print axioms contDiffAt_w1F3_of_data
#print axioms partial2_w1F3_eq_w1F2_of_data

end Kepler.Text.TaylorSecond
