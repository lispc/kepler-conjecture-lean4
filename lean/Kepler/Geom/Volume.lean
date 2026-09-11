/-
Kepler.Geom.Volume — 体积层基础设施（HOL Light Flyspeck `vol1.hl` / `flyspeck.ml` 的 Lean 移植）

本文件落地 `radial_norm`（vol1.hl:18）与 `sol`（vol1.hl:651，经
`new_specification` 由 `pre_def_4_3b_alt` 引入）两个定义，并证明 `sol` 的规格
`sol_spec`（vol1.hl:651）与径向体积标度引理 `lemma_r_r'`（vol1.hl:458）。

`sol x C` 是体积密度：对任意满足可测与径向条件（`radial_norm r x (C ∩ ball x r)`）
的半径 `r`，`sol x C = 3 * vol (C ∩ ball x r) / r³`。此处用 `Classical.choose`
选择见证半径（HOL 的 `@`/`new_specification` 对应），规格的良定义性由
`lemma_r_r'` 的标度不变性保证。

来源副本：`/dev/shm/kepler-ref/flyspeck/text_formalization/volume/vol1.hl`。
-/

import Mathlib
import Kepler.Geom.Aff
import Kepler.Geom.Azim

open MeasureTheory
open scoped Topology Pointwise

namespace Kepler.Geom

/-- HOL `radial_norm r x C`（vol1.hl:18）：`C` 含于以 `x` 为心、`r` 为半径的球，
且沿从 `x` 出发的射线在球内径向封闭。 -/
def radialNorm (r : ℝ) (x : V3) (C : Set V3) : Prop :=
  C ⊆ Metric.ball x r ∧
    ∀ u : V3, x + u ∈ C → ∀ t : ℝ, 0 < t → t * ‖u‖ < r → x + t • u ∈ C

/-- HOL `eventually_radial x C`（sphere.hl:452）：存在半径使 `C` 在该半径内径向。 -/
def EventuallyRadial (x : V3) (C : Set V3) : Prop :=
  ∃ r : ℝ, 0 < r ∧ radialNorm r x (C ∩ Metric.ball x r)

/-- HOL `sol x C`（vol1.hl:651）：体积密度，规格见 `sol_spec`。 -/
noncomputable def sol (x : V3) (C : Set V3) : ℝ := by
  classical
  exact if h : ∃ r : ℝ, 0 < r ∧ MeasurableSet (C ∩ Metric.ball x r) ∧
      radialNorm r x (C ∩ Metric.ball x r)
    then 3 * volume.real (C ∩ Metric.ball x (Classical.choose h)) /
      (Classical.choose h) ^ 3
    else 0

/-! ## 平移与标度下的实值测度 -/

theorem volume_real_add_left (x : V3) (S : Set V3) :
    volume.real ((fun y : V3 => x + y) '' S) = volume.real S := by
  have h : (fun y : V3 => x + y) '' S = (fun z : V3 => -x + z) ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨-x + z, hz, by simp⟩
  rw [h, Measure.real_def, Measure.real_def, measure_preimage_add]

theorem volume_real_add_right (x : V3) (S : Set V3) :
    volume.real ((fun y : V3 => y + x) '' S) = volume.real S := by
  have h : (fun y : V3 => y + x) '' S = (fun z : V3 => z + -x) ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨z + -x, hz, by simp⟩
  rw [h, Measure.real_def, Measure.real_def, measure_preimage_add_right]

theorem volume_real_smul (c : ℝ) (S : Set V3) :
    volume.real (c • S) = |c| ^ 3 * volume.real S := by
  rw [Measure.real_def, Measure.real_def, Measure.addHaar_smul volume c S,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hfr : Module.finrank ℝ V3 = 3 := by
    simp [V3, finrank_euclideanSpace]
  rw [hfr, abs_pow]

/-! ## 径向体积标度（vol1.hl:458 `lemma_r_r'`） -/

theorem radialNorm.volume_scaling {x : V3} {C : Set V3} {r s : ℝ}
    (hC : radialNorm r x C) (hs : 0 < s) (hsr : s < r) :
    volume.real (C ∩ Metric.ball x s) = volume.real C * (s / r) ^ 3 := by
  have hr : 0 < r := lt_trans hs hsr
  have hsrpos : 0 < s / r := div_pos hs hr
  have hCsub : C ⊆ Metric.ball x r := hC.1
  have hCball : C ∩ Metric.ball x r = C := Set.inter_eq_left.mpr hCsub
  have hdiv : (s / r) * r = s := by field_simp
  have hdiv' : (r / s) * s = r := by field_simp
  have himg : (fun y : V3 => x + (s / r) • (y - x)) '' (C ∩ Metric.ball x r) =
      C ∩ Metric.ball x s := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyC, hyball⟩, rfl⟩
      have hy_norm : ‖y - x‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hyball
      have hxu : x + (y - x) ∈ C := by simpa using hyC
      have ht_norm : (s / r) * ‖y - x‖ < r := by
        have h1 : (s / r) * ‖y - x‖ < (s / r) * r :=
          mul_lt_mul_of_pos_left hy_norm hsrpos
        rw [hdiv] at h1
        linarith
      have hmem : x + (s / r) • (y - x) ∈ C :=
        hC.2 (y - x) hxu (s / r) hsrpos ht_norm
      refine ⟨hmem, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have heq : x + (s / r) • (y - x) - x = (s / r) • (y - x) := by abel
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hsrpos]
      have h1 : (s / r) * ‖y - x‖ < (s / r) * r :=
        mul_lt_mul_of_pos_left hy_norm hsrpos
      rw [hdiv] at h1
      exact h1
    · intro hz
      have hzC : z ∈ C := hz.1
      have hz_norm : ‖z - x‖ < s := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz.2
      have hxu : x + (z - x) ∈ C := by simpa using hzC
      have htr : 0 < r / s := div_pos hr hs
      have ht_norm : (r / s) * ‖z - x‖ < r := by
        have h1 : (r / s) * ‖z - x‖ < (r / s) * s :=
          mul_lt_mul_of_pos_left hz_norm htr
        rw [hdiv'] at h1
        exact h1
      have hyC : x + (r / s) • (z - x) ∈ C :=
        hC.2 (z - x) hxu (r / s) htr ht_norm
      have hy_norm : ‖x + (r / s) • (z - x) - x‖ < r := by
        have heq : x + (r / s) • (z - x) - x = (r / s) • (z - x) := by abel
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos htr]
        have h1 : (r / s) * ‖z - x‖ < (r / s) * s :=
          mul_lt_mul_of_pos_left hz_norm htr
        rw [hdiv'] at h1
        exact h1
      refine ⟨x + (r / s) • (z - x), ⟨hyC, ?_⟩, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]; exact hy_norm
      · have h1 : (s / r) * (r / s) = 1 := by field_simp
        show x + (s / r) • ((x + (r / s) • (z - x)) - x) = z
        rw [show x + (r / s) • (z - x) - x = (r / s) • (z - x) by abel]
        rw [smul_smul, h1, one_smul]
        abel
  rw [← himg]
  have hcomp : (fun y : V3 => x + (s / r) • (y - x)) =
      (fun z : V3 => x + z) ∘ (fun w : V3 => (s / r) • w) ∘
        (fun y : V3 => y + -x) := by
    funext y; simp only [Function.comp_apply, sub_eq_add_neg]
  rw [hcomp, Set.image_comp, Set.image_comp, Set.image_smul,
    volume_real_add_left, volume_real_smul, volume_real_add_right, hCball,
    abs_of_pos hsrpos]
  ring

/-! ## `sol` 的规格（vol1.hl:651） -/

/-- 任意两个满足可测/径向条件的半径给出相同的体积密度。 -/
theorem sol_radius_independent {x : V3} {C : Set V3} {r₁ r₂ : ℝ}
    (h₁ : 0 < r₁) (h₁r : radialNorm r₁ x (C ∩ Metric.ball x r₁))
    (h₂ : 0 < r₂) (h₂r : radialNorm r₂ x (C ∩ Metric.ball x r₂)) :
    3 * volume.real (C ∩ Metric.ball x r₁) / r₁ ^ 3 =
      3 * volume.real (C ∩ Metric.ball x r₂) / r₂ ^ 3 := by
  wlog hle : r₁ ≤ r₂ generalizing r₁ r₂ with H
  · rw [not_le] at hle
    exact (H h₂ h₂r h₁ h₁r hle.le).symm
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq]
  have hsub : Metric.ball x r₁ ⊆ Metric.ball x r₂ := Metric.ball_subset_ball hle
  have hscale := radialNorm.volume_scaling h₂r h₁ hlt
  have hinter : C ∩ Metric.ball x r₁ = (C ∩ Metric.ball x r₂) ∩ Metric.ball x r₁ := by
    rw [Set.inter_assoc]
    congr 1
    exact (Set.inter_eq_right.mpr hsub).symm
  rw [hinter, hscale]
  have hr₂ : r₂ ≠ 0 := ne_of_gt h₂
  field_simp

/-- HOL `sol_spec`（vol1.hl:651）：`sol` 的体积密度规格。 -/
theorem sol_spec {x : V3} {C : Set V3} {r : ℝ}
    (hr : 0 < r) (hm : MeasurableSet (C ∩ Metric.ball x r))
    (hrad : radialNorm r x (C ∩ Metric.ball x r)) :
    sol x C = 3 * volume.real (C ∩ Metric.ball x r) / r ^ 3 := by
  have hex : ∃ r' : ℝ, 0 < r' ∧ MeasurableSet (C ∩ Metric.ball x r') ∧
      radialNorm r' x (C ∩ Metric.ball x r') := ⟨r, hr, hm, hrad⟩
  rw [sol, dif_pos hex]
  exact sol_radius_independent (Classical.choose_spec hex).1 (Classical.choose_spec hex).2.2
    hr hrad

end Kepler.Geom
