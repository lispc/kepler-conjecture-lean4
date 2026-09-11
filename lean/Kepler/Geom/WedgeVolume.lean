/-
Kepler.Geom.WedgeVolume — 球与楔形交体积（HOL Light Flyspeck `VOLUME_BALL_WEDGE`,
`Multivariate/flyspeck.ml:5452`）

目标：
`volume (Metric.ball z r ∩ wedge z w w1 w2) = ofReal (azim z w w1 w2 * 2 * r^3 / 3)`。

路线：
1. 平移不变性（`azim`、`wedge`、`volume`）。
2. 用 `w - z` 上的右手 ON 标架把三维问题化为 `ℝ × ℂ` 上的乘积测度问题；
   `f x = (x ⬝ᵥ e3, zOf e1 e2 x)` 是保测度的线性等距同构。
3. 在标架下 `azim 0 w w1 y` 等于平面投影的连续幅角差 `ang`，楔形变成
   半径 `√(r²-t²)`、角度 `θ` 的二维扇形。
4. 对轴向坐标 `t` 用 Fubini，扇形面积用 `sector_area_ang`，最后
   `∫_{-r}^{r} (r²-t²)/2 dt = 2r³/3`。
-/

import Mathlib
import Kepler.Geom.Azim
import Kepler.Geom.AzimLemmas
import Kepler.Geom.SectorArea
import Kepler.Geom.Volume

open MeasureTheory Complex
open scoped Real ENNReal

noncomputable section

namespace Kepler.Geom

/-! ## 平移不变性 -/

private theorem collinear3_zero_sub {x a b : V3} :
    Collinear3 x a b ↔ Collinear3 0 (a - x) (b - x) := by
  by_cases h : a = x
  · rw [h]
    simp only [sub_self]
    constructor <;> intro _ <;> exact collinear3_of_eq rfl
  · have h' : a - x ≠ 0 := sub_ne_zero.mpr h
    rw [collinear3_iff_smul h, collinear3_iff_smul h']
    simp only [sub_zero]

private theorem azimSpec_zero_sub {x a b c : V3} {θ : ℝ} :
    AzimSpec x a b c θ ↔ AzimSpec 0 (a - x) (b - x) (c - x) θ := by
  unfold AzimSpec
  simp only [sub_zero, sub_ne_zero]
  have hd : dist a x = dist (a - x) 0 := by rw [dist_eq_norm, dist_eq_norm, sub_zero]
  rw [hd]

private theorem azim_sub_self (x a b c : V3) :
    azim x a b c = azim 0 (a - x) (b - x) (c - x) := by
  unfold azim
  rw [collinear3_zero_sub (x := x) (a := a) (b := b),
    collinear3_zero_sub (x := x) (a := a) (b := c)]
  have hpred : AzimSpec x a b c = AzimSpec 0 (a - x) (b - x) (c - x) :=
    funext fun _ => propext azimSpec_zero_sub
  rw [hpred]

private theorem wedge_sub_self (x a b c : V3) :
    wedge x a b c = (fun y => x + y) '' wedge 0 (a - x) (b - x) (c - x) := by
  ext y
  rw [Set.mem_image]
  constructor
  · intro hy
    refine ⟨y - x, ?_, by abel⟩
    simp only [wedge, Set.mem_setOf_eq] at hy ⊢
    exact ⟨fun h => hy.1 ((collinear3_zero_sub (x := x) (a := a) (b := y)).mpr h),
      by rw [← azim_sub_self x a b y]; exact hy.2.1,
      by rw [← azim_sub_self x a b y, ← azim_sub_self x a b c]; exact hy.2.2⟩
  · rintro ⟨u, hu, rfl⟩
    simp only [wedge, Set.mem_setOf_eq] at hu ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [collinear3_zero_sub (x := x) (a := a) (b := x + u),
        show (x + u) - x = u by abel]
      exact hu.1
    · rw [azim_sub_self x a b (x + u), show (x + u) - x = u by abel]
      exact hu.2.1
    · rw [azim_sub_self x a b (x + u), show (x + u) - x = u by abel,
        azim_sub_self x a b c]
      exact hu.2.2

theorem volume_image_add_left (x : V3) (S : Set V3) :
    volume ((fun y : V3 => x + y) '' S) = volume S := by
  have h : (fun y : V3 => x + y) '' S = (fun z : V3 => -x + z) ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨-x + z, hz, by simp⟩
  rw [h]
  exact measure_preimage_add volume (-x) S

private theorem ball_sub_self (x : V3) (r : ℝ) :
    Metric.ball x r = (fun y => x + y) '' Metric.ball 0 r := by
  ext z
  constructor
  · intro hz
    refine ⟨z - x, ?_, by abel⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    rwa [show z - x - 0 = z - x by abel]
  · rintro ⟨y, hy, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    simpa using hy

/-- 平移归约：把顶点移到原点。 -/
theorem volume_ball_wedge_sub (z w w1 w2 : V3) (r : ℝ) :
    volume (Metric.ball z r ∩ wedge z w w1 w2) =
      volume (Metric.ball 0 r ∩ wedge 0 (w - z) (w1 - z) (w2 - z)) := by
  have hset : Metric.ball z r ∩ wedge z w w1 w2 =
      (fun y => z + y) '' (Metric.ball 0 r ∩ wedge 0 (w - z) (w1 - z) (w2 - z)) := by
    rw [ball_sub_self z r, wedge_sub_self z w w1 w2,
      Set.image_inter (f := fun y => z + y) (fun a b h => add_left_cancel h)]
  rw [hset, volume_image_add_left]

/-! ## 连续幅角 `ang`（把 `Complex.arg ∈ (-π, π]` 映到 `[0, 2π)`） -/

/-- `[0, 2π)` 幅角：`arg < 0` 时加 `2π`。 -/
def angArg (t : ℝ) : ℝ := if t < 0 then t + 2 * Real.pi else t

/-- 复数的连续幅角。 -/
def ang (z : ℂ) : ℝ := angArg z.arg

theorem measurable_angArg : Measurable angArg := by
  unfold angArg
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_id.add_const _) measurable_id

theorem measurable_ang : Measurable ang := measurable_angArg.comp Complex.measurable_arg

theorem angArg_nonneg {t : ℝ} (ht : -Real.pi < t) : 0 ≤ angArg t := by
  unfold angArg
  split
  · rename_i h; linarith [Real.pi_pos]
  · rename_i h; linarith

theorem angArg_lt_two_pi {t : ℝ} (ht : t ≤ Real.pi) : angArg t < 2 * Real.pi := by
  unfold angArg
  split
  · rename_i h; linarith
  · rename_i h; linarith [Real.pi_pos]

theorem ang_nonneg (z : ℂ) : 0 ≤ ang z := angArg_nonneg (Complex.neg_pi_lt_arg z)
theorem ang_lt_two_pi (z : ℂ) : ang z < 2 * Real.pi := angArg_lt_two_pi (Complex.arg_le_pi z)

theorem ang_eq_arg_of_nonneg {z : ℂ} (h : 0 ≤ z.arg) : ang z = z.arg := by
  simp [ang, angArg, not_lt.mpr h]

theorem ang_eq_arg_add_of_neg {z : ℂ} (h : z.arg < 0) : ang z = z.arg + 2 * Real.pi := by
  simp [ang, angArg, h]

theorem exp_ang (z : ℂ) :
    Complex.exp (ang z * I) = Complex.exp (z.arg * I) := by
  by_cases h : z.arg < 0
  · rw [ang_eq_arg_add_of_neg h]
    have h2pi : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
      simp
    rw [show ((z.arg + 2 * Real.pi : ℝ) : ℂ) * I
        = (z.arg : ℂ) * I + ((2 * Real.pi : ℝ) : ℂ) * I by
      rw [Complex.ofReal_add, add_mul]]
    rw [Complex.exp_add, h2pi, mul_one]
  · rw [ang_eq_arg_of_nonneg (not_lt.mp h)]

theorem ang_mul_exp (z : ℂ) :
    z = (‖z‖ : ℂ) * Complex.exp (ang z * I) := by
  rw [exp_ang]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

/-- 正实数倍不改变 `ang`。 -/
theorem ang_ofReal_mul_of_pos {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ang ((c : ℂ) * z) = ang z := by
  by_cases hz : z = 0
  · rw [hz, mul_zero]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hmem : ((c : ℂ)).arg + z.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hc.le, zero_add]
    exact Complex.arg_mem_Ioc z
  have harg : ((c : ℂ) * z).arg = z.arg := by
    rw [Complex.arg_mul hc0 hz hmem, Complex.arg_ofReal_of_nonneg hc.le, zero_add]
  rw [ang, ang, harg]

/-! ## 二维扇形面积（角度可达 `2π`） -/

/-- 参数幅角集合（开区间，避免 `polarCoord` 的负实轴割线）。 -/
def angSet (θ : ℝ) : Set ℝ :=
  {t : ℝ | -Real.pi < t ∧ t < Real.pi ∧ 0 < angArg t ∧ angArg t < θ}

theorem angSet_eq_Ioo {θ : ℝ} (hθ : θ ≤ Real.pi) : angSet θ = Set.Ioo 0 θ := by
  ext t
  rw [angSet, Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases ht : t < 0
    · exfalso
      simp only [angArg, ht, ↓reduceIte] at h4
      linarith [Real.pi_pos]
    · simp only [angArg, ht, ↓reduceIte] at h3 h4
      exact ⟨h3, h4⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith [Real.pi_pos]
    · linarith [h2, hθ]
    · simp only [angArg, not_lt.mpr h1.le, ↓reduceIte]; exact h1
    · simp only [angArg, not_lt.mpr h1.le, ↓reduceIte]; exact h2

theorem angSet_eq_union {θ : ℝ} (hπθ : Real.pi < θ) (hθ2π : θ < 2 * Real.pi) :
    angSet θ = Set.Ioo (-Real.pi) (θ - 2 * Real.pi) ∪ Set.Ioo 0 Real.pi := by
  ext t
  rw [angSet, Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases ht : t < 0
    · left
      simp only [angArg, ht, ↓reduceIte] at h3 h4
      exact ⟨h1, by linarith⟩
    · right
      simp only [angArg, ht, ↓reduceIte] at h3 h4
      exact ⟨h3, h2⟩
  · rintro (⟨h1, h4⟩ | ⟨h3, h2⟩)
    · have ht : t < 0 := by linarith
      refine ⟨h1, by linarith [Real.pi_pos], ?_, ?_⟩
      · simp only [angArg, ht, ↓reduceIte]; linarith [Real.pi_pos]
      · simp only [angArg, ht, ↓reduceIte]; linarith
    · have ht : ¬ t < 0 := not_lt.mpr h3.le
      refine ⟨by linarith, h2, ?_, ?_⟩
      · simp only [angArg, ht, ↓reduceIte]; exact h3
      · simp only [angArg, ht, ↓reduceIte]; linarith

theorem measurableSet_angSet {θ : ℝ} (hθ2π : θ < 2 * Real.pi) :
    MeasurableSet (angSet θ) := by
  by_cases hθ : θ ≤ Real.pi
  · rw [angSet_eq_Ioo hθ]; exact measurableSet_Ioo
  · rw [angSet_eq_union (not_le.mp hθ) hθ2π]
    exact measurableSet_Ioo.union measurableSet_Ioo

theorem volume_angSet {θ : ℝ} (hθ2π : θ < 2 * Real.pi) :
    volume (angSet θ) = ENNReal.ofReal θ := by
  by_cases hθ : θ ≤ Real.pi
  · rw [angSet_eq_Ioo hθ, Real.volume_Ioo, sub_zero]
  · have hπθ : Real.pi < θ := not_le.mp hθ
    rw [angSet_eq_union hπθ hθ2π,
      measure_union (by
        rw [Set.disjoint_left]
        intro t ht1 ht2
        rw [Set.mem_Ioo] at ht1
        rw [Set.mem_Ioo] at ht2
        linarith) measurableSet_Ioo,
      Real.volume_Ioo, Real.volume_Ioo]
    rw [← ENNReal.ofReal_add]
    · congr 1; ring
    · linarith [Real.pi_pos]
    · linarith

/-- `ang (e^{iθ}) = θ` 对 `θ ∈ [0, 2π)`。 -/
theorem ang_exp_mul_I {θ : ℝ} (h0 : 0 ≤ θ) (h2π : θ < 2 * Real.pi) :
    ang (Complex.exp (θ * I)) = θ := by
  apply angle_eq_of_exp_eq (ang_nonneg _) (ang_lt_two_pi _) h0 h2π
  have hne : Complex.exp (θ * I) ≠ 0 := Complex.exp_ne_zero _
  have h1 := ang_mul_exp (Complex.exp (θ * I))
  rw [Complex.norm_exp, show (θ * I).re = 0 from by simp [Complex.mul_re],
    Real.exp_zero, Complex.ofReal_one, one_mul] at h1
  exact h1.symm

/-- 半径 `ρ`、角度 `θ ∈ [0, 2π)` 的开扇形面积。 -/
theorem sector_area_ang {ρ θ : ℝ} (hρ : 0 ≤ ρ) (_hθ0 : 0 ≤ θ) (hθ2π : θ < 2 * Real.pi) :
    volume {z : ℂ | ‖z‖ < ρ ∧ 0 < ang z ∧ ang z < θ} =
      ENNReal.ofReal (ρ ^ 2 * θ / 2) := by
  set S : Set ℂ := {z : ℂ | ‖z‖ < ρ ∧ 0 < ang z ∧ ang z < θ} with hS
  set A : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) ρ ×ˢ angSet θ with hA
  have hS_meas : MeasurableSet S := by
    rw [hS]
    exact (measurableSet_lt measurable_norm measurable_const).inter
      ((measurableSet_lt measurable_const measurable_ang).inter
        (measurableSet_lt measurable_ang measurable_const))
  have hA_meas : MeasurableSet A := by
    rw [hA]
    exact measurableSet_Ioo.prod (measurableSet_angSet hθ2π)
  have hA_sub_T : A ⊆ Complex.polarCoord.target := by
    intro p hp
    rw [hA] at hp
    rw [Complex.polarCoord_target]
    exact ⟨hp.1.1, hp.2.1, hp.2.2.1⟩
  have h_polar : volume S =
      ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • S.indicator 1 (Complex.polarCoord.symm p) := by
    rw [← lintegral_indicator_one hS_meas]
    exact (Complex.lintegral_comp_polarCoord_symm (S.indicator 1)).symm
  have h_point : ∀ p ∈ Complex.polarCoord.target,
      ENNReal.ofReal p.1 • S.indicator 1 (Complex.polarCoord.symm p)
        = A.indicator (fun p : ℝ × ℝ => ENNReal.ofReal p.1) p := by
    intro p hp
    rw [Complex.polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    have harg : (Complex.polarCoord.symm p).arg = p.2 := by
      rw [Complex.polarCoord_symm_apply]
      rw [show (↑p.1 * (↑(Real.cos p.2) + ↑(Real.sin p.2) * Complex.I))
          = (↑p.1 * (Complex.cos ↑p.2 + Complex.sin ↑p.2 * Complex.I)) by
        rw [Complex.ofReal_cos, Complex.ofReal_sin]]
      exact Complex.arg_mul_cos_add_sin_mul_I hp1 ⟨hp.2.1, hp.2.2.le⟩
    have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    have hmem : Complex.polarCoord.symm p ∈ S ↔ p ∈ A := by
      rw [hS, hA]
      simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioo, angSet]
      rw [hnorm, show ang (Complex.polarCoord.symm p) = angArg p.2 from by
        rw [ang, harg]]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨hp1, h1⟩, hp.2.1, hp.2.2, h2, h3⟩
      · rintro ⟨⟨_, h1⟩, _, _, h2, h3⟩
        exact ⟨h1, h2, h3⟩
    by_cases hpA : p ∈ A
    · rw [Set.indicator_of_mem hpA, Set.indicator_of_mem (hmem.mpr hpA)]
      simp
    · rw [Set.indicator_of_notMem hpA,
        Set.indicator_of_notMem (fun h => hpA (hmem.mp h))]
      simp
  have hT_to_A : ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • S.indicator 1 (Complex.polarCoord.symm p) =
      ∫⁻ p in A, ENNReal.ofReal p.1 := by
    rw [setLIntegral_congr_fun Complex.polarCoord.open_target.measurableSet h_point]
    rw [setLIntegral_indicator hA_meas]
    rw [show A ∩ Complex.polarCoord.target = A from Set.inter_eq_left.mpr hA_sub_T]
  rw [h_polar, hT_to_A, hA]
  have hprod := setLIntegral_prod (μ := volume) (ν := volume)
    (s := Set.Ioo (0 : ℝ) ρ) (t := angSet θ)
    (fun p : ℝ × ℝ => ENNReal.ofReal p.1)
    (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable
  change (∫⁻ (p : ℝ × ℝ) in Set.Ioo (0 : ℝ) ρ ×ˢ angSet θ,
      ENNReal.ofReal p.1 ∂(volume.prod volume)) = ENNReal.ofReal (ρ ^ 2 * θ / 2)
  rw [hprod]
  have hinner : ∀ x : ℝ,
      ∫⁻ y in angSet θ, ENNReal.ofReal x = ENNReal.ofReal x * ENNReal.ofReal θ := by
    intro x
    rw [setLIntegral_const, volume_angSet hθ2π]
  simp_rw [hinner]
  rw [lintegral_mul_const _ ENNReal.measurable_ofReal]
  rw [lintegral_Ioo_zero_ofReal_id hρ]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ρ ^ 2 / 2)]
  congr 1
  ring

/-! ## 标架等距同构 `V3 ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℂ)` -/

private theorem zOf_norm_sq (e1 e2 : V3) (x : V3) :
    ‖zOf e1 e2 x‖ ^ 2 = (x ⬝ᵥ e1) ^ 2 + (x ⬝ᵥ e2) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [zOf, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    add_zero, zero_add, mul_one, sub_self]
  ring

private theorem zOf_self_left (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) :
    zOf e1 e2 e1 = 1 := by
  unfold zOf; rw [he.1, he.2.2.2.1]; simp

private theorem zOf_self_right (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) :
    zOf e1 e2 e2 = Complex.I := by
  unfold zOf
  rw [show e2 ⬝ᵥ e1 = 0 from by rw [dotProduct_comm]; exact he.2.2.2.1, he.2.1]
  simp

private theorem zOf_axis_zero (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) :
    zOf e1 e2 e3 = 0 := by
  unfold zOf
  rw [show e3 ⬝ᵥ e1 = 0 from by rw [dotProduct_comm]; exact he.2.2.2.2.1,
    show e3 ⬝ᵥ e2 = 0 from by rw [dotProduct_comm]; exact he.2.2.2.2.2.1]
  simp

private theorem on3_norm_sq (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) (x : V3) :
    ‖x‖ ^ 2 = (x ⬝ᵥ e1) ^ 2 + (x ⬝ᵥ e2) ^ 2 + (x ⬝ᵥ e3) ^ 2 := by
  have h12 : e1 ⬝ᵥ e2 = 0 := he.2.2.2.1
  have h21 : e2 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact he.2.2.2.1
  have h13 : e1 ⬝ᵥ e3 = 0 := he.2.2.2.2.1
  have h31 : e3 ⬝ᵥ e1 = 0 := by rw [dotProduct_comm]; exact he.2.2.2.2.1
  have h23 : e2 ⬝ᵥ e3 = 0 := he.2.2.2.2.2.1
  have h32 : e3 ⬝ᵥ e2 = 0 := by rw [dotProduct_comm]; exact he.2.2.2.2.2.1
  rw [norm_sq_eq_dot, on3_expand he x]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [he.1, he.2.1, he.2.2.1, h12, h21, h13, h31, h23, h32]
  ring

/-- 右手 ON 标架给出的线性等距同构 `x ↦ (x ⬝ᵥ e3, zOf e1 e2 x)`。 -/
noncomputable def frameIsometry (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) :
    V3 ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℂ) where
  toLinearEquiv := LinearEquiv.ofBijective
    { toFun := fun (x : V3) => WithLp.toLp 2 (x ⬝ᵥ e3, zOf e1 e2 x)
      map_add' := by
        intro x y
        have hp : ((x + y) ⬝ᵥ e3, zOf e1 e2 (x + y))
            = (x ⬝ᵥ e3, zOf e1 e2 x) + (y ⬝ᵥ e3, zOf e1 e2 y) := by
          ext <;> simp [add_dotProduct, zOf_add]
        show WithLp.toLp 2 ((x + y) ⬝ᵥ e3, zOf e1 e2 (x + y)) =
          WithLp.toLp 2 (x ⬝ᵥ e3, zOf e1 e2 x) + WithLp.toLp 2 (y ⬝ᵥ e3, zOf e1 e2 y)
        rw [hp, WithLp.toLp_add]
      map_smul' := by
        intro c x
        have hp : ((c • x) ⬝ᵥ e3, zOf e1 e2 (c • x))
            = c • (x ⬝ᵥ e3, zOf e1 e2 x) := by
          ext <;> simp [smul_dotProduct, zOf_smul]
        show WithLp.toLp 2 ((c • x) ⬝ᵥ e3, zOf e1 e2 (c • x))
            = c • WithLp.toLp 2 (x ⬝ᵥ e3, zOf e1 e2 x)
        rw [hp, WithLp.toLp_smul] }
    (by
      constructor
      · intro x y hxy
        have h := congrArg WithLp.ofLp hxy
        have h1 : x ⬝ᵥ e3 = y ⬝ᵥ e3 := congrArg Prod.fst h
        have h2 : zOf e1 e2 x = zOf e1 e2 y := congrArg Prod.snd h
        have hx1 : x ⬝ᵥ e1 = y ⬝ᵥ e1 := by
          have := congrArg Complex.re h2; simpa [zOf] using this
        have hx2 : x ⬝ᵥ e2 = y ⬝ᵥ e2 := by
          have := congrArg Complex.im h2; simpa [zOf] using this
        rw [on3_expand he x, on3_expand he y, h1, hx1, hx2]
      · intro z
        refine ⟨z.snd.re • e1 + z.snd.im • e2 + z.fst • e3, ?_⟩
        rw [WithLp.ext_iff]
        have hfst : ((z.snd.re • e1 + z.snd.im • e2 + z.fst • e3 : V3) ⬝ᵥ e3) = z.fst := by
          simp [add_dotProduct, smul_dotProduct, he.2.2.1, he.2.2.2.2.1,
            he.2.2.2.2.2.1]
        have hsnd : zOf e1 e2 (z.snd.re • e1 + z.snd.im • e2 + z.fst • e3 : V3) = z.snd := by
          simp only [zOf_add, zOf_smul, zOf_self_left e1 e2 e3 he,
            zOf_self_right e1 e2 e3 he, zOf_axis_zero e1 e2 e3 he, mul_one, mul_zero,
            add_zero]
          exact Complex.re_add_im z.snd
        show WithLp.ofLp (WithLp.toLp 2
          (((z.snd.re • e1 + z.snd.im • e2 + z.fst • e3 : V3)) ⬝ᵥ e3,
            zOf e1 e2 (z.snd.re • e1 + z.snd.im • e2 + z.fst • e3 : V3))) = WithLp.ofLp z
        rw [WithLp.ofLp_toLp, hfst, hsnd]
        rfl)
  norm_map' := by
    intro x
    change ‖(WithLp.toLp 2 (x ⬝ᵥ e3, zOf e1 e2 x) : WithLp 2 (ℝ × ℂ))‖ = ‖x‖
    have h : ‖(WithLp.toLp 2 (x ⬝ᵥ e3, zOf e1 e2 x) : WithLp 2 (ℝ × ℂ))‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      rw [show (WithLp.toLp 2 (x ⬝ᵥ e3, zOf e1 e2 x) : WithLp 2 (ℝ × ℂ)).fst
            = x ⬝ᵥ e3 from rfl,
          show (WithLp.toLp 2 (x ⬝ᵥ e3, zOf e1 e2 x) : WithLp 2 (ℝ × ℂ)).snd
            = zOf e1 e2 x from rfl]
      rw [zOf_norm_sq, Real.norm_eq_abs, sq_abs, on3_norm_sq e1 e2 e3 he x]
      ring
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ h with h' | h'
    · exact h'
    · have h1 := norm_nonneg (WithLp.toLp 2 (x ⬝ᵥ e3, zOf e1 e2 x) : WithLp 2 (ℝ × ℂ))
      have h2 := norm_nonneg x
      linarith

/-- 投影 `x ↦ (x ⬝ᵥ e3, zOf e1 e2 x)` 保测度（到 `ℝ × ℂ` 的乘积测度）。 -/
theorem measurePreserving_proj (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) :
    MeasurePreserving (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) volume
      (volume.prod volume) := by
  have h1 : MeasurePreserving (frameIsometry e1 e2 e3 he) volume volume :=
    LinearIsometryEquiv.measurePreserving _
  have h2 : MeasurePreserving (WithLp.ofLp : WithLp 2 (ℝ × ℂ) → ℝ × ℂ) volume volume :=
    WithLp.volume_preserving_ofLp ℝ ℂ
  have h3 : MeasurePreserving ((WithLp.ofLp : WithLp 2 (ℝ × ℂ) → ℝ × ℂ) ∘
      (frameIsometry e1 e2 e3 he)) volume volume := h2.comp h1
  have h4 : (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) =
      ((WithLp.ofLp : WithLp 2 (ℝ × ℂ) → ℝ × ℂ) ∘ (frameIsometry e1 e2 e3 he)) := rfl
  rw [h4]
  have hv : (volume : Measure (ℝ × ℂ)) = volume.prod volume := Measure.volume_eq_prod ℝ ℂ
  rw [← hv]
  exact h3

/-! ## 单位复数旋转 -/

/-- 单位复数乘法 `z ↦ u * z` 作为实线性等距同构。 -/
noncomputable def cplxRot (u : ℂ) (hu : ‖u‖ = 1) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv := LinearEquiv.ofBijective
    { toFun := fun z => u * z
      map_add' := fun z w => by ring
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, Complex.real_smul]
        ring }
    (by
      have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
      constructor
      · intro z w h
        change u * z = u * w at h
        exact mul_left_cancel₀ hu0 h
      · intro z
        exact ⟨u⁻¹ * z, by
          change u * (u⁻¹ * z) = z
          rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]⟩)
  norm_map' := fun z => by
    change ‖u * z‖ = ‖z‖
    rw [Complex.norm_mul, hu, one_mul]

/-- 线性等距同构保持 `volume` 的像测度。 -/
private theorem volume_image_cplx (f : ℂ ≃ₗᵢ[ℝ] ℂ) (S : Set ℂ) (hS : MeasurableSet S) :
    volume (f '' S) = volume S := by
  have h : f '' S = (f.symm : ℂ → ℂ) ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hz; exact ⟨f.symm z, hz, f.apply_symm_apply z⟩
  rw [h]
  exact (LinearIsometryEquiv.measurePreserving f.symm).measure_preimage hS.nullMeasurableSet

/-- 绕原点旋转 `a⁻¹` 后的扇形面积。 -/
theorem volume_sector_rot {a : ℂ} (ha : a ≠ 0) {R θ : ℝ}
    (hR : 0 ≤ R) (hθ0 : 0 ≤ θ) (hθ2π : θ < 2 * Real.pi) :
    volume {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (a⁻¹ * ζ) ∧ ang (a⁻¹ * ζ) < θ} =
      ENNReal.ofReal (R ^ 2 * θ / 2) := by
  have hnorm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set u : ℂ := a / (‖a‖ : ℂ) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg a)]
    exact div_self (norm_ne_zero_iff.mpr ha)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have ha_eq : a = (‖a‖ : ℂ) * u := by
    have hne : (‖a‖ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]
      exact norm_ne_zero_iff.mpr ha
    rw [hu_def, div_eq_mul_inv, mul_comm a ((‖a‖ : ℂ))⁻¹, ← mul_assoc,
      mul_inv_cancel₀ hne, one_mul]
  have hkey : ∀ w : ℂ, a⁻¹ * w = ((‖a‖⁻¹ : ℝ) : ℂ) * (u⁻¹ * w) := by
    have ha' : a⁻¹ = u⁻¹ * ((‖a‖⁻¹ : ℝ) : ℂ) := by
      conv_lhs => rw [ha_eq]
      rw [mul_inv_rev, ← Complex.ofReal_inv]
    intro w
    rw [ha']
    ring
  have hkeypos : (0 : ℝ) < (‖a‖ : ℝ)⁻¹ := inv_pos.mpr hnorm_pos
  have hset : {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang (a⁻¹ * ζ) ∧ ang (a⁻¹ * ζ) < θ}
      = (cplxRot u hu) '' {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang ζ ∧ ang ζ < θ} := by
    ext ζ
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hζ
      refine ⟨u⁻¹ * ζ, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [Complex.norm_mul, norm_inv, hu, inv_one, one_mul]; exact hζ.1
      · have h := hζ.2.1
        rw [hkey ζ, ang_ofReal_mul_of_pos hkeypos] at h
        exact h
      · have h := hζ.2.2
        rw [hkey ζ, ang_ofReal_mul_of_pos hkeypos] at h
        exact h
      · show u * (u⁻¹ * ζ) = ζ
        rw [← mul_assoc, mul_inv_cancel₀ hu0, one_mul]
    · rintro ⟨ζ', ⟨h1, h2, h3⟩, rfl⟩
      have hmem : u⁻¹ * (u * ζ') = ζ' := by
        rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
      refine ⟨?_, ?_, ?_⟩
      · change ‖u * ζ'‖ < R
        rw [Complex.norm_mul, hu, one_mul]; exact h1
      · change 0 < ang (a⁻¹ * (u * ζ'))
        rw [hkey (u * ζ'), hmem, ang_ofReal_mul_of_pos hkeypos]; exact h2
      · change ang (a⁻¹ * (u * ζ')) < θ
        rw [hkey (u * ζ'), hmem, ang_ofReal_mul_of_pos hkeypos]; exact h3
  have hS : MeasurableSet {ζ : ℂ | ‖ζ‖ < R ∧ 0 < ang ζ ∧ ang ζ < θ} :=
    (measurableSet_lt measurable_norm measurable_const).inter
      ((measurableSet_lt measurable_const measurable_ang).inter
        (measurableSet_lt measurable_ang measurable_const))
  rw [hset, volume_image_cplx (cplxRot u hu) _ hS]
  exact sector_area_ang hR hθ0 hθ2π

/-! ## `azim` 与平面幅角 `ang` 的桥接 -/

/-- 在轴向标架下，`azim 0 w w1 y` 等于平面投影 `zOf` 的连续幅角差。 -/
theorem azim_eq_ang_of_frame {w w1 y : V3} (e1 e2 e3 : V3)
    (he : Orthonormal3 e1 e2 e3) (hax : (w : V3) = dist w 0 • e3) (hw : w ≠ 0)
    (h1 : ¬ Collinear3 0 w w1) (hy : ¬ Collinear3 0 w y) :
    azim 0 w w1 y = ang ((zOf e1 e2 w1)⁻¹ * zOf e1 e2 y) := by
  have hax' : (w - 0 : V3) = dist w 0 • e3 := by rw [sub_zero]; exact hax
  obtain ⟨ψ, r1, ry, hr1, hry, hz1, hzy⟩ := azim_frame_spec h1 hy he hax' hw
  simp only [sub_zero] at hz1 hzy
  have hdiv : (zOf e1 e2 w1)⁻¹ * zOf e1 e2 y
      = ((ry / r1 : ℝ) : ℂ) * Complex.exp (azim 0 w w1 y * I) := by
    rw [← div_eq_inv_mul, hz1, hzy, exp_add_I]
    field_simp [hr1.ne', Complex.exp_ne_zero]
    rw [Complex.ofReal_div]
    field_simp [hr1.ne']
  rw [hdiv, ang_ofReal_mul_of_pos (div_pos hry hr1),
    ang_exp_mul_I (azim_nonneg _ _ _ _) (azim_lt_two_pi _ _ _ _)]

/-! ## 投影下的球∩楔形 -/

private theorem dot_e3_rep (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) (t : ℝ) (ζ : ℂ) :
    ((t • e3 + ζ.re • e1 + ζ.im • e2 : V3) ⬝ᵥ e3) = t := by
  simp [add_dotProduct, smul_dotProduct, he.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.1]

private theorem zOf_rep (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) (t : ℝ) (ζ : ℂ) :
    zOf e1 e2 (t • e3 + ζ.re • e1 + ζ.im • e2 : V3) = ζ := by
  simp only [zOf_add, zOf_smul, zOf_self_left e1 e2 e3 he, zOf_self_right e1 e2 e3 he,
    zOf_axis_zero e1 e2 e3 he, mul_one, mul_zero]
  simp only [zero_add]
  exact Complex.re_add_im ζ

/-- 投影 `x ↦ (x ⬝ᵥ e3, zOf e1 e2 x)` 是双射（显式右逆）。 -/
theorem proj_rep (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3) (p : ℝ × ℂ) :
    (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x))
      (p.1 • e3 + p.2.re • e1 + p.2.im • e2) = p := by
  ext
  · exact dot_e3_rep e1 e2 e3 he p.1 p.2
  · exact zOf_rep e1 e2 e3 he p.1 p.2

/-- 球∩楔形在投影下的特征（用 `ang` 表述）。 -/
theorem proj_mem_iff {w w1 w2 : V3} (e1 e2 e3 : V3) (he : Orthonormal3 e1 e2 e3)
    (hax : (w : V3) = dist w 0 • e3) (hw : w ≠ 0) (h1 : ¬ Collinear3 0 w w1)
    {r : ℝ} (hr : 0 ≤ r) (x : V3) :
    (x ∈ Metric.ball 0 r ∧ x ∈ wedge 0 w w1 w2) ↔
      ((x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 < r ^ 2 ∧ zOf e1 e2 x ≠ 0 ∧
        0 < ang ((zOf e1 e2 w1)⁻¹ * zOf e1 e2 x) ∧
        ang ((zOf e1 e2 w1)⁻¹ * zOf e1 e2 x) < azim 0 w w1 w2) := by
  have hax' : (w - 0 : V3) = dist w 0 • e3 := by rw [sub_zero]; exact hax
  rw [Metric.mem_ball, dist_zero_right, wedge, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hball, hcol, ha, hb⟩
    have hnorm : ‖x‖ ^ 2 = (x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 := by
      rw [on3_norm_sq e1 e2 e3 he x, zOf_norm_sq]; ring
    refine ⟨?_, by simpa using (zOf_ne_zero_iff he hax' hw x).mpr hcol, ?_, ?_⟩
    · rw [← hnorm]
      exact (sq_lt_sq₀ (norm_nonneg x) hr).mpr hball
    · rw [azim_eq_ang_of_frame e1 e2 e3 he hax hw h1 hcol] at ha; exact ha
    · rw [azim_eq_ang_of_frame e1 e2 e3 he hax hw h1 hcol] at hb; exact hb
  · rintro ⟨hball, hz, ha, hb⟩
    have hnorm : ‖x‖ ^ 2 = (x ⬝ᵥ e3) ^ 2 + ‖zOf e1 e2 x‖ ^ 2 := by
      rw [on3_norm_sq e1 e2 e3 he x, zOf_norm_sq]; ring
    have hcol : ¬ Collinear3 0 w x := (zOf_ne_zero_iff he hax' hw x).mp (by simpa using hz)
    refine ⟨?_, hcol, ?_, ?_⟩
    · rw [← hnorm] at hball
      exact (sq_lt_sq₀ (norm_nonneg x) hr).mp hball
    · rw [azim_eq_ang_of_frame e1 e2 e3 he hax hw h1 hcol]; exact ha
    · rw [azim_eq_ang_of_frame e1 e2 e3 he hax hw h1 hcol]; exact hb

/-- 投影下的球∩楔形集合。 -/
theorem image_proj_ball_wedge {w w1 w2 : V3} (e1 e2 e3 : V3)
    (he : Orthonormal3 e1 e2 e3) (hax : (w : V3) = dist w 0 • e3) (hw : w ≠ 0)
    (h1 : ¬ Collinear3 0 w w1) {r : ℝ} (hr : 0 ≤ r) :
    (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) '' (Metric.ball 0 r ∩ wedge 0 w w1 w2)
      = {p : ℝ × ℂ | p.1 ^ 2 + ‖p.2‖ ^ 2 < r ^ 2 ∧ p.2 ≠ 0 ∧
          0 < ang ((zOf e1 e2 w1)⁻¹ * p.2) ∧
          ang ((zOf e1 e2 w1)⁻¹ * p.2) < azim 0 w w1 w2} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (proj_mem_iff e1 e2 e3 he hax hw h1 hr x).mp hx
  · intro hp
    refine ⟨p.1 • e3 + p.2.re • e1 + p.2.im • e2, ?_, ?_⟩
    · refine (proj_mem_iff e1 e2 e3 he hax hw h1 hr _).mpr ?_
      rw [dot_e3_rep e1 e2 e3 he p.1 p.2, zOf_rep e1 e2 e3 he p.1 p.2]
      exact hp
    · exact proj_rep e1 e2 e3 he p

/-! ## 积分计算 -/

private theorem norm_lt_sqrt_iff (R : ℝ) (ζ : ℂ) :
    ‖ζ‖ < Real.sqrt R ↔ ‖ζ‖ ^ 2 < R := by
  rcases le_total 0 R with hR | hR
  · rw [Real.lt_sqrt (norm_nonneg ζ), sq]
  · have h0 : Real.sqrt R = 0 := Real.sqrt_eq_zero_of_nonpos hR
    rw [h0]
    constructor
    · intro h; exact absurd h (not_lt.mpr (norm_nonneg ζ))
    · intro h; exact absurd h (not_lt.mpr (by linarith [hR, sq_nonneg ‖ζ‖]))

/-- `∫⁻ t, ofReal ((r²-t²)θ/2) = ofReal (2r³θ/3)`（积分只在 `(-r,r)` 上非零）。 -/
theorem lintegral_parabola {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 ≤ θ) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((r ^ 2 - t ^ 2) * θ / 2) =
      ENNReal.ofReal (2 * r ^ 3 * θ / 3) := by
  set s : Set ℝ := Set.Ioo (-r) r with hs
  have hsupp : ∀ t, t ∉ s → ENNReal.ofReal ((r ^ 2 - t ^ 2) * θ / 2) = 0 := by
    intro t ht
    rw [hs, Set.mem_Ioo, not_and_or, not_lt, not_lt] at ht
    rw [ENNReal.ofReal_eq_zero]
    have key : ∀ t : ℝ, t ≤ -r → r ^ 2 ≤ t ^ 2 := by
      intro t ht
      have h1 : r ≤ -t := by linarith
      have h2 : r * r ≤ (-t) * (-t) := mul_self_le_mul_self hr h1
      nlinarith
    rcases ht with ht | ht
    · have := key t ht; nlinarith [hθ, this]
    · have h1 : r ≤ t := ht
      have h2 : r * r ≤ t * t := mul_self_le_mul_self hr h1
      nlinarith [hθ, h2]
  have h1 : ∫⁻ t : ℝ, ENNReal.ofReal ((r ^ 2 - t ^ 2) * θ / 2)
      = ∫⁻ t in s, ENNReal.ofReal ((r ^ 2 - t ^ 2) * θ / 2) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext t
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, hsupp t ht]
  rw [h1]
  have h_int : IntegrableOn (fun t : ℝ => (r ^ 2 - t ^ 2) * θ / 2) s := by
    rw [hs]
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : -r ≤ r)).mp
      (Continuous.intervalIntegrable (by fun_prop) (-r) r)
  have h_nn : 0 ≤ᵐ[volume.restrict s] (fun t : ℝ => (r ^ 2 - t ^ 2) * θ / 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [hs, Set.mem_Ioo] at ht
    have ht2 : t ^ 2 < r ^ 2 := by
      rw [sq_lt_sq, abs_of_nonneg hr]
      exact abs_lt.mpr ⟨ht.1, ht.2⟩
    have hpos : 0 < r ^ 2 - t ^ 2 := by linarith
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal h_int h_nn]
  have hint : ∫ t in s, (r ^ 2 - t ^ 2) * θ / 2 = 2 * r ^ 3 * θ / 3 := by
    rw [hs, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    have h : ∀ t : ℝ, (r ^ 2 - t ^ 2) * θ / 2 = (r ^ 2 * θ / 2) - (θ / 2) * t ^ 2 := by
      intro t; ring
    simp_rw [h]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_pow]
      ring
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hint]

/-! ## 主定理 -/

/-- `z = 0` 情形。 -/
theorem volume_ball_wedge_zero {w w1 w2 : V3} {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball 0 r ∩ wedge 0 w w1 w2) =
      ENNReal.ofReal (azim 0 w w1 w2 * 2 * r ^ 3 / 3) := by
  by_cases hdeg : Collinear3 0 w w1 ∨ Collinear3 0 w w2
  · have hz : azim 0 w w1 w2 = 0 := by
      unfold azim; rw [if_pos hdeg]
    have hwedge : wedge 0 w w1 w2 = ∅ := by
      rw [wedge]
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, -, hlt⟩
      rw [hz] at hlt
      exact absurd hlt (not_lt.mpr (azim_nonneg 0 w w1 y))
    rw [hwedge, Set.inter_empty, measure_empty, hz]
    simp
  · obtain ⟨hw1, hw2⟩ := not_or.mp hdeg
    have hw : w ≠ 0 := fun h => hw1 (by rw [h]; exact collinear3_of_eq rfl)
    obtain ⟨e1, e2, e3, he, halign⟩ := exists_on3_eq_smul w hw
    have hax : (w : V3) = dist w 0 • e3 := by
      rw [dist_eq_norm, sub_zero]; exact halign
    have hax' : (w - 0 : V3) = dist w 0 • e3 := by rw [sub_zero]; exact hax
    set a : ℂ := zOf e1 e2 w1 with ha_def
    have ha : a ≠ 0 := by
      rw [ha_def]
      simpa using (zOf_ne_zero_iff he hax' hw w1).mpr hw1
    set θ : ℝ := azim 0 w w1 w2 with hθ_def
    have hθ0 : 0 ≤ θ := azim_nonneg 0 w w1 w2
    have hθ2π : θ < 2 * Real.pi := azim_lt_two_pi 0 w w1 w2
    set T : Set (ℝ × ℂ) :=
      {p : ℝ × ℂ | p.1 ^ 2 + ‖p.2‖ ^ 2 < r ^ 2 ∧ p.2 ≠ 0 ∧
        0 < ang (a⁻¹ * p.2) ∧ ang (a⁻¹ * p.2) < θ} with hT_def
    have himg : (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) ''
        (Metric.ball 0 r ∩ wedge 0 w w1 w2) = T := by
      rw [hT_def, ha_def, hθ_def]
      exact image_proj_ball_wedge e1 e2 e3 he hax hw hw1 hr
    have hT_meas : MeasurableSet T := by
      rw [hT_def]
      have h1 : MeasurableSet {p : ℝ × ℂ | p.1 ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
        measurableSet_lt ((measurable_fst.pow_const 2).add
          (measurable_snd.norm.pow_const 2)) measurable_const
      have h2 : MeasurableSet {p : ℝ × ℂ | p.2 ≠ 0} :=
        (measurableSet_singleton (0 : ℂ)).compl.preimage measurable_snd
      have h3 : MeasurableSet {p : ℝ × ℂ | 0 < ang (a⁻¹ * p.2)} :=
        measurableSet_lt measurable_const
          (measurable_ang.comp (measurable_const.mul measurable_snd))
      have h4 : MeasurableSet {p : ℝ × ℂ | ang (a⁻¹ * p.2) < θ} :=
        measurableSet_lt (measurable_ang.comp (measurable_const.mul measurable_snd))
          measurable_const
      rw [show {p : ℝ × ℂ | p.1 ^ 2 + ‖p.2‖ ^ 2 < r ^ 2 ∧ p.2 ≠ 0 ∧
            0 < ang (a⁻¹ * p.2) ∧ ang (a⁻¹ * p.2) < θ}
          = {p | p.1 ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} ∩ {p | p.2 ≠ 0} ∩
            {p | 0 < ang (a⁻¹ * p.2)} ∩ {p | ang (a⁻¹ * p.2) < θ} by
        ext p; simp [and_assoc]]
      exact ((h1.inter h2).inter h3).inter h4
    have hproj := measurePreserving_proj e1 e2 e3 he
    have hvol : volume (Metric.ball 0 r ∩ wedge 0 w w1 w2) =
        (volume.prod volume) T := by
      have hinj : Function.Injective (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) := by
        intro x y h
        have h1 : x ⬝ᵥ e3 = y ⬝ᵥ e3 := congrArg Prod.fst h
        have h2 : zOf e1 e2 x = zOf e1 e2 y := congrArg Prod.snd h
        have hx1 : x ⬝ᵥ e1 = y ⬝ᵥ e1 := by
          have := congrArg Complex.re h2; simpa [zOf] using this
        have hx2 : x ⬝ᵥ e2 = y ⬝ᵥ e2 := by
          have := congrArg Complex.im h2; simpa [zOf] using this
        rw [on3_expand he x, on3_expand he y, h1, hx1, hx2]
      have hpre : Metric.ball 0 r ∩ wedge 0 w w1 w2 =
          (fun x : V3 => (x ⬝ᵥ e3, zOf e1 e2 x)) ⁻¹' T := by
        rw [← himg]
        ext x
        constructor
        · intro hx; exact ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, hyx⟩; rwa [hinj hyx] at hy
      rw [hpre]
      exact hproj.measure_preimage hT_meas.nullMeasurableSet
    rw [hvol, Measure.prod_apply hT_meas]
    have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' T) =
        ENNReal.ofReal ((r ^ 2 - t ^ 2) * θ / 2) := by
      intro t
      have hset : Prod.mk t ⁻¹' T =
          {ζ : ℂ | ‖ζ‖ < Real.sqrt (r ^ 2 - t ^ 2) ∧ 0 < ang (a⁻¹ * ζ) ∧
            ang (a⁻¹ * ζ) < θ} := by
        rw [hT_def]
        ext ζ
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          exact ⟨(norm_lt_sqrt_iff _ ζ).mpr (by linarith), h3, h4⟩
        · rintro ⟨h1, h3, h4⟩
          refine ⟨?_, ?_, h3, h4⟩
          · rw [norm_lt_sqrt_iff] at h1; linarith
          · intro hz
            rw [hz, mul_zero] at h3
            simp [ang, angArg] at h3
      rw [hset]
      rcases le_total (t ^ 2) (r ^ 2) with ht | ht
      · have hR : 0 ≤ Real.sqrt (r ^ 2 - t ^ 2) := Real.sqrt_nonneg _
        rw [volume_sector_rot ha hR hθ0 hθ2π]
        congr 1
        rw [Real.sq_sqrt (by linarith)]
      · have hsqrt0 : Real.sqrt (r ^ 2 - t ^ 2) = 0 :=
          Real.sqrt_eq_zero_of_nonpos (by linarith)
        rw [hsqrt0]
        have hempty : {ζ : ℂ | ‖ζ‖ < (0 : ℝ) ∧ 0 < ang (a⁻¹ * ζ) ∧
            ang (a⁻¹ * ζ) < θ} = ∅ := by
          ext ζ; simp [not_lt.mpr (norm_nonneg ζ)]
        rw [hempty, measure_empty]
        exact (ENNReal.ofReal_eq_zero.mpr (by nlinarith [hθ0])).symm
    simp_rw [hslice]
    rw [lintegral_parabola hr hθ0]
    congr 1
    ring

/-- HOL Light Flyspeck `VOLUME_BALL_WEDGE`（`Multivariate/flyspeck.ml:5452`）。 -/
theorem volume_ball_wedge {z w w1 w2 : V3} {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball z r ∩ wedge z w w1 w2)
      = ENNReal.ofReal (azim z w w1 w2 * 2 * r ^ 3 / 3) := by
  rw [volume_ball_wedge_sub z w w1 w2 r, azim_sub_self z w w1 w2]
  exact volume_ball_wedge_zero hr

end Kepler.Geom
