/-
Kepler.Geom.SimplexVolume — gammaX Wave V：体积桥（docs/gamax-bridge-scout.md V1–V4）。

四面体实体积桥，供下一波接通 PA20 `gammaX_gamm4fgcy` / `gammaX_gamma3f` 的
`volume.real (convexHull …) = volY …` 槽。本文件不 import PA20：消费接线在下一波
由 PA20 反向 import 本模块（避免模块环）。四层：

  V1  标准单形测度：`volume.real stdTetra = 1/6`。路线：`Fin n → ℝ` 上的标准单形
      `piSimplex n` 经 `measurePreserving_piFinSuccAbove`（Fubini 切片，唯一真新
      测度件）+ `Measure.addHaar_smul`（切片缩放 c^n）+ `integral_pow` 逐维递降，
      再经 `WithLp.toLp`（volume-preserving）搬运到 V3。
  V2  迁移：平移不变（复用 `Kepler.Geom.Volume.volume_real_add_left`）+ 线性映射
      `|det|` 缩放（`Measure.addHaar_image_linearMap`，PA15:2069-2071 实战模板）。
  V3  Gram 代数：六距离平方的 `Kepler.Text.deltaX` = 4 × Gram 行列式（纯环等式
      `deltaX_eq_four_mul_det_gram`）；`LinearMap.normDet` 桥
      （`normDet_sq_eq_det_gram` + `normDet_eq_norm_det`，Mathlib NormDet.lean:304）
      把 |det f|² 接到 Gram 行列式。
  V4  装配：`volume.real (convexHull ℝ {p0,p1,p2,p3}) = √(deltaX 六距离²)/12`。
      右端与 PA20 `volY y1…y6 = volXf (y1²)…(y6²) = √(deltaX (y1²)…)/12`
      （PackingAuto20.lean:99-104）定义相等；y1..y6 排列约定与
      `gammaX_gamm4fgcy`（PackingAuto20.lean:1473-1475）一致：
        y1 = dist p0 p1, y2 = dist p0 p2, y3 = dist p0 p3,
        y4 = dist p2 p3, y5 = dist p1 p3, y6 = dist p1 p2.

零 sorry；公理仅标准三（Geom 层纪律）。
-/

import Mathlib
import Kepler.Geom.Volume
import Kepler.Text.SphereKit

set_option maxHeartbeats 5000000

namespace Kepler.Geom

open MeasureTheory Measure Set Classical
open scoped Pointwise InnerProductSpace

/-! ## 公共小件 -/

/-- 内积的半和公式（极化恒等式的实形式）。 -/
private theorem inner_eq_halfof (x y : V3) :
    ⟪x, y⟫_ℝ = (‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2) / 2 := by
  rw [norm_sub_sq_real]
  ring

/-- 差向量范数的距离形。 -/
private theorem norm_sub_eq_dist (p q : V3) : ‖p - q‖ = dist q p := by
  rw [dist_eq_norm, norm_sub_rev]

/-- `ofLp` 与 `Finset.sum` 交换。 -/
private theorem ofLp_sum {ι : Type*} [Fintype ι] (s : Finset ι) (g : ι → V3) :
    (WithLp.ofLp (∑ i ∈ s, g i)) = ∑ i ∈ s, WithLp.ofLp (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [ha, ih, WithLp.ofLp_add]

/-- `MeasurableEquiv.toLp` 的函数形与 `WithLp.toLp 2` 一致。 -/
private theorem toLp_eq (x : Fin 3 → ℝ) :
    (WithLp.toLp 2 x : V3) = (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) x := rfl

/-! ## V3：Gram 代数 — `deltaX`（六距离平方）= 4 × Gram 行列式 -/

/-- 纯代数核：以六距离 y1..y6（PA20 约定）为变量的 `Kepler.Text.deltaX` 恰为
半和型 Gram 矩阵（对角 `y_i²`，非对角半和 `(y_i² + y_j² - y_k²)/2`）的行列式的
4 倍（Cayley–Menger 的 Gram 形；`ring` 级恒等式）。 -/
theorem deltaX_eq_four_mul_det_gram (y1 y2 y3 y4 y5 y6 : ℝ) :
    Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) / 4
      = Matrix.det (Matrix.of
          ![![y1 * y1, (y1 * y1 + y2 * y2 - y6 * y6) / 2, (y1 * y1 + y3 * y3 - y5 * y5) / 2],
            ![(y1 * y1 + y2 * y2 - y6 * y6) / 2, y2 * y2, (y2 * y2 + y3 * y3 - y4 * y4) / 2],
            ![(y1 * y1 + y3 * y3 - y5 * y5) / 2, (y2 * y2 + y3 * y3 - y4 * y4) / 2, y3 * y3]]) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  unfold Kepler.Text.deltaX
  field_simp
  ring

/-- 把标准基映到给定三向量的线性件（`Basis.constr`）。 -/
noncomputable def tetraMap (v1 v2 v3 : V3) : V3 →ₗ[ℝ] V3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr ℝ ![v1, v2, v3]

/-- `tetraMap` 在标准正交基上的取值。 -/
theorem tetraMap_basis (v1 v2 v3 : V3) (i : Fin 3) :
    tetraMap v1 v2 v3 ((EuclideanSpace.basisFun (Fin 3) ℝ) i) = ![v1, v2, v3] i :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr_basis ℝ ![v1, v2, v3] i

/-- Gram 矩阵（`Matrix.gram` 条目 = 内积）在标准基坐标下的显式矩阵。 -/
theorem gram_tetra_eq (v1 v2 v3 : V3) :
    (Matrix.gram ℝ fun i : Fin 3 => tetraMap v1 v2 v3 ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
      = Matrix.of ![![⟪v1, v1⟫_ℝ, ⟪v1, v2⟫_ℝ, ⟪v1, v3⟫_ℝ],
                    ![⟪v2, v1⟫_ℝ, ⟪v2, v2⟫_ℝ, ⟪v2, v3⟫_ℝ],
                    ![⟪v3, v1⟫_ℝ, ⟪v3, v2⟫_ℝ, ⟪v3, v3⟫_ℝ]] := by
  have hb := tetraMap_basis v1 v2 v3
  ext i j
  simp only [Matrix.gram, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [hb, Matrix.head_cons, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one] <;> rfl

/-- **V3 主件**：`tetraMap v1 v2 v3` 的 `det` 平方 = 六距离平方的 `deltaX` / 4，
其中 y1..y6 按被映向量两两长度的 PA20 约定读取。 -/
theorem det_sq_eq_deltaX_div_four (v1 v2 v3 : V3)
    (y1 y2 y3 y4 y5 y6 : ℝ)
    (h1 : ‖v1‖ = y1) (h2 : ‖v2‖ = y2) (h3 : ‖v3‖ = y3)
    (h4 : ‖v2 - v3‖ = y4) (h5 : ‖v1 - v3‖ = y5) (h6 : ‖v1 - v2‖ = y6) :
    (LinearMap.det (tetraMap v1 v2 v3)) ^ 2
      = Kepler.Text.deltaX (y1 * y1) (y2 * y2) (y3 * y3) (y4 * y4) (y5 * y5) (y6 * y6) / 4 := by
  -- Gram 矩阵 = 半和矩阵
  have hgram : (Matrix.gram ℝ
        fun i : Fin 3 => tetraMap v1 v2 v3 ((EuclideanSpace.basisFun (Fin 3) ℝ) i))
      = Matrix.of
          ![![y1 * y1, (y1 * y1 + y2 * y2 - y6 * y6) / 2, (y1 * y1 + y3 * y3 - y5 * y5) / 2],
            ![(y1 * y1 + y2 * y2 - y6 * y6) / 2, y2 * y2, (y2 * y2 + y3 * y3 - y4 * y4) / 2],
            ![(y1 * y1 + y3 * y3 - y5 * y5) / 2, (y2 * y2 + y3 * y3 - y4 * y4) / 2, y3 * y3]] := by
    have d24 : dist v2 v3 = y4 := by rw [dist_eq_norm]; exact h4
    have d26 : dist v1 v2 = y6 := by rw [dist_eq_norm]; exact h6
    have d15 : dist v1 v3 = y5 := by rw [dist_eq_norm]; exact h5
    rw [gram_tetra_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [inner_eq_halfof, h1, h2, h3, h4, h5, h6, d24, d26, d15, norm_sub_eq_dist,
        dist_self] <;>
      ring
  -- normDet 桥：|det f|² = Gram 行列式
  have hnd : LinearMap.normDet (tetraMap v1 v2 v3) = |LinearMap.det (tetraMap v1 v2 v3)| :=
    LinearMap.normDet_eq_norm_det _
  have hsq := LinearMap.normDet_sq_eq_det_gram (tetraMap v1 v2 v3)
    (EuclideanSpace.basisFun (Fin 3) ℝ)
  rw [hnd] at hsq
  have hsq2 : (LinearMap.det (tetraMap v1 v2 v3)) ^ 2
      = (Matrix.gram ℝ
          fun x : Fin 3 => (tetraMap v1 v2 v3) ((EuclideanSpace.basisFun (Fin 3) ℝ) x)).det := by
    rw [← sq_abs]
    exact hsq
  rw [hsq2, hgram, deltaX_eq_four_mul_det_gram]

/-! ## V1：`Fin n → ℝ` 上的标准单形测度（Fubini 切片） -/

/-- 标准单形 `{x | ∀ i, 0 ≤ x i ∧ ∑ i, x i ≤ 1}`（`Fin n → ℝ` 上）。 -/
def piSimplex (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, 0 ≤ x i ∧ ∑ i, x i ≤ 1}

theorem measurableSet_piSimplex (n : ℕ) : MeasurableSet (piSimplex n) := by
  have h1 : MeasurableSet {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    have h : {x : Fin n → ℝ | ∀ i, 0 ≤ x i}
        = ⋂ i ∈ (Set.univ : Set (Fin n)), (fun x : Fin n → ℝ => x i) ⁻¹' Ici 0 := by
      ext x
      simp [Set.mem_iInter]
    rw [h]
    exact Set.Finite.measurableSet_biInter Set.finite_univ
      fun i _ => MeasurableSet.preimage measurableSet_Ici (measurable_pi_apply i)
  have hIic : MeasurableSet (Iic (1 : ℝ)) := measurableSet_Iic
  have hsum : Measurable (fun x : Fin n → ℝ => ∑ i, x i) :=
    (continuous_finsetSum Finset.univ fun i _ => continuous_apply i).measurable
  unfold piSimplex
  rw [show ({x : Fin n → ℝ | ∀ i, 0 ≤ x i ∧ ∑ i, x i ≤ 1}
      = {x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x : Fin n → ℝ | ∑ i, x i ≤ 1}) from by
    ext x
    constructor
    · intro h
      refine ⟨fun i => (h i).1, ?_⟩
      by_cases hempty : IsEmpty (Fin n)
      · have hz0 : ∑ i ∈ (Finset.univ : Finset (Fin n)), x i = 0 :=
          Finset.sum_eq_zero fun i _ => isEmptyElim i
        rw [Set.mem_setOf_eq, hz0]
        norm_num
      · obtain ⟨i⟩ := not_isEmpty_iff.mp hempty
        exact (h i).2
    · intro h
      exact fun i => ⟨h.1 i, h.2⟩]
  exact h1.inter (MeasurableSet.preimage hIic hsum)

/-- 缩放切片（V1 备件）：`{f | f ≥ 0, ∑ f ≤ c} = c • 标准单形`（`0 ≤ c`）。 -/
theorem smul_piSimplex_slice (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    {f : Fin n → ℝ | (∀ j, 0 ≤ f j) ∧ ∑ j, f j ≤ c} = c • (piSimplex n) := by
  ext f
  simp only [Set.mem_setOf_eq, mem_smul_set, piSimplex, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hf0, hfsum⟩
    by_cases hcz : c = 0
    · refine ⟨0, fun j => ⟨by simp, by simp⟩, ?_⟩
      funext j
      rw [hcz] at hfsum
      have hz : ∑ i, f i = 0 := le_antisymm hfsum (Finset.sum_nonneg fun i _ => hf0 i)
      have hfj : f j = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hf0 i)).mp hz j (by simp)
        exact this
      simp [hfj]
    · refine ⟨c⁻¹ • f, fun j => ⟨mul_nonneg (inv_nonneg.mpr hc) (hf0 j), ?_⟩, ?_⟩
      · calc ∑ j, c⁻¹ * f j = c⁻¹ * ∑ j, f j := (Finset.mul_sum _ _ _).symm
          _ ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left hfsum (inv_nonneg.mpr hc)
          _ = 1 := inv_mul_cancel₀ hcz
      · rw [smul_smul, mul_inv_cancel₀ hcz, one_smul]
  · rintro ⟨g, hgp, hgrfl⟩
    refine ⟨fun j => by rw [← hgrfl]; exact mul_nonneg hc ((hgp j).1), ?_⟩
    have hsum : ∑ j, f j = c * ∑ j, g j := by
      rw [← hgrfl]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [hsum]
    rcases isEmpty_or_nonempty (Fin n) with hempty | hne
    · haveI := hempty
      rw [Finset.sum_eq_zero fun i _ => isEmptyElim i, mul_zero]
      exact hc
    · have j0 := Classical.choice hne
      calc c * ∑ j, g j ≤ c * 1 := mul_le_mul_of_nonneg_left ((hgp j0).2) hc
        _ = c := mul_one c

/-- 缩放切片的测度（V1 备件）：体积因子 `c^n`。 -/
theorem measure_pi_slice (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (Measure.pi fun _ : Fin n => (volume : Measure ℝ))
        {f : Fin n → ℝ | (∀ j, 0 ≤ f j) ∧ ∑ j, f j ≤ c}
      = ENNReal.ofReal (c ^ n) *
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) (piSimplex n) := by
  rw [smul_piSimplex_slice n c hc]
  have hsm := Measure.addHaar_smul (μ := (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) c
    (piSimplex n)
  rw [hsm, abs_of_nonneg (pow_nonneg hc _), Module.finrank_fin_fun ℝ]

theorem measure_piSimplex_zero :
    (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) (piSimplex 0) = 1 := by
  have h : piSimplex 0 = Set.univ := by
    ext x
    simp [piSimplex]
  rw [h]
  exact Measure.pi_empty_univ _

/-- **V1 核心（切片步）**：`(n+1)` 维标准单形测度 = `1/(n+1)` × `n` 维标准单形测度。
经 `piFinSuccAbove` 量测保持等价 + `Measure.prod_apply` 截面 + 缩放因子 `(1-t)^n`。 -/
theorem measure_piSimplex_succ (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ)) (piSimplex (n + 1))
      = ENNReal.ofReal (1 / ((n : ℝ) + 1)) *
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) (piSimplex n) := by
  classical
  set v := (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) (piSimplex n) with hv
  set e := MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (n + 1)) with he
  have hmp : MeasurePreserving e
      (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ))
      (volume.prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) :=
    MeasureTheory.measurePreserving_piFinSuccAbove _ _
  have hms : MeasurableSet (piSimplex (n + 1)) := measurableSet_piSimplex (n + 1)
  have himgm : MeasurableSet (e '' piSimplex (n + 1)) := by
    rw [MeasurableEquiv.image_eq_preimage_symm]
    exact MeasurableSet.preimage hms e.symm.measurable
  have h0 : (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ)) (piSimplex (n + 1))
      = (volume.prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ)))
          (e '' piSimplex (n + 1)) := by
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable himgm,
      Set.preimage_image_eq _ e.injective]
  rw [h0, Measure.prod_apply himgm]
  -- 逐截面刻画：先把 (n+1) 维条件归约到 0 号坐标 + 其余 n 维
  have hexiff : ∀ x : Fin (n + 1) → ℝ, x ∈ piSimplex (n + 1) ↔
      0 ≤ x (0 : Fin (n + 1)) ∧
        (∀ j, 0 ≤ x (Fin.succAbove (0 : Fin (n + 1)) j)) ∧
        ∑ j, x (Fin.succAbove (0 : Fin (n + 1)) j) ≤ 1 - x (0 : Fin (n + 1)) := by
    intro x
    unfold piSimplex
    constructor
    · intro hmem
      have h0 : 0 ≤ x (0 : Fin (n + 1)) := (hmem (0 : Fin (n + 1))).1
      have hall : ∀ j, 0 ≤ x (Fin.succAbove (0 : Fin (n + 1)) j) := fun j => (hmem _).1
      have hsum1 : ∑ i, x i ≤ 1 := (hmem (0 : Fin (n + 1))).2
      rw [Fin.sum_univ_succAbove (fun i => x i) (0 : Fin (n + 1))] at hsum1
      have hs2 : 0 ≤ ∑ j, x (Fin.succAbove (0 : Fin (n + 1)) j) :=
        Finset.sum_nonneg fun j _ => hall j
      exact ⟨h0, hall, by linarith⟩
    · intro h
      have hall : ∀ i, 0 ≤ x i := by
        rw [Fin.forall_iff_succAbove (0 : Fin (n + 1))]
        exact ⟨h.1, h.2.1⟩
      refine fun i => ⟨hall i, ?_⟩
      rw [Fin.sum_univ_succAbove (fun i => x i) (0 : Fin (n + 1))]
      linarith
  have hmp' : ∀ (t' : ℝ) (g : Fin n → ℝ) (j : Fin n),
      e.symm (t', g) (Fin.succAbove (0 : Fin (n + 1)) j) = g j :=
    fun t' g j => Fin.insertNth_apply_succAbove (α := fun _ => ℝ) (0 : Fin (n + 1)) t' g j
  have hms' : ∀ (t' : ℝ) (g : Fin n → ℝ),
      e.symm (t', g) (0 : Fin (n + 1)) = t' :=
    fun t' g => Fin.insertNth_apply_same (α := fun _ => ℝ) (0 : Fin (n + 1)) t' g
  have himgsec : ∀ t : ℝ, Prod.mk t ⁻¹' (e '' piSimplex (n + 1))
      = {f : Fin n → ℝ | 0 ≤ t ∧ (∀ j, 0 ≤ f j) ∧ ∑ j, f j ≤ 1 - t} := by
    intro t
    ext f
    have hmem : (t, f) ∈ e '' piSimplex (n + 1) ↔ e.symm (t, f) ∈ piSimplex (n + 1) := by
      constructor
      · intro hm
        rw [Set.mem_image] at hm
        obtain ⟨x, hx, hex⟩ := hm
        rw [← hex, MeasurableEquiv.symm_apply_apply]
        exact hx
      · exact fun hx => ⟨e.symm (t, f), hx, MeasurableEquiv.apply_symm_apply e (t, f)⟩
    constructor
    · intro hf
      rw [Set.mem_preimage, hmem, hexiff (e.symm (t, f))] at hf
      simp only [hms' t f, hmp' t f] at hf
      exact hf
    · intro h
      rw [Set.mem_preimage, hmem, hexiff (e.symm (t, f))]
      simp only [hms' t f, hmp' t f]
      exact h
  -- 切片测度（0 ≤ t ≤ 1 时恒精确，含 t = 1 的 0•s 退化）
  have hsec : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ))
          {f : Fin n → ℝ | 0 ≤ t ∧ (∀ j, 0 ≤ f j) ∧ ∑ j, f j ≤ 1 - t}
        = ENNReal.ofReal ((1 - t) ^ n) * v := by
    intro t ht1 ht2
    have hs : {f : Fin n → ℝ | 0 ≤ t ∧ (∀ j, 0 ≤ f j) ∧ ∑ j, f j ≤ 1 - t}
        = {f : Fin n → ℝ | (∀ j, 0 ≤ f j) ∧ ∑ j, f j ≤ 1 - t} := by
      ext f
      simp only [Set.mem_setOf_eq]
      exact and_iff_right ht1
    rw [hs, measure_pi_slice n (1 - t) (by linarith)]
  -- 积分预备件
  have hmeas : Measurable (fun t : ℝ => ENNReal.ofReal ((1 - t) ^ n)) :=
    (ENNReal.continuous_ofReal.comp
      ((continuous_const.sub continuous_id).pow n)).measurable
  have hintegr : MeasureTheory.Integrable (fun t : ℝ => (1 - t) ^ n)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
    have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => (1 - t) ^ n) (Set.Icc (0 : ℝ) 1)
        (volume : Measure ℝ) := ((continuous_const.sub continuous_id).pow n).integrableOn_Icc
    exact h1.mono_set Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)] fun t : ℝ => (1 - t) ^ n := by
    rw [MeasureTheory.ae_restrict_eq measurableSet_Ioc]
    exact Filter.eventually_inf_principal.mpr
      (Filter.Eventually.of_forall fun t ht => by
        have h1 : 0 ≤ 1 - t := by linarith [ht.2]
        positivity)
  have hint : ∫ t : ℝ, (1 - t) ^ n ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
      = 1 / ((n : ℝ) + 1) := by
    have h2 : ∫ t : ℝ, (1 - t) ^ n ∂((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1))
        = ∫ t in Set.Ioc (0 : ℝ) 1, (1 - t) ^ n ∂(volume : Measure ℝ) := rfl
    rw [h2, ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) (1 : ℝ), integral_pow]
    norm_num
  -- a.e. 指示函数形（唯一例外点 t = 0）
  have hIoc : ∀ᵐ t : ℝ,
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ))
          (Prod.mk t ⁻¹' (e '' piSimplex (n + 1)))
        = (Set.Ioc (0 : ℝ) 1).indicator (fun t : ℝ => ENNReal.ofReal ((1 - t) ^ n) * v) t := by
    rw [MeasureTheory.ae_iff]
    have hsub : {t : ℝ | ¬ ((Measure.pi fun _ : Fin n => (volume : Measure ℝ))
          (Prod.mk t ⁻¹' (e '' piSimplex (n + 1)))
        = (Set.Ioc (0 : ℝ) 1).indicator (fun t : ℝ => ENNReal.ofReal ((1 - t) ^ n) * v) t)}
        ⊆ {0} := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      simp only [Set.mem_singleton_iff]
      by_cases ht0 : t = 0
      · exact ht0
      by_cases htI : t ∈ Set.Ioc (0 : ℝ) 1
      · exact absurd (by
          rw [himgsec t, Set.indicator_of_mem htI]
          exact hsec t (le_of_lt htI.1) htI.2) ht
      · exfalso
        apply ht
        have hR : (Set.Ioc (0 : ℝ) 1).indicator
            (fun t : ℝ => ENNReal.ofReal ((1 - t) ^ n) * v) t = 0 :=
          Set.indicator_of_notMem htI (fun t => ENNReal.ofReal ((1 - t) ^ n) * v)
        by_cases hneg : t < 0
        · have hE : {f : Fin n → ℝ | 0 ≤ t ∧ (∀ j, 0 ≤ f j) ∧ ∑ j, f j ≤ 1 - t} = ∅ := by
            ext f
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
            rintro ⟨h0, -, -⟩
            exact absurd h0 (by linarith)
          rw [himgsec, hE, hR]
          simp
        · by_cases ht1 : t = 1
          · -- t = 1：走 hsec 路线（0 ≤ 1 ≤ 1）
            rw [ht1, himgsec 1]
            have hm : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
              simp only [Set.mem_Ioc]; norm_num
            rw [Set.indicator_of_mem hm]
            exact hsec 1 (by norm_num) (by norm_num)
          · have h0t : 0 < t := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm ht0)
            have h1t : 1 < t := lt_of_not_ge fun hle => htI ⟨h0t, hle⟩
            have hE : {f : Fin n → ℝ | 0 ≤ t ∧ (∀ j, 0 ≤ f j) ∧ ∑ j, f j ≤ 1 - t} = ∅ := by
              ext f
              simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              rintro ⟨h0, hall, hsum⟩
              have hsum0 : 0 ≤ ∑ j, f j := Finset.sum_nonneg fun j _ => hall j
              linarith
            rw [himgsec, hE, hR]
            simp
    have h0v : (volume : Measure ℝ) {0} = 0 := Real.volume_singleton
    have hle : (volume : Measure ℝ) {t : ℝ | ¬ ((Measure.pi fun _ : Fin n => (volume : Measure ℝ))
        (Prod.mk t ⁻¹' (e '' piSimplex (n + 1)))
      = (Set.Ioc (0 : ℝ) 1).indicator (fun t : ℝ => ENNReal.ofReal ((1 - t) ^ n) * v) t)}
      ≤ (volume : Measure ℝ) {0} := measure_mono hsub
    exact le_antisymm (le_trans hle (le_of_eq h0v)) zero_le
  -- 装配
  rw [lintegral_congr_ae hIoc, lintegral_indicator measurableSet_Ioc]
  rw [lintegral_mul_const v hmeas]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (μ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) hintegr hnn]
  rw [hint]

/-- **V1 主定理**：`Fin n → ℝ` 上标准单形测度 = `1/n!`。 -/
theorem measure_piSimplex (n : ℕ) :
    (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) (piSimplex n)
      = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  induction n with
  | zero =>
    rw [measure_piSimplex_zero]
    simp
  | succ n ih =>
    rw [measure_piSimplex_succ, ih, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    push_cast [Nat.factorial_succ]
    ring

/-! ## V1'：标准四面体（V3）= 1/6 -/

/-- 标准四面体：0 与三个单位坐标向量的凸包。 -/
noncomputable def stdTetra : Set V3 :=
  convexHull ℝ (insert (0 : V3)
    {PiLp.single 2 (0 : Fin 3) (1 : ℝ), PiLp.single 2 1 (1 : ℝ), PiLp.single 2 2 (1 : ℝ)})

/-- 生成点的坐标事实：坐标非负、坐标和 ≤ 1。 -/
private theorem pt_facts (u : V3) (hu : u = 0 ∨ u = PiLp.single 2 (0 : Fin 3) (1 : ℝ) ∨
    u = PiLp.single 2 1 (1 : ℝ) ∨ u = PiLp.single 2 2 (1 : ℝ)) :
    (∀ j, 0 ≤ (WithLp.ofLp u) j) ∧ ∑ j, (WithLp.ofLp u) j ≤ 1 := by
  rcases hu with rfl | rfl | rfl | rfl
  · simp
  · refine ⟨fun j => by by_cases h : j = 0 <;> simp [h, PiLp.single_apply], ?_⟩
    rw [Fin.sum_univ_three]
    simp
  · refine ⟨fun j => by by_cases h : j = 1 <;> simp [h, PiLp.single_apply], ?_⟩
    rw [Fin.sum_univ_three]
    simp
  · refine ⟨fun j => by by_cases h : j = 2 <;> simp [h, PiLp.single_apply], ?_⟩
    rw [Fin.sum_univ_three]
    simp

/-- 标准四面体 = `piSimplex 3` 经 `WithLp.toLp 2` 的像。 -/
theorem stdTetra_eq_image :
    stdTetra = (WithLp.toLp 2 : (Fin 3 → ℝ) → V3) '' (piSimplex 3) := by
  ext x
  show x ∈ stdTetra ↔ x ∈ (WithLp.toLp 2 : (Fin 3 → ℝ) → V3) '' (piSimplex 3)
  constructor
  · -- 凸组合 ⇒ 坐标非负、坐标和 ≤ 1
    intro hx
    obtain ⟨ι, _, w, z, hw0, hw1, hz, hxz⟩ := mem_convexHull_iff_exists_fintype.mp hx
    have hzf : ∀ i : ι, (z i = 0 ∨ z i = PiLp.single 2 (0 : Fin 3) (1 : ℝ) ∨
        z i = PiLp.single 2 1 (1 : ℝ) ∨ z i = PiLp.single 2 2 (1 : ℝ)) := by
      intro i
      have hi := hz i
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      exact hi
    refine ⟨WithLp.ofLp x, fun j => ⟨?_, ?_⟩, WithLp.toLp_ofLp 2 x⟩
    · -- 0 ≤ ofLp x j
      have hentry : (WithLp.ofLp x) j = ∑ i, w i * (WithLp.ofLp (z i)) j := by
        rw [← hxz, ofLp_sum, Finset.sum_apply]
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      rw [hentry]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (hw0 i) ((pt_facts _ (hzf i)).1 j)
    · -- ∑ j, ofLp x j ≤ 1
      have hentry : ∑ j, (WithLp.ofLp x) j = ∑ j, ∑ i, w i * (WithLp.ofLp (z i)) j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← hxz, ofLp_sum, Finset.sum_apply]
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      rw [hentry]
      calc ∑ j, ∑ i, w i * (WithLp.ofLp (z i)) j
          = ∑ i, ∑ j, w i * (WithLp.ofLp (z i)) j := Finset.sum_comm
        _ = ∑ i, w i * ∑ j, (WithLp.ofLp (z i)) j :=
            Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ i, w i * 1 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (pt_facts _ (hzf i)).2 (hw0 i)
        _ = ∑ i, w i := Finset.sum_congr rfl fun i _ => mul_one _
        _ = 1 := hw1
  · -- piSimplex 3 的像在凸包内（显式 Fin 4 凸组合）
    intro hx
    rw [Set.mem_image] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    have hf0 : ∀ j, 0 ≤ f j := fun j => (hf j).1
    have hf1 : ∑ j, f j ≤ 1 := (hf 0).2
    have hs0 : 0 ≤ ∑ j, f j := Finset.sum_nonneg fun j _ => hf0 j
    have hs3 : ∑ j, f j = f 0 + f 1 + f 2 := Fin.sum_univ_three f
    refine mem_convexHull_of_exists_fintype
      (fun i => (![1 - ∑ j, f j, f 0, f 1, f 2] : Fin 4 → ℝ) i)
      (fun i =>
        (![0, PiLp.single 2 (0 : Fin 3) (1 : ℝ), PiLp.single 2 1 (1 : ℝ),
            PiLp.single 2 2 (1 : ℝ)] : Fin 4 → V3) i)
      ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · show (0 : ℝ) ≤ 1 - ∑ j, f j
        linarith
      · show (0 : ℝ) ≤ f (0 : Fin 3)
        exact hf0 0
      · show (0 : ℝ) ≤ f (1 : Fin 3)
        exact hf0 1
      · show (0 : ℝ) ≤ f (2 : Fin 3)
        exact hf0 2
    · rw [Fin.sum_univ_four]
      show ((1 - ∑ j, f j : ℝ) + f (0 : Fin 3) + f (1 : Fin 3) + f (2 : Fin 3)) = 1
      linarith
    · intro i
      fin_cases i <;> simp
    · show ∑ i : Fin 4,
          (![1 - ∑ j, f j, f 0, f 1, f 2] : Fin 4 → ℝ) i •
            (![0, PiLp.single 2 (0 : Fin 3) (1 : ℝ), PiLp.single 2 1 (1 : ℝ),
                PiLp.single 2 2 (1 : ℝ)] : Fin 4 → V3) i
        = (WithLp.toLp 2 f : V3)
      have hent : ∀ j, (WithLp.ofLp (∑ i : Fin 4,
            (![1 - ∑ j, f j, f 0, f 1, f 2] : Fin 4 → ℝ) i •
              (![0, PiLp.single 2 (0 : Fin 3) (1 : ℝ), PiLp.single 2 1 (1 : ℝ),
                  PiLp.single 2 2 (1 : ℝ)] : Fin 4 → V3) i)) j = f j := by
        intro j
        rw [ofLp_sum, Fin.sum_univ_four]
        fin_cases j <;> simp
      have h1 : WithLp.toLp 2 (WithLp.ofLp (∑ i : Fin 4,
            (![1 - ∑ j, f j, f 0, f 1, f 2] : Fin 4 → ℝ) i •
              (![0, PiLp.single 2 (0 : Fin 3) (1 : ℝ), PiLp.single 2 1 (1 : ℝ),
                  PiLp.single 2 2 (1 : ℝ)] : Fin 4 → V3) i)) = WithLp.toLp 2 f := by
        rw [funext hent]
      rw [WithLp.toLp_ofLp] at h1
      exact h1

theorem measurableSet_stdTetra : MeasurableSet stdTetra := by
  have hset : (WithLp.toLp 2 : (Fin 3 → ℝ) → V3)
      = (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) := funext toLp_eq
  rw [stdTetra_eq_image, hset, MeasurableEquiv.image_eq_preimage_symm]
  exact MeasurableSet.preimage (measurableSet_piSimplex 3)
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurable

/-- **V1 主定理（V3 形）**：标准四面体体积 = 1/6。 -/
theorem volume_real_stdTetra : volume.real stdTetra = 1 / 6 := by
  have hT := PiLp.volume_preserving_toLp (Fin 3)
  have hinj : Function.Injective (WithLp.toLp 2 : (Fin 3 → ℝ) → V3) := by
    intro a b h
    have h2 : (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) a
        = (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) b := by
      rw [← toLp_eq a, ← toLp_eq b, h]
    exact (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).injective h2
  have hmeas : ∀ s : Set (Fin 3 → ℝ), MeasurableSet s →
      MeasurableSet ((WithLp.toLp 2 : (Fin 3 → ℝ) → V3) '' s) := by
    intro s hs
    have hset : (WithLp.toLp 2 : (Fin 3 → ℝ) → V3)
        = (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) := funext toLp_eq
    have h1 := MeasurableSet.preimage hs (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurable
    rwa [← MeasurableEquiv.image_eq_preimage_symm, ← hset] at h1
  have himg : (volume : Measure V3)
      ((WithLp.toLp 2 : (Fin 3 → ℝ) → V3) '' (piSimplex 3))
      = (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)) (piSimplex 3) := by
    rw [← hT.map_eq, Measure.map_apply hT.measurable
      (hmeas _ (measurableSet_piSimplex 3)),
      Set.preimage_image_eq _ hinj, volume_pi]
  rw [stdTetra_eq_image, Measure.real_def, himg, measure_piSimplex]
  norm_num [Nat.factorial]

/-! ## V2：平移与线性 |det| 迁移 -/

/-- 平移仿射映射 `q ↦ p + q`。 -/
def transMap (p : V3) : V3 →ᵃ[ℝ] V3 where
  toFun q := p + q
  linear := LinearMap.id
  map_vadd' x y := by
    simp
    abel

/-- **V2（线性迁移）**：线性像的实值测度 = `|det|` × 原
（`addHaar_image_linearMap`，PA15:2069-2071 实战模板）。 -/
theorem volume_real_linearMap_image (f : V3 →ₗ[ℝ] V3) (s : Set V3) :
    volume.real (f '' s) = |LinearMap.det f| * volume.real s := by
  rw [Measure.real_def, Measure.real_def, Measure.addHaar_image_linearMap,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- **V2（平移不变）**：平移像的实值测度不变（复用 `volume_real_add_left`）。 -/
theorem volume_real_transMap_image (p : V3) (s : Set V3) :
    volume.real ((transMap p : V3 → V3) '' s) = volume.real s :=
  volume_real_add_left p s

/-! ## V4：装配 — 四面体凸包体积 = volY 六距离 -/

/-- **V4 主定理**：四面体凸包的实体积 = `√(deltaX 六距离²)/12`，即 PA20 `volY`
六距离（`volY y1..y6 = volXf (y1²)…(y6²) = √(deltaX (y1²)…)/12`，PackingAuto20.lean:99-104，
定义相等）。y1..y6 排列约定与 PA20 `gammaX_gamm4fgcy`（:1473-1475）一致：
y1 = dist p0 p1, y2 = dist p0 p2, y3 = dist p0 p3,
y4 = dist p2 p3, y5 = dist p1 p3, y6 = dist p1 p2。 无退化性假设。 -/
theorem volume_real_convexHull_tetra (p0 p1 p2 p3 : V3) :
    volume.real (convexHull ℝ {p0, p1, p2, p3})
      = Real.sqrt (Kepler.Text.deltaX ((dist p0 p1) ^ 2) ((dist p0 p2) ^ 2) ((dist p0 p3) ^ 2)
          ((dist p2 p3) ^ 2) ((dist p1 p3) ^ 2) ((dist p1 p2) ^ 2)) / 12 := by
  classical
  set f := tetraMap (p1 - p0) (p2 - p0) (p3 - p0) with hf
  -- 距离事实接进 V3 主件（* 形式）
  have hkey := det_sq_eq_deltaX_div_four (p1 - p0) (p2 - p0) (p3 - p0)
    (dist p0 p1) (dist p0 p2) (dist p0 p3) (dist p2 p3) (dist p1 p3) (dist p1 p2)
    (by rw [norm_sub_eq_dist])
    (by rw [norm_sub_eq_dist])
    (by rw [norm_sub_eq_dist])
    (by rw [sub_sub_sub_cancel_right, norm_sub_eq_dist, dist_comm])
    (by rw [sub_sub_sub_cancel_right, norm_sub_eq_dist, dist_comm])
    (by rw [sub_sub_sub_cancel_right, norm_sub_eq_dist, dist_comm])
  rw [← hf] at hkey
  -- ^ 形与 * 形的 deltaX 互相转换
  have hD : Kepler.Text.deltaX ((dist p0 p1) ^ 2) ((dist p0 p2) ^ 2) ((dist p0 p3) ^ 2)
      ((dist p2 p3) ^ 2) ((dist p1 p3) ^ 2) ((dist p1 p2) ^ 2)
      = Kepler.Text.deltaX (dist p0 p1 * dist p0 p1) (dist p0 p2 * dist p0 p2)
        (dist p0 p3 * dist p0 p3) (dist p2 p3 * dist p2 p3)
        (dist p1 p3 * dist p1 p3) (dist p1 p2 * dist p1 p2) := by
    simp only [pow_two]
  have hB : ∀ i : Fin 3, f ((EuclideanSpace.basisFun (Fin 3) ℝ) i)
      = (![p1 - p0, p2 - p0, p3 - p0] : Fin 3 → V3) i := tetraMap_basis _ _ _
  have hsingle : ∀ i : Fin 3,
      (EuclideanSpace.basisFun (Fin 3) ℝ) i = PiLp.single 2 i (1 : ℝ) :=
    fun i => EuclideanSpace.basisFun_apply _ _ i
  -- 仿射装配：convexHull {p0,p1,p2,p3} = A '' stdTetra
  set A : V3 →ᵃ[ℝ] V3 := (transMap p0).comp f.toAffineMap with hAdef
  have hAapp : ∀ q : V3, (A : V3 → V3) q = p0 + f q := fun _ => rfl
  have hcase0 : (A : V3 → V3) 0 = p0 := by simp [hAapp, map_zero]
  have hcase1 : (A : V3 → V3) (PiLp.single 2 (0 : Fin 3) (1 : ℝ)) = p1 := by
    rw [← hsingle (0 : Fin 3), hAapp, hB (0 : Fin 3)]
    simp
  have hcase2 : (A : V3 → V3) (PiLp.single 2 1 (1 : ℝ)) = p2 := by
    rw [← hsingle 1, hAapp, hB 1]
    simp
  have hcase3 : (A : V3 → V3) (PiLp.single 2 2 (1 : ℝ)) = p3 := by
    rw [← hsingle 2, hAapp, hB 2]
    simp
  have himgset : (A : V3 → V3) '' stdTetra = convexHull ℝ {p0, p1, p2, p3} := by
    unfold stdTetra
    rw [AffineMap.image_convexHull]
    congr 1
    ext q
    rw [Set.mem_image]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      try simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz | hz | hz
      · rw [hz, hcase0]; simp
      · rw [hz, hcase1]; simp
      · rw [hz, hcase2]; simp
      · rw [hz, hcase3]; simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by simp, hcase0⟩
      · exact ⟨PiLp.single 2 (0 : Fin 3) (1 : ℝ), by simp, hcase1⟩
      · exact ⟨PiLp.single 2 1 (1 : ℝ), by simp, hcase2⟩
      · exact ⟨PiLp.single 2 2 (1 : ℝ), by simp, hcase3⟩
  -- A 像 = 平移 ∘ 线性像
  have hcomp : ((A : V3 → V3) '' stdTetra)
      = ((fun q : V3 => p0 + q) '' ((f : V3 → V3) '' stdTetra)) := by
    ext z
    rw [Set.mem_image]
    simp only [Set.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨f q, ⟨q, hq, rfl⟩, hAapp q⟩
    · rintro ⟨w, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, hAapp q⟩
  rw [← himgset, hcomp, volume_real_add_left p0, volume_real_linearMap_image,
    volume_real_stdTetra]
  -- 目标：|det f| * (1/6) = √(deltaX …)/12
  by_cases hne : LinearMap.det f = 0
  · -- 退化：det f = 0 ⇒ 两端同时为 0
    have hdX : Kepler.Text.deltaX ((dist p0 p1) ^ 2) ((dist p0 p2) ^ 2) ((dist p0 p3) ^ 2)
        ((dist p2 p3) ^ 2) ((dist p1 p3) ^ 2) ((dist p1 p2) ^ 2) = 0 := by
      rw [hD]
      have h2 := hkey
      rw [hne] at h2
      haveI : (4 : ℝ) ≠ 0 := by norm_num
      have h4 : Kepler.Text.deltaX (dist p0 p1 * dist p0 p1) (dist p0 p2 * dist p0 p2)
          (dist p0 p3 * dist p0 p3) (dist p2 p3 * dist p2 p3)
          (dist p1 p3 * dist p1 p3) (dist p1 p2 * dist p1 p2) / 4 = (0 : ℝ) ^ 2 := h2.symm
      norm_num at h4
      exact h4
    rw [hne, abs_zero, zero_mul, hdX]
    simp
  · -- 非退化：|det f| = √(deltaX/4) = √(deltaX)/2
    have hdX0 : 0 ≤ Kepler.Text.deltaX ((dist p0 p1) ^ 2) ((dist p0 p2) ^ 2) ((dist p0 p3) ^ 2)
        ((dist p2 p3) ^ 2) ((dist p1 p3) ^ 2) ((dist p1 p2) ^ 2) := by
      have h3 := hkey
      rw [← hD] at h3
      field_simp at h3
      nlinarith [sq_nonneg (LinearMap.det f)]
    have habs : |LinearMap.det f|
        = Real.sqrt (Kepler.Text.deltaX ((dist p0 p1) ^ 2) ((dist p0 p2) ^ 2) ((dist p0 p3) ^ 2)
            ((dist p2 p3) ^ 2) ((dist p1 p3) ^ 2) ((dist p1 p2) ^ 2)) / 2 := by
      have hsq4 : (Real.sqrt (4 : ℝ)) = 2 := by norm_num
      have hkey2 : (LinearMap.det f) ^ 2
          = Kepler.Text.deltaX ((dist p0 p1) ^ 2) ((dist p0 p2) ^ 2) ((dist p0 p3) ^ 2)
              ((dist p2 p3) ^ 2) ((dist p1 p3) ^ 2) ((dist p1 p2) ^ 2) / 4 := by
        rw [hkey, ← hD]
      rw [← Real.sqrt_sq_eq_abs, hkey2, Real.sqrt_div hdX0, hsq4]
    rw [habs]
    ring_nf

end Kepler.Geom
