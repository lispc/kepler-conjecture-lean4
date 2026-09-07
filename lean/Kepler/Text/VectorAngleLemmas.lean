/-
Port of the HOL Light vector-angle basic properties
(Multivariate-geom.ml).

Source: persistent copy `/home/scroll/hol-light-ref/Multivariate-geom.ml`.

Coverage:
- `VECTOR_ANGLE_SYM` (52) ↦ `vectorAngle_comm`.
- `VECTOR_ANGLE_RANGE` (125) ↦ `vectorAngle_nonneg` / `vectorAngle_le_pi`.
- `VECTOR_ANGLE_EQ_0` (145) ↦ `vectorAngle_eq_zero_iff`（正倍数形式）、
  `vectorAngle_eq_zero_iff_norm`（HOL 原文 `norm(x) % y = norm(y) % x` 形式）.
- `VECTOR_ANGLE_EQ_PI` (156) ↦ `vectorAngle_eq_pi_iff`（负倍数形式）、
  `vectorAngle_eq_pi_iff_norm`（HOL 原文 `norm(x) % y + norm(y) % x = vec 0`
  形式）.
- `COLLINEAR_VECTOR_ANGLE` (325) ↦ `collinear3_iff_vectorAngle`
  （`collinear {vec 0, x, y}` ↦ `Collinear3 0 x y`）.
- `COLLINEAR_SIN_VECTOR_ANGLE` (334) ↦ `collinear3_iff_sin_vectorAngle`.
- `COLLINEAR_SIN_VECTOR_ANGLE_IMP` (339) ↦ `sin_vectorAngle_eq_zero_imp`
  （sin = 0 迫使夹角 ∈ {0, π}；若有一向量为 0 则夹角为 π/2 且 sin = 1，
  矛盾，对应 HOL 证明中的 EQ_0_DIST/EQ_PI_DIST 部分）.
- `VECTOR_ANGLE_EQ_0_RIGHT` (345) ↦ `vectorAngle_eq_zero_right`.
- `VECTOR_ANGLE_EQ_0_LEFT` (356) ↦ `vectorAngle_eq_zero_left`.
- `VECTOR_ANGLE_EQ_PI_RIGHT` (361) ↦ `vectorAngle_eq_pi_right`.
- `VECTOR_ANGLE_EQ_PI_LEFT` (369) ↦ `vectorAngle_eq_pi_left`.
- `COS_VECTOR_ANGLE` (374) ↦ `cos_vectorAngle`.
- 辅助引理 `sin_vectorAngle_eq_zero_iff`（正弦为零 ↦ 夹角为 0 或 π，
  对应 HOL `SIN_VECTOR_ANGLE_EQ_0`）.

Key bridge: Mathlib 的 `InnerProductGeometry.angle` 定义为
`arccos (inner/(‖·‖*‖·‖))`，无零向量特判；由垃圾约定（`inner 0 y = 0`、
`0/0 = 0`、`arccos 0 = π/2`）与本库 `vectorAngle`（零向量时取 π/2）逐点
相等，故大量复用 Mathlib 角度引理。

Conventions: HOL line numbers in the head comment of each item; zero
`sorry`/`native_decide`/new axioms.
-/

import Kepler.Text.Planarity
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

set_option maxHeartbeats 5000000

namespace Kepler.Text

open Kepler.Geom

variable {x y : V3}

/-- 桥接引理：`vectorAngle` 与 Mathlib `InnerProductGeometry.angle` 在 V3 上
逐点相等（零向量退化情形由垃圾约定同样给出 π/2）。 -/
theorem vectorAngle_eq_angle :
    vectorAngle x y = InnerProductGeometry.angle x y := by
  by_cases hx : x = 0
  · subst hx
    simp [vectorAngle, InnerProductGeometry.angle]
  by_cases hy : y = 0
  · subst hy
    simp [vectorAngle, InnerProductGeometry.angle]
  rw [vectorAngle, if_neg (not_or.mpr ⟨hx, hy⟩), InnerProductGeometry.angle,
    inner_eq_dot]

/-- HOL Multivariate-geom.ml:52 `VECTOR_ANGLE_SYM`. -/
theorem vectorAngle_comm : vectorAngle x y = vectorAngle y x := by
  rw [vectorAngle_eq_angle, vectorAngle_eq_angle, InnerProductGeometry.angle_comm]

/-- HOL Multivariate-geom.ml:125 `VECTOR_ANGLE_RANGE`（第一半）。 -/
theorem vectorAngle_nonneg : 0 ≤ vectorAngle x y := by
  rw [vectorAngle_eq_angle]
  exact InnerProductGeometry.angle_nonneg x y

/-- HOL Multivariate-geom.ml:125 `VECTOR_ANGLE_RANGE`（第二半）。 -/
theorem vectorAngle_le_pi : vectorAngle x y ≤ Real.pi := by
  rw [vectorAngle_eq_angle]
  exact InnerProductGeometry.angle_le_pi x y

/-- HOL Multivariate-geom.ml:145 `VECTOR_ANGLE_EQ_0`：夹角为 0 当且仅当两向
量非零且一者为另一者的正倍数（HOL 原文用 `norm(x) % y = norm(y) % x`
表达同向，见 `vectorAngle_eq_zero_iff_norm`）。 -/
theorem vectorAngle_eq_zero_iff :
    vectorAngle x y = 0 ↔ x ≠ 0 ∧ ∃ c : ℝ, 0 < c ∧ y = c • x := by
  rw [vectorAngle_eq_angle, InnerProductGeometry.angle_eq_zero_iff]

/-- HOL Multivariate-geom.ml:145 `VECTOR_ANGLE_EQ_0`（HOL 原文形式：
`norm(x) % y = norm(y) % x`）。 -/
theorem vectorAngle_eq_zero_iff_norm :
    vectorAngle x y = 0 ↔ x ≠ 0 ∧ y ≠ 0 ∧ ‖x‖ • y = ‖y‖ • x := by
  rw [vectorAngle_eq_zero_iff]
  constructor
  · rintro ⟨hx, c, hc, rfl⟩
    refine ⟨hx, ?_, ?_⟩
    · refine norm_ne_zero_iff.mp ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_ne_zero hc.ne' (norm_ne_zero_iff.mpr hx)
    · rw [smul_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_comm ‖x‖ c]
  · rintro ⟨hx, hy, h⟩
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hyc : y = (‖y‖ / ‖x‖) • x := by
      have h1 : ‖x‖⁻¹ • (‖x‖ • y) = ‖x‖⁻¹ • (‖y‖ • x) := by rw [h]
      rw [smul_smul, inv_mul_cancel₀ hxn, one_smul, smul_smul,
        mul_comm ‖x‖⁻¹ ‖y‖] at h1
      rw [div_eq_mul_inv]
      exact h1
    exact ⟨hx, ⟨‖y‖ / ‖x‖, div_pos (norm_pos_iff.mpr hy) (norm_pos_iff.mpr hx),
      hyc⟩⟩

/-- HOL Multivariate-geom.ml:156 `VECTOR_ANGLE_EQ_PI`：夹角为 π 当且仅当两
向量非零且一者为另一者的负倍数（HOL 原文用 `norm(x) % y + norm(y) % x =
vec 0` 表达反向，见 `vectorAngle_eq_pi_iff_norm`）。 -/
theorem vectorAngle_eq_pi_iff :
    vectorAngle x y = Real.pi ↔ x ≠ 0 ∧ ∃ c : ℝ, c < 0 ∧ y = c • x := by
  rw [vectorAngle_eq_angle, InnerProductGeometry.angle_eq_pi_iff]

/-- HOL Multivariate-geom.ml:156 `VECTOR_ANGLE_EQ_PI`（HOL 原文形式：
`norm(x) % y + norm(y) % x = vec 0`）。 -/
theorem vectorAngle_eq_pi_iff_norm :
    vectorAngle x y = Real.pi ↔ x ≠ 0 ∧ y ≠ 0 ∧ ‖x‖ • y + ‖y‖ • x = 0 := by
  rw [vectorAngle_eq_pi_iff]
  constructor
  · rintro ⟨hx, c, hc, rfl⟩
    refine ⟨hx, ?_, ?_⟩
    · refine norm_ne_zero_iff.mp ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_neg hc]
      exact mul_ne_zero (neg_ne_zero.mpr hc.ne) (norm_ne_zero_iff.mpr hx)
    · rw [smul_smul, norm_smul, Real.norm_eq_abs, abs_of_neg hc, ← add_smul,
      show ‖x‖ * c + -c * ‖x‖ = 0 from by ring, zero_smul]
  · rintro ⟨hx, hy, h⟩
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have h1 : ‖x‖⁻¹ • (‖x‖ • y + ‖y‖ • x) = ‖x‖⁻¹ • (0 : V3) := by rw [h]
    rw [smul_add, smul_smul, inv_mul_cancel₀ hxn, one_smul, smul_smul,
      mul_comm ‖x‖⁻¹ ‖y‖, smul_zero] at h1
    refine ⟨hx, ⟨-‖y‖ / ‖x‖,
      div_neg_of_neg_of_pos (neg_lt_zero.mpr (norm_pos_iff.mpr hy))
        (norm_pos_iff.mpr hx), ?_⟩⟩
    rw [div_eq_mul_inv, neg_mul, neg_smul]
    exact eq_neg_of_add_eq_zero_left h1

/-- HOL Multivariate-geom.ml:325 `COLLINEAR_VECTOR_ANGLE`：两非零向量与原点
三点共线当且仅当夹角为 0 或 π（`collinear {vec 0, x, y}` ↦
`Collinear3 0 x y`）。 -/
theorem collinear3_iff_vectorAngle (hx : x ≠ 0) (hy : y ≠ 0) :
    Collinear3 0 x y ↔ vectorAngle x y = 0 ∨ vectorAngle x y = Real.pi := by
  rw [collinear3_iff_smul (v := 0) (w := x) (w1 := y) hx, sub_zero, sub_zero,
    vectorAngle_eq_zero_iff, vectorAngle_eq_pi_iff]
  constructor
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := by
      intro h0
      apply hy
      rw [h0, zero_smul]
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · exact Or.inr ⟨hx, ⟨c, hneg, rfl⟩⟩
    · exact Or.inl ⟨hx, ⟨c, hpos, rfl⟩⟩
  · rintro (⟨_, c, _, rfl⟩ | ⟨_, c, _, rfl⟩)
    · exact ⟨c, rfl⟩
    · exact ⟨c, rfl⟩

variable {z : V3}

/-- 辅助引理（HOL `SIN_VECTOR_ANGLE_EQ_0`）：夹角正弦为零当且仅当夹角为
0 或 π（正弦在开区间 (0, π) 内恒正）。 -/
theorem sin_vectorAngle_eq_zero_iff :
    Real.sin (vectorAngle x y) = 0 ↔ vectorAngle x y = 0 ∨ vectorAngle x y = Real.pi := by
  constructor
  · intro h
    rcases eq_or_lt_of_le (vectorAngle_nonneg (x := x) (y := y)) with h0 | hpos
    · exact Or.inl h0.symm
    · rcases lt_or_eq_of_le (vectorAngle_le_pi (x := x) (y := y)) with hlt | heq
      · exact absurd h (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt))
      · exact Or.inr heq
  · rintro (h | h)
    · rw [h, Real.sin_zero]
    · rw [h, Real.sin_pi]

/-- HOL Multivariate-geom.ml:334 `COLLINEAR_SIN_VECTOR_ANGLE`. -/
theorem collinear3_iff_sin_vectorAngle (hx : x ≠ 0) (hy : y ≠ 0) :
    Collinear3 0 x y ↔ Real.sin (vectorAngle x y) = 0 := by
  rw [collinear3_iff_vectorAngle hx hy]
  exact sin_vectorAngle_eq_zero_iff.symm

/-- HOL Multivariate-geom.ml:339 `COLLINEAR_SIN_VECTOR_ANGLE_IMP`：正弦为零
迫使夹角 ∈ {0, π}，而零向量夹角为 π/2（正弦为 1），故两向量均非零。 -/
theorem sin_vectorAngle_eq_zero_imp (h : Real.sin (vectorAngle x y) = 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ Collinear3 0 x y := by
  have hx : x ≠ 0 := by
    intro h0
    subst h0
    rw [vectorAngle, if_pos (Or.inl rfl), Real.sin_pi_div_two] at h
    exact one_ne_zero h
  have hy : y ≠ 0 := by
    intro h0
    subst h0
    rw [vectorAngle, if_pos (Or.inr rfl), Real.sin_pi_div_two] at h
    exact one_ne_zero h
  rcases sin_vectorAngle_eq_zero_iff.mp h with h0 | h0
  · exact ⟨hx, hy, (collinear3_iff_vectorAngle hx hy).mpr (Or.inl h0)⟩
  · exact ⟨hx, hy, (collinear3_iff_vectorAngle hx hy).mpr (Or.inr h0)⟩

/-- HOL Multivariate-geom.ml:345 `VECTOR_ANGLE_EQ_0_RIGHT`：夹角为 0 时第二
向量换成其正倍数，与第三向量的夹角不变（HOL 走 `VECTOR_ANGLE_LMUL`）。 -/
theorem vectorAngle_eq_zero_right (h : vectorAngle x y = 0) :
    vectorAngle x z = vectorAngle y z := by
  obtain ⟨_, c, hc, rfl⟩ := vectorAngle_eq_zero_iff.mp h
  rw [vectorAngle_eq_angle, vectorAngle_eq_angle,
    InnerProductGeometry.angle_smul_left_of_pos x z hc]

/-- HOL Multivariate-geom.ml:356 `VECTOR_ANGLE_EQ_0_LEFT`. -/
theorem vectorAngle_eq_zero_left (h : vectorAngle x y = 0) :
    vectorAngle z x = vectorAngle z y := by
  rw [vectorAngle_comm (x := z) (y := x), vectorAngle_comm (x := z) (y := y),
    vectorAngle_eq_zero_right h]

/-- HOL Multivariate-geom.ml:361 `VECTOR_ANGLE_EQ_PI_RIGHT`：夹角为 π 时第二
向量换成其负倍数，与第三向量的夹角关于 π 互补（HOL 走 `VECTOR_ANGLE_LNEG`）。 -/
theorem vectorAngle_eq_pi_right (h : vectorAngle x y = Real.pi) :
    vectorAngle x z = Real.pi - vectorAngle y z := by
  obtain ⟨_, c, hc, rfl⟩ := vectorAngle_eq_pi_iff.mp h
  rw [vectorAngle_eq_angle, vectorAngle_eq_angle,
    InnerProductGeometry.angle_smul_left_of_neg x z hc,
    InnerProductGeometry.angle_neg_left x z]
  ring

/-- HOL Multivariate-geom.ml:369 `VECTOR_ANGLE_EQ_PI_LEFT`. -/
theorem vectorAngle_eq_pi_left (h : vectorAngle x y = Real.pi) :
    vectorAngle z x = Real.pi - vectorAngle z y := by
  rw [vectorAngle_comm (x := z) (y := x), vectorAngle_comm (x := z) (y := y),
    vectorAngle_eq_pi_right h]

/-- HOL Multivariate-geom.ml:374 `COS_VECTOR_ANGLE`：夹角余弦的显式公式，
零向量退化时为 0（垃圾约定 cos π/2 = 0）。 -/
theorem cos_vectorAngle :
    Real.cos (vectorAngle x y) =
      if x = 0 ∨ y = 0 then 0 else (x ⬝ᵥ y) / (‖x‖ * ‖y‖) := by
  by_cases hx : x = 0
  · subst hx
    rw [vectorAngle, if_pos (Or.inl rfl), Real.cos_pi_div_two, if_pos (Or.inl rfl)]
  by_cases hy : y = 0
  · subst hy
    rw [vectorAngle, if_pos (Or.inr rfl), Real.cos_pi_div_two, if_pos (Or.inr rfl)]
  rw [if_neg (not_or.mpr ⟨hx, hy⟩), vectorAngle_eq_angle,
    InnerProductGeometry.cos_angle, inner_eq_dot]
