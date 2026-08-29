/-
Kepler.Geom.Azim — 方位角与正交标架（flyspeck 第 3/4 章几何词汇，Lean 移植）

源：HOL Light `Multivariate/flyspeck.ml`（持久副本
`/home/scroll/hol-light-ref/Multivariate-flyspeck.ml`；fan 章经
`text_formalization/general/sphere.hl` 消费该词汇）。

- `orthonormal`（flyspeck.ml:1864）：三向量标准正交且右手系。
- `azim`（flyspeck.ml:2148 `azim_def`）：方位角。轴 `w - v` 定为 `e3`，
  `w1` 与 `w2` 的水平角差；退化（轴上共线）时为 0。选择算子 `@`
  对应 `Classical.epsilon`（HOL @ 在无见证时给出垃圾值，理论只在
  `azim` 的特征定理 `AZIM_EXISTS`（flyspeck.ml:2200+）非退化情形下消费它）。
- `aff_ge` / `affsign` / `lin_combo`（flyspeck.ml:685–699）：下一块
  （`Kepler/Geom/Aff.lean`）落地；HOL 的集合和 `sum`/`vsum` 语义在
  无限集上为废值，Lean 侧将带 `Set.Finite` 显式化。

Mathlib 对应：`EuclideanSpace ℝ (Fin 3)`（= HOL `real^3`）、
`Matrix.dotProduct`（`dot`）、`Matrix.cross`（`cross`，右手系）、
`Collinear ℝ {v,w,w1}`（`collinear {v,w,w1}`）。
-/

import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Classical

namespace Kepler.Geom

/-- HOL `real^3`。 -/
abbrev V3 : Type := EuclideanSpace ℝ (Fin 3)

/-- HOL `orthonormal e1 e2 e3`（flyspeck.ml:1864）：
标准正交 + 右手系（`(e1 cross e2) dot e3 > 0`）。 -/
def Orthonormal3 (e1 e2 e3 : V3) : Prop :=
  e1 ⬝ᵥ e1 = 1 ∧ e2 ⬝ᵥ e2 = 1 ∧ e3 ⬝ᵥ e3 = 1 ∧
    e1 ⬝ᵥ e2 = 0 ∧ e1 ⬝ᵥ e3 = 0 ∧ e2 ⬝ᵥ e3 = 0 ∧
    0 < (crossProduct (e1 : Fin 3 → ℝ) (e2 : Fin 3 → ℝ)) ⬝ᵥ (e3 : Fin 3 → ℝ)

/-- HOL `collinear {v,w,w1}` 的薄封装（geom.ml 的 `collinear`）。 -/
def Collinear3 (v w w1 : V3) : Prop := Collinear ℝ ({v, w, w1} : Set V3)

/-- `azim` 的特征谓词（`azim_def` 中 `@theta` 的身体，非退化情形）。 -/
def AzimSpec (v w w1 w2 : V3) (theta : ℝ) : Prop :=
  0 ≤ theta ∧ theta < 2 * Real.pi ∧
    ∃ h1 h2 : ℝ, ∀ e1 e2 e3 : V3, Orthonormal3 e1 e2 e3 →
      ((w - v : V3) = dist w v • e3) → w ≠ v →
      ∃ psi r1 r2 : ℝ,
        (w1 - v : V3) = (r1 * Real.cos psi) • (e1 : V3) +
            (r1 * Real.sin psi) • (e2 : V3) + h1 • ((w - v : V3)) ∧
        (w2 - v : V3) = (r2 * Real.cos (psi + theta)) • (e1 : V3) +
            (r2 * Real.sin (psi + theta)) • (e2 : V3) + h2 • ((w - v : V3)) ∧
        0 < r1 ∧ 0 < r2

/-- HOL `azim v w w1 w2`（flyspeck.ml:2148 `azim_def`）。 -/
noncomputable def azim (v w w1 w2 : V3) : ℝ :=
  if Collinear3 v w w1 ∨ Collinear3 v w w2 then 0
  else Classical.epsilon (AzimSpec v w w1 w2)

/-- HOL `wedge v0 v1 w1 w2`（flyspeck.ml:3714）：两条方位射线之间的开楔形。 -/
def wedge (v0 v1 w1 w2 : V3) : Set V3 :=
  {y | ¬ Collinear3 v0 v1 y ∧ 0 < azim v0 v1 w1 y ∧ azim v0 v1 w1 y < azim v0 v1 w1 w2}

end Kepler.Geom
