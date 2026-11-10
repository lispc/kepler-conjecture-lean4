/-
Kepler/Text/LocalFanStepW24.lean — wave W24-①：C2 ⟺ 绕序叉积不等式（绕序槽的机器形态）。

W23 判定：C2 的 det 单调性缺「fan 相邻射线一致定向（绕序）」。本件把该槽的
**可消费形态**钉死：C2（`y ∈ affGt{0, a}{v}`，共同基系数 (b1,g1)/(b2,g2)）
等价于**绕序叉积不等式**
  `(a × y) · (v × r) < 0`
（相邻射线对 (a, y) 相对基 (v, r) 的绕序符号）。这样绕序槽可直接以
`crossProduct` 形式陈述并作为信任边界消费（与 hstep/hprev-v2 同级）。

件目：
* `pW24_c2_iff_crossdot`：C2 ⟺ 叉积点积 < 0（`pW22_c2_iff_det` + 叉积双线性
  + 点积符号搬运）。
-/
import Kepler.Text.LocalFanStepW22C2

set_option maxHeartbeats 1000000

namespace Kepler.Text

open Kepler.Geom Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **C2 ⟺ 绕序叉积不等式**：共同基 `(v, r)` 表示下，
`y ∈ affGt{0, a}{v} ↔ (a × y) · (v × r) < 0`（叉积在 Pi 侧，点积同侧；
`(v × r) · (v × r) > 0` 为独立前提）。 -/
theorem pW24_c2_iff_crossdot {v r a y : V3} {b1 g1 b2 g2 : ℝ}
    (hv0 : v ≠ 0) (hr0 : r ≠ 0) (hnc : ¬ Collinear3 (0 : V3) v r)
    (ha0 : a ≠ 0) (hva : v ≠ a)
    (hy : y = b1 • v + g1 • r) (hg1 : 0 < g1)
    (ha : a = b2 • v + g2 • r) (hg2 : 0 < g2)
    (hpos : 0 < (crossProduct ((v : V3) : Fin 3 → ℝ) ((r : V3) : Fin 3 → ℝ)) ⬝ᵥ
      (crossProduct ((v : V3) : Fin 3 → ℝ) ((r : V3) : Fin 3 → ℝ))) :
    y ∈ affGt ({0, a} : Set V3) {v} ↔
      (crossProduct ((a : V3) : Fin 3 → ℝ) ((y : V3) : Fin 3 → ℝ)) ⬝ᵥ
        (crossProduct ((v : V3) : Fin 3 → ℝ) ((r : V3) : Fin 3 → ℝ)) < 0 := by
  have hcv : ((a : V3) : Fin 3 → ℝ)
      = b2 • ((v : V3) : Fin 3 → ℝ) + g2 • ((r : V3) : Fin 3 → ℝ) := by
    have h := congrArg (fun p : V3 => (p : Fin 3 → ℝ)) ha
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
  have hcy : ((y : V3) : Fin 3 → ℝ)
      = b1 • ((v : V3) : Fin 3 → ℝ) + g1 • ((r : V3) : Fin 3 → ℝ) := by
    have h := congrArg (fun p : V3 => (p : Fin 3 → ℝ)) hy
    simpa only [WithLp.ofLp_add, WithLp.ofLp_smul] using h
  have hrv : crossProduct ((r : V3) : Fin 3 → ℝ) ((v : V3) : Fin 3 → ℝ)
      = -(crossProduct ((v : V3) : Fin 3 → ℝ) ((r : V3) : Fin 3 → ℝ)) :=
    (cross_anticomm _ _).symm
  have hxe : crossProduct
      (b2 • ((v : V3) : Fin 3 → ℝ) + g2 • ((r : V3) : Fin 3 → ℝ))
      (b1 • ((v : V3) : Fin 3 → ℝ) + g1 • ((r : V3) : Fin 3 → ℝ))
      = (b2 * g1 - g2 * b1) •
        crossProduct ((v : V3) : Fin 3 → ℝ) ((r : V3) : Fin 3 → ℝ) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      cross_self, hrv, smul_zero, zero_add, add_zero, smul_neg, smul_smul]
    module
  have hcross : (crossProduct ((a : V3) : Fin 3 → ℝ) ((y : V3) : Fin 3 → ℝ)) ⬝ᵥ
      (crossProduct ((v : V3) : Fin 3 → ℝ) ((r : V3) : Fin 3 → ℝ))
      = (b2 * g1 - g2 * b1) *
        ((crossProduct ((v : V3) : Fin 3 → ℝ) ((r : V3) : Fin 3 → ℝ)) ⬝ᵥ
          (crossProduct ((v : V3) : Fin 3 → ℝ) ((r : V3) : Fin 3 → ℝ))) := by
    rw [hcv, hcy, hxe, smul_dotProduct, smul_eq_mul]
  rw [pW22_c2_iff_det hv0 hr0 hnc ha0 hva hy hg1 ha hg2, hcross]
  constructor <;> intro h <;> nlinarith [hpos]

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pW24_c2_iff_crossdot
