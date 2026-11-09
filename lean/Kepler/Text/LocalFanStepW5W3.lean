/-
Kepler/Text/LocalFanStepW5W3.lean — wave C-W5a-ii-2：候选 2 判定件。

判定问题（工单）：`FAN_IN_AFF_GE_IMP_EQ`（LA5:1660）能否排除「v 系数 ≤ 0」
边界，把 2_1 形 `vv n ∈ affGt{0,v}{vv(n-1)}` 升级为 1_2 形
`vv n ∈ affGt{0}{v, vv(n-1)}`？

机器结论（本件）：
* **1_2 = 2_1 ∩ 另一 2_1**（`aff_gt_inter_aff_gt`）：`pW5w3_one_two_iff`。
  因此 `hprev` 的升级 = 补第二个 2_1 合取 `vv n ∈ affGt{0, vv(n-1)}{v}`
  （v 系数正）。
* **`FAN_IN_AFF_GE_IMP_EQ` 的形不匹配**：它的结论是「V 中的点 = 边的端点」
  （前件：点在 `affGe{0}{a,b}`、`{a,b} ∈ E`），而「v 系数 ≤ 0」是**半空间
  符号条件**，不是「点落在某条 fan 边的闭锥内」。判定：**候选 2 不可行**
  （见 DELIVERY §2 的逐条分析）。
* 两步走换 tip 也不成立：第二个 2_1 需要 `v ∈ affGt{0, vv(n-1)}{c}`，
  而 `v` 在 `H_ι` 半平面的**边界射线** 0→v 上（非开半平面内），
  换 tip 无法给出该前件。

本件只交判定用的等价件（可独立落库）；`hprev` 走镜像全套（候选 1）。
-/
import Kepler.Text.LocalFanStepW5W2

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **1_2 = 2_1 ∩ 另一 2_1**：`vv n ∈ affGt{0}{v,a}` ⟺
`vv n ∈ affGt{0,v}{a} ∧ vv n ∈ affGt{0,a}{v}`（`x,b,c` 非共线时）。 -/
theorem pW5w3_one_two_iff {x v a y : V3} (hnc : ¬ Collinear3 x v a) :
    y ∈ affGt ({x} : Set V3) {v, a}
      ↔ y ∈ affGt ({x, v} : Set V3) {a} ∧ y ∈ affGt ({x, a} : Set V3) {v} := by
  have hnc0 : ¬ Collinear ℝ ({x, v, a} : Set V3) := hnc
  rw [aff_gt_inter_aff_gt (x := x) (v := v) (w := a) hnc0]
  exact Iff.rfl

/-- **判定配套**：`affGt{0}{v,a}` 的 2_1 形说明（供 hprev 的镜像路线组装时引用）。 -/
theorem pW5w3_two_one_of_one_two {x v a y : V3} (hnc : ¬ Collinear3 x v a) :
    y ∈ affGt ({x} : Set V3) {v, a} → y ∈ affGt ({x, v} : Set V3) {a} := by
  intro h
  exact ((pW5w3_one_two_iff hnc).mp h).1

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5w3_one_two_iff
#print axioms Kepler.Text.pW5w3_one_two_iff
#check @Kepler.Text.pW5w3_two_one_of_one_two
#print axioms Kepler.Text.pW5w3_two_one_of_one_two
