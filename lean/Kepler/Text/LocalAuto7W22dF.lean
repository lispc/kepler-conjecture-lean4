/-
LocalAuto7W22dF: W22d wave 3 — `localization_simple_hypermap` 的**展开/桥**（第 1 件）。

## HOL 原形（`local/RNSYJXM-compiled.hl:182-258`，~76 行 dense）

```
f ∈ face_set (hypermap_of_fan (V,E)) ∧ 2 ≤ CARD f ∧ simple_hypermap (hypermap_of_fan (V,E))
  ==> simple_hypermap (hypermap_of_fan (v_prime V f, e_prime E f))
```

## 本件（展开；主体交班见 DELIVERY §P2）

`p22d_simple_expand`：`Simple` 的轨道形（`Hypermap.node`/`Hypermap.face` 定义展开）。
第二件（`IsHypOn_p10` 形，darts 换成 `dartsOfHyp_p3`）剩 1 处 `rw` 机械问题，
主体（`nnOfHyp_p3`/`ffOfHyp_p3` 的交集 = 单点）需切片扇轨道结构，交下一波。

## DIFFERS（绕法，按编排者确认）

* HOL `dartH` ⇒ 本树 `p22c2_face_subset_darts`（W22c-ii，已落）；
* HOL `hypermap_HYP_elim` ⇒ `IsHypOn_p10` 的四映射等式（已是 Lean 侧的同一内容）；
* **不新造同义件**。

W22dA–D / W22c* / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22dD

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- **`Simple` 的轨道形**：`H.Simple ↔ ∀ x ∈ H.darts, orbitMap H.nodeMap x ∩ orbitMap H.faceMap x = {x}`
（`Hypermap.node`/`Hypermap.face` 的定义展开）。 -/
theorem p22d_simple_expand {α : Type*} [DecidableEq α] (H : Hypermap α) :
    H.Simple ↔ ∀ x ∈ H.darts,
      orbitMap H.nodeMap x ∩ orbitMap H.faceMap x = ({x} : Set α) := by
  simp only [Hypermap.Simple, Hypermap.node, Hypermap.face]

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22d_simple_expand

end Kepler.Text
