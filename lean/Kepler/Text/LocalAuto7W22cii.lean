/-
LocalAuto7W22cii: W22c-ii（第 1 件）— 面 ⊆ darts（`in_face_imp_in_dart` 的 Lean 形）。

本波按 §7 止损只交件 d；`p22c2_f_surr_localization_cond`（5 合取条件形）的**精确剩余步骤**
已写入 DELIVERY §L2（含 `dartsOfHyp_p3` 的边成员性提取与 `hno` 槽来源），交下一波。

## 件

`p22c2_face_subset_darts`：`x ∈ H.darts → H.face x ⊆ ↑H.darts`
（`orbitMap_subset_of_permutesOn` + `Hypermap.faceMap_permutes`）。

W22c / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22c

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-- **`H.face x ⊆ ↑H.darts`**（HOL `in_face_imp_in_dart` 的 Lean 形）：
面是 `faceMap` 的轨道，而 `faceMap` 在 `darts` 上 `PermutesOn` ⇒ 轨道 ⊆ darts。 -/
theorem p22c2_face_subset_darts {α : Type*} [DecidableEq α] (H : Hypermap α)
    {x : α} (hx : x ∈ H.darts) :
    H.face x ⊆ ↑H.darts :=
  orbitMap_subset_of_permutesOn H.faceMap_permutes hx

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22c2_face_subset_darts

end Kepler.Text
