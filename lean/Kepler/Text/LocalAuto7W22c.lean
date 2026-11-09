/-
LocalAuto7W22c: W22c — `azimDart` ↔ `azimInFan` 桥（LA2:1616 `azim_dart_azim_in_fan`
的下游重证）+ `f_surr_localization` 的**条件形**（`hcard`/`hsimple` 显式槽）。

## 件

| # | 件 | = HOL / 树内桩 | 状态 |
|---|---|---|---|
| 1 | **`p22c_azimDart_eq_azimInFan`** | `azim_dart_azim_in_fan`（LA2:1616，**第 6 个未证桩**） | 本件下游新名 |
| 2 | `p22c_f_surr_localization_cond` | `f_surr_localization`（RNSYJXM:292） | **条件形**（`hcard`/`hsimple` 槽） |

**件 2 为什么是条件形**（按工单第 5 条预案）：`LVDUCXU`（LA10:1708，std3）已给出 5 合取，
但其 `local_fan` 合取需要 `2 < FF.ncard` 与 `H2.Simple`——对应 HOL
`FULLY_SURROUNDED_IMP_CARD_FACE_GE_3`（依赖 `CARD_SET_OF_EDGE_GT_1_IMP_CARD_FACE_GE_3`）
与 `fully_surrounded_simple_hypermap`，**两件均未移植**，属 W22c-ii 的独立波。
本件把这两条做成显式槽，`f_surr_localization_convex_local`（W22d）可先用条件形接上。

LA2:1616 的**原位桩保留**（LA2 不能 import 下游）——DIFFERS：本件为下游新名，陈述逐字对齐。
-/
import Kepler.Text.LocalAuto7W22b
import Kepler.Text.LocalAuto10

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

/-! ## 1. LA2:1616 的下游重证：`azimDart = azimInFan_p3` -/

/-- **HOL `azim_dart_azim_in_fan`**（树内 LA2:1616 是未证桩）：`{x.1,x.2} ∈ E` 时
`azimDart V E x = azimInFan_p3 x E`。

桥：`EE_p3 x.1 E = setOfEdge x.1 V E`（FAN 的 `⋃₀E ⊆ V`）+ `AZIM_CYCLE_EQ_SIGMA_FAN_ALT`
（LA2:1212，std3）+ `edge_ne_of_fan`。 -/
theorem p22c_azimDart_eq_azimInFan {V : Set V3} {E : Set (Set V3)} (hfan : FAN 0 V E)
    {x : V3 × V3} (hx : {x.1, x.2} ∈ E) :
    azimDart V E x = azimInFan_p3 x E := by
  have hne : x.1 ≠ x.2 := edge_ne_of_fan hfan hx
  -- `EE_p3 = setOfEdge`（FAN 下：边端点必在 V）
  have hEE : EE_p3 x.1 E = setOfEdge x.1 V E := by
    ext w
    simp only [EE_p3, setOfEdge, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h, hfan.1 (Set.mem_sUnion_of_mem
        (Set.mem_insert_of_mem x.1 (Set.mem_singleton w)) h)⟩, fun h => h.1⟩
  have hmem : x.2 ∈ setOfEdge x.1 V E :=
    ⟨hx, hfan.1 (Set.mem_sUnion_of_mem
      (Set.mem_insert_of_mem x.1 (Set.mem_singleton x.2)) hx)⟩
  unfold Fan.azimDart Fan.azimFan azimInFan_p3
  rw [if_neg hne, hEE]
  by_cases hc : 1 < (setOfEdge x.1 V E).ncard
  · rw [if_pos hc, if_pos hc]
    rw [show azimCycle_p3 (setOfEdge x.1 V E) 0 x.1 x.2 = sigmaFan 0 V E x.1 x.2 from
      AZIM_CYCLE_EQ_SIGMA_FAN_ALT hfan hmem]
  · rw [if_neg hc, if_neg hc]

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22c_azimDart_eq_azimInFan

end Kepler.Text
