/-
LocalAuto7W22ciib: W22c-ii-b — `f_surr_localization` 的**条件形**（5 合取）。

`LVDUCXU`（`LocalAuto10:1708`，std3）已给全部 5 条（p3 词汇 + `azimInFan`）；本波按 §7 止损只交面⊆darts 的边成员性件；条件形本体剩余步骤见 DELIVERY §M2。

## 槽

* `hfs : FullySurrounded V E` —— HOL RNSYJXM 整节假设；用于排除 `selfPairs_p3`（孤立点自环）。
* `hcard : 2 < FF.ncard` / `hsimple : H2.Simple` —— HOL `FULLY_SURROUNDED_IMP_CARD_FACE_GE_3` /
  `fully_surrounded_simple_hypermap`（**未移植**，W22c-iii 的 a/b）。
* `hno` —— `LocalFan.of_localFan_p3` 的 `dartsOfHyp_p3 = dart1OfFan` 槽（切片扇无孤立点，
  需 `FullySurrounded (vPrime_p3 V FF) (ePrime_p3 E FF)` 或直接给等式）。

W22c / W22c-ii / W22b / W22a / W21 / LA2 / LA9 零改动。
-/
import Kepler.Text.LocalAuto7W22cii

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical
open Kepler.Text.TameLp

/-! ## 1. `dartsOfHyp_p3` 的边成员性（`FullySurrounded` 下无自环） -/

/-- **`FullySurrounded V E → dartsOfHyp_p3 E V ⊆ {d | {d.1,d.2} ∈ E}`**：
`dartsOfHyp_p3 = ordPairs_p3 ∪ selfPairs_p3`，前者定义即边，后者在 `FullySurrounded`
（无孤立点，`p22a_fs_has_edge`）下为空。 -/
theorem p22c2_dartsOfHyp_subset {V : Set V3} {E : Set (Set V3)} (hfs : FullySurrounded V E) :
    dartsOfHyp_p3 E V ⊆ {d : V3 × V3 | {d.1, d.2} ∈ E} := by
  intro d hd
  unfold dartsOfHyp_p3 at hd
  rcases hd with hord | hself
  · exact hord
  · -- 自环支：`EE_p3 d.1 E = ∅`，而 `FullySurrounded` 给 `d.1` 有邻居
    obtain ⟨w, hw⟩ := p22a_fs_has_edge hfs d.1 hself.2.1
    have hmem : w ∈ EE_p3 d.1 E := hw
    rw [hself.2.2] at hmem
    exact absurd hmem (Set.notMem_empty w)

/-! ## `#print axioms` 探针（落库闸直接读编译输出） -/

#print axioms Kepler.Text.p22c2_dartsOfHyp_subset

end Kepler.Text
