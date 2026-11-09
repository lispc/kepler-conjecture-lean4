/-
Kepler/Text/LocalFanStepW5W6.lean — wave C-W5a-ii-5：径向序的 azim 归约 + 依赖面审计。

本件（判定/归约，非径向序本体）：
* `pW5w6_radial_iff_azim`：径向序目标 `y ∈ affGt{0,a}{v}` **等价于**
  `azim 0 a v y = 0`（`azim_eq_zero_iff_alt`，Geom/AzimLemmas:307，标准三）。
  这把「v 系数 > 0」的锥问题归约为一个 **azim 等式**——与 HOL 2184-2440
  的 AZIM_EQ 链同一目标形。
* DELIVERY 附依赖面审计：`azim_eq_azim_iff` / `_alt` / `sum4_azim_fan` /
  `AZIM_EQ_0_GE_ALT2` / `azim_eq_zero_iff` / `_alt` 全部 **标准三**
  （无 sorry 桩）⇒ 缺口不是账面上的桩，而是 AZIM_EQ 链的装配工作量
  （按硬止损：本波判定后转显式前提 ②，不再纠缠）。
-/
import Kepler.Text.LocalFanStepW5W5

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **径向序的 azim 归约**：`y ∈ affGt{0,a}{v} ↔ azim 0 a v y = 0`
（`azim_eq_zero_iff_alt` 的对称形）。 -/
theorem pW5w6_radial_iff_azim {a v y : V3}
    (hnc1 : ¬ Collinear3 (0 : V3) a v) (hnc2 : ¬ Collinear3 (0 : V3) a y) :
    y ∈ affGt ({0, a} : Set V3) {v} ↔ azim 0 a v y = 0 :=
  (azim_eq_zero_iff_alt (v0 := (0 : V3)) (v1 := a) (w := v) (x := y) hnc1 hnc2).symm

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5w6_radial_iff_azim
#print axioms Kepler.Text.pW5w6_radial_iff_azim
#check @Kepler.Geom.azim_eq_azim_iff
#print axioms Kepler.Geom.azim_eq_azim_iff
#check @Kepler.Geom.azim_eq_azim_iff_alt
#print axioms Kepler.Geom.azim_eq_azim_iff_alt
#check @Kepler.Text.sum4_azim_fan
#print axioms Kepler.Text.sum4_azim_fan
#check @Kepler.Text.AZIM_EQ_0_GE_ALT2
#print axioms Kepler.Text.AZIM_EQ_0_GE_ALT2
#check @Kepler.Geom.azim_eq_zero_iff
#print axioms Kepler.Geom.azim_eq_zero_iff
#check @Kepler.Geom.azim_eq_zero_iff_alt
#print axioms Kepler.Geom.azim_eq_zero_iff_alt
