/-
Kepler/Text/LocalFanStepW5W5.lean — wave C-W5a-ii-4：azim 路线的槽审计 + 每步不等式桥。

工单问题：`MONO_AZIM_AS_BTA_I_p35`（LA35:28123）的 `hstep` 槽
  `∀ i, i+1 < k → azim 0 v0 (ρ 1) (ρ i) ≤ azim 0 v0 (ρ 1) (ρ (i+1))`
能否由 `EGHNAVX` 的 `hmono`（`∀ i j, i<j → j<k → bta i ≤ bta j`）直接供？

**机器结论：能。** 本件交 `pW5w5_azim_step`（`hmono` + `hbta` ⇒ 每步不等式，
与 p35 槽逐字同形），∅ 缺口。

另：**azim 单调性本身不是锥系数符号**——`hprev` 的第二 2_1
（`vv n ∈ affGt{0, vv(n-1)}{v}`，v 系数 > 0）还需要「azim → 锥系数」桥
（见 DELIVERY §3 的判定）。
-/
import Kepler.Text.LocalFanStepW5W4
import Kepler.Text.LocalAuto35

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **每步 azim 不等式桥**：EGHNAVX 的 `hmono` + `hbta` ⇒
`MONO_AZIM_AS_BTA_I_p35` 的 `hstep` 槽（逐字同形）。 -/
theorem pW5w5_azim_step {v0 : V3} {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hmono : ∀ i j, i < j → j < k → bta i ≤ bta j)
    (hbta : ∀ i, azim 0 v0 (vv 1) (vv i) = bta i) :
    ∀ i, i + 1 < k → azim 0 v0 (vv 1) (vv i) ≤ azim 0 v0 (vv 1) (vv (i + 1)) := by
  intro i hi
  rw [hbta i, hbta (i + 1)]
  exact hmono i (i + 1) (by omega) hi

/-- 与 `MONO_AZIM_AS_BTA_I_p35` 槽的逐字对齐探针（ρ := vv 的实例化形）。 -/
theorem pW5w5_azim_step_slot {v0 : V3} {vv : ℕ → V3} {bta : ℕ → ℝ} {k : ℕ}
    (hmono : ∀ i j, i < j → j < k → bta i ≤ bta j)
    (hbta : ∀ i, azim 0 v0 (vv 1) (vv i) = bta i) :
    ∀ i, i + 1 < k →
      azim 0 v0 (vv 1) (vv i) ≤ (fun m => azim 0 v0 (vv 1) (vv m)) (i + 1) :=
  pW5w5_azim_step (vv := vv) hmono hbta

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW5w5_azim_step
#print axioms Kepler.Text.pW5w5_azim_step
#check @Kepler.Text.pW5w5_azim_step_slot
#print axioms Kepler.Text.pW5w5_azim_step_slot
#check @Kepler.Text.MONO_AZIM_AS_BTA_I_p35
#check @Kepler.Text.MONO_AZIM_AS_BTA_I
