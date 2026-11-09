/-
Kepler/Text/LocalFanStepBW4b.lean — wave C-W4b（B 支 u 侧，续）：dart 级边成员。

HOL 锚：`NKEZBFC.hl:2242-2270`（u 侧 dart 级包含的边成员片段）：
对每个轨道点 `vv n`，`vv n ∈ EE (ρ (vv n)) E`（即 dart `(ρ(vv n), vv n)` 的
端点边集含 `vv n`），由 `LOFA_IMP_EE_TWO_ELMS` + `AZIM_CYCLE_TWO_POINT_SET`
直接给出。

**W4b-i（`hstep` 推导，HOL 2184-2242）尚未交付**（本波止损于此，见 DELIVERY
§4 的路线与卡点：`decomposition_planar_by_angle_fan` 第一析取即 `hstep`，
第二析取需用 telescope 的 union 恒等式排除；decode 未完成，不硬凑）。
-/
import Kepler.Text.LocalFanStepBW4

set_option maxHeartbeats 1200000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

open scoped Matrix

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-- **u 侧 dart 的边成员**（HOL:2242-2270 片段）：轨道点 `vv n` 在
`EE (ρ(vv n)) E` 中。 -/
theorem pW4b_iter_ee_mem (h : localFan_p2 V E FF) {v : V3} (hv : v ∈ V)
    {vv : ℕ → V3} (hiter : ∀ n, (rhoNode1_p2 FF)^[n] v = vv n) (n : ℕ) :
    vv n ∈ EE_p2 (rhoNode1_p2 FF (vv n)) E := by
  have hVV : vv n ∈ V := by
    rw [← hiter n]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V h hv n
  have hρeq : rhoNode1_p2 FF (vv n) = vv (n + 1) := by
    rw [← hiter n, ← hiter (n + 1)]
    rw [show n + 1 = Nat.succ n from rfl, Function.iterate_succ_apply']
  have hρV : rhoNode1_p2 FF (vv n) ∈ V := by
    rw [hρeq, ← hiter (n + 1)]
    exact LOCAL_FAN_ITER_RHO_NODE_IN_V h hv (n + 1)
  have hEE : EE_p2 (rhoNode1_p2 FF (vv n)) E
      = ({rhoNode1_p2 FF (rhoNode1_p2 FF (vv n)), vv n} : Set V3) :=
    LOFA_IMP_EE_TWO_ELMS h hVV rfl
  rw [hEE]
  exact Or.inr rfl

end Kepler.Text

/-! ## 探针 -/
#check @Kepler.Text.pW4b_iter_ee_mem
#print axioms Kepler.Text.pW4b_iter_ee_mem
