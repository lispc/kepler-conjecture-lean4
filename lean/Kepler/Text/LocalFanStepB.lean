/-
Kepler/Text/LocalFanStepB.lean — wave C0：stepB 的 p2→LA1 桥 + 接口壳。

## 范围（C0，≤220 行）

本件只做 stepB（HOL `NKEZBFC.hl:1749-2616`）的**基础设施与接口**，**不含**
轨道/方位（`vv`/`bta`）论证与 `aff_ge` 并集分解（留给 W1–W7）。三件：

1. `pC_ConvexLocalFan_of_p2`：`convexLocalFan_p2 → ConvexLocalFan`（p2→LA1 桥）。
   EGHNAVX（LA14:6965）的假设是 LA1 形 `ConvexLocalFan`，树内只有反方向桥
   `p13w_convexLocalFan_p2_of_clf`（LocalFanPerimeterGeneric.lean:55）；本件是
   其逆向，组件全部来自 AzimBridge/LA5 的 std3 公开件。
2. `pC_sol_nonneg_of_angle_ge_pi`：stepB 的顶层壳——若 `∀ v∈V, π ≤ interiorAngle1`，
   则 `0 ≤ solLocal_p9`（`SOL_LOFA_EQ_SUM_INANGLE_p9` + 逐项非负）。
3. `pC_stepB_of_angle_bound`：把 LA9 `p9_main_induction` 的 `stepB` 槽（LA9:3164-3167）
   化归为唯一的 `angle_bound` 假设。W1–W7 只需在 `angle_bound` 内部推进；W7 把它填实
   即得 `pC_stepB`。

## import 闭包

只 import `Kepler.Text.LocalAuto14`（它传递提供 LA9/LA6/LA35/LA37/LA5/AzimBridge；
EGHNAVX、SOL_LOFA、p2/p3/LA1 桥组件全部可用）。已机器验证：单独 import LA14 无
private 名冲突（`logs/import_probe.log`，RC=0）。本件**不直接 import LocalAuto7**。

## 与 stepB 车道的接口

W1–W7 在新文件（或本文件续写）中证明
`angle_bound : ∀ V E FF, convexLocalFan_p2 V E FF → generic_p2 V E → ¬chord →
  ∀ v∈V, π ≤ interiorAngle1_p2 0 FF v`，
然后 `pC_stepB := pC_stepB_of_angle_bound angle_bound`，其类型逐字等于 LA9 的 `stepB` 槽。
-/
import Kepler.Text.LocalAuto14

set_option maxHeartbeats 2000000

namespace Kepler.Text

open Kepler.Geom Kepler.Text.Fan Set Classical

variable {V : Set V3} {E : Set (Set V3)} {FF : Set (V3 × V3)}

/-! ## C0.1 p2 → LA1 `ConvexLocalFan` 桥 -/

/-- `convexLocalFan_p2 → ConvexLocalFan`：p2→p3（rfl 桥）→ LA1（`LocalFan.of_localFan_p3`，
无孤立顶点由 `LOFA_CARD_EE_V_1` 给出）+ `azimInFan`/`wedgeInFanGe` 的 p1↔p3 桥。 -/
theorem pC_ConvexLocalFan_of_p2 (h : convexLocalFan_p2 V E FF) :
    ConvexLocalFan V E FF := by
  obtain ⟨hlf2, hcvx2⟩ := h
  have hlf3 : localFan_p3 V E FF := localFan_p3.of_localFan_p2 hlf2
  have hedge : ∀ v ∈ V, ∃ w, {v, w} ∈ E := by
    intro v hv
    have h2 : (EE_p2 v E).ncard = 2 := LOFA_CARD_EE_V_1 hlf2 hv
    rcases Set.eq_empty_or_nonempty (EE_p2 v E) with h0 | hne
    · rw [h0, Set.ncard_empty] at h2
      omega
    · obtain ⟨w, hw⟩ := hne
      exact ⟨w, hw⟩
  have hno : dartsOfHyp_p3 E V = dart1OfFan V E := hno_of_no_isolated hedge
  have hlf1 : LocalFan V E FF := LocalFan.of_localFan_p3 hlf3 hno
  obtain ⟨hfan, -, -, -, -, hsub, -⟩ := localFan_data hlf1
  refine ⟨hlf1, ?_⟩
  intro x hx
  have hd : x ∈ dart1OfFan V E := hsub hx
  refine ⟨?_, ?_⟩
  · have h1 : azimInFan x E = azimInFan_p3 x E := azimInFan_eq_azimInFan_p3 hfan hd
    have h2 : azimInFan_p3 x E = azimInFan_p2 x E := rfl
    rw [h1, h2]
    exact (hcvx2 x hx).1
  · have h1 : wedgeInFanGe x E = wedgeInFanGe_p3 x E :=
      wedgeInFanGe_eq_wedgeInFanGe_p3 hfan hd
    have h2 : wedgeInFanGe_p3 x E = wedgeInFanGe_p2 x E := rfl
    rw [h1, h2]
    exact (hcvx2 x hx).2

/-! ## C0.2 顶层壳：全内角 ≥ π ⇒ sol ≥ 0 -/

/-- stepB 的顶层归约（HOL NKEZBFC.hl:1749-1767）：由 `SOL_LOFA_EQ_SUM_INANGLE`
把 `solLocal` 化为 `2π + Σ_V(interior − π)`；逐项非负即得结论。 -/
theorem pC_sol_nonneg_of_angle_ge_pi (hcl : convexLocalFan_p2 V E FF)
    (h : ∀ v ∈ V, Real.pi ≤ interiorAngle1_p2 0 FF v) :
    0 ≤ solLocal_p9 E FF := by
  rw [SOL_LOFA_EQ_SUM_INANGLE_p9 hcl]
  have hsum : 0 ≤ setSum V (fun v => interiorAngle1_p2 0 FF v - Real.pi) := by
    unfold setSum
    by_cases hV : V.Finite
    · rw [dif_pos hV]
      exact Finset.sum_nonneg fun v hv =>
        sub_nonneg.mpr (h v ((Set.Finite.mem_toFinset hV).mp hv))
    · rw [dif_neg hV]
  linarith [Real.pi_pos]

/-! ## C0.3 stepB 槽：化归到 angle_bound -/

/-- LA9 `p9_main_induction` 的 `stepB` 槽（LA9:3164-3167）的化归形：给定
`angle_bound`，本件即 LA9 `stepB` 的完整类型。W1–W7 只需证 `angle_bound`。 -/
theorem pC_stepB_of_angle_bound
    (angle_bound : ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
      convexLocalFan_p2 V E FF → generic_p2 V E →
      (¬ ∃ v w : V3, v ∈ V ∧ w ∈ V ∧
        ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) →
      ∀ v ∈ V, Real.pi ≤ interiorAngle1_p2 0 FF v) :
    ∀ (V : Set V3) (E : Set (Set V3)) (FF : Set (V3 × V3)),
      convexLocalFan_p2 V E FF → generic_p2 V E →
      (¬ ∃ v w : V3, v ∈ V ∧ w ∈ V ∧
        ∀ e ∈ FF, affGt ({0} : Set V3) {v, w} ⊆ wedgeInFanGt_p2 e E) →
      0 ≤ solLocal_p9 E FF := by
  intro V E FF hcl hg hnc
  exact pC_sol_nonneg_of_angle_ge_pi hcl (angle_bound V E FF hcl hg hnc)

end Kepler.Text

/-! ## 探针 -/
#print axioms Kepler.Text.pC_ConvexLocalFan_of_p2
#print axioms Kepler.Text.pC_sol_nonneg_of_angle_ge_pi
#print axioms Kepler.Text.pC_stepB_of_angle_bound
