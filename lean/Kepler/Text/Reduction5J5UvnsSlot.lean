/-
  Kepler.Text.Reduction5J5UvnsSlot — `k3UvnsOfSlots`：hUvns 槽的构造器（U 段落库前接线）

  ┌─ 目标 ─────────────────────────────────────────────────────────
  │ 把 `k3UvnsSlot`（K3CONJ #18）的**四件已知供料**接好，只留 U 段
  │ 主定理一个显式槽 `hU`；当 U 段交付无条件形（= `finalAssumptionUvnsCombinedOfSlots`
  │ 的两槽 hVs'/hUvns 由主定理一并给出）后，一行
  │   `k3UvnsOfSlots <U 定理> : k3UvnsSlot`
  │ 即消槽。
  └────────────────────────────────────────────────────────────────

  ┌─ 四件供料（按 `k3UvnsSlot` 前提顺序）──────────────────────────
  │ hnNil   ← `k3Sx3SlotInstance`（Reduction5J5SxC，ac8c6f7b）
  │ hnFy    ← `Reduction4.finalAssumptionNotMemSndXFy`（2c9d708b）
  │ hnZx    ← `Reduction4.finalAssumptionNotMemSndXZx`（2c9d708b）
  │ hIdxSnd ← `indexSndX`（Reduction5J5K4IndexSndX，9006597b）
  └────────────────────────────────────────────────────────────────

  咬合说明：
  - `k3UvnsSlot` 的 hnNil 前提与 `k3Sx3Slot` 的结论逐字一致（同一
    `listOfDarts (quotientList L N)` 形），`k3Sx3SlotInstance` 直投；
  - hnFy/hnZx 需要 `AqiunppSlot`，本件由 `TameSpine.aqiunpp`（定理）内部构造；
  - 主槽 `k3UvnsMainSlot` = `finalAssumptionUvnsCombinedOfSlots` 的十前提形、
    两分支（hVs'/hUvns）由主定理一并给出。若 U 段以两条分支定理交付，
    接线为 `k3UvnsOfSlots (fun L hL hgn hres hm hnf hk hnNil hnFy hnZx hIdxSnd =>
      finalAssumptionUvnsCombinedOfSlots L hL hgn hres hm hnf hk hnNil hnFy hnZx hIdxSnd
        <hVs' 定理> <hUvns 定理>)`（无需新件）。

  纪律：零公理、零占位证明、零反射式判定；不改既有陈述/定义；主仓 tracked 零改动。
-/
import Kepler.Text.Reduction5J5UvnsCombined
import Kepler.Text.Reduction5J5SxC
import Kepler.Text.Reduction4K4C0R2d
import Kepler.Text.Reduction5J5K4IndexSndX
import Kepler.Text.TameSpine.JcajyduRed2Tav2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph between)
open Kepler.Assembly (GoodList nextEl prevEl findFaceDarts listOfDarts listPairs)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- **U 段主定理的公开类型**：`finalAssumptionUvnsCombinedOfSlots` 的十前提形，
两分支（`final_assumption_uvns_vs'` / `final_assumption_uvns`）由主定理一并给出。 -/
def k3UvnsMainSlot : Prop :=
  ∀ (L : fgraph ℕ) (hL : GoodList L) (hgn : GoodListNodesTl L hL)
    (hres : (hypermapOfList L hL).IsRestricted)
    {N : List (List Dart)} {r : List Dart} {x : Dart} {k : ℕ}
    (hm : markedList L hL N r x) (hnf : ¬ finalList L r)
    (hk : transformCount L N r x = k)
    (hnNil : ∀ i : ℕ, i < k →
      between (findFaceDarts L x) (ytrans L N r x i) (ztrans L N r x i) = [] →
        ((ytrans L N r x i).1, (ztrans L N r x i).1) ∉
          listOfDarts (quotientList L N))
    (hnFy : ∀ i : ℕ, i < k →
      1 < (ftrans L N r x i ::
        ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1).length →
        x.2 ∉ ifbetwn (core L r) (ftrans L N r x i) (ytrans L N r x i).1)
    (hnZx : x.2 ∉ ifbetwn (core L r) (ztrans L N r x (k - 1)).1 x.1)
    (hIdxSnd : ∀ i : ℕ, i < k →
      indexf x.2 (ytrans L N r x i).1 (core L r) <
        indexf x.2 (ztrans L N r x i).1 (core L r)),
    ∀ v : ℕ, (prevEl (core L r) v, v) = x →
      (let uvns := Kepler.Text.Reduction3.coreTripleV4 L N r x
       let vs := Kepler.Text.Reduction3.destTripleFull (core L r) v uvns
       let vs' := vs.filterMap id
       (∀ i : ℕ, i + 1 < vs'.length →
          indexf v (vs'.getD i 0) (core L r) < indexf v (vs'.getD (i + 1) 0) (core L r)) ∧
        (∀ i : ℕ,
          let d : Dart := ((vs.getD i none).getD 0, (vs.getD (i + 1) none).getD 0);
          ((vs.getD i none).isSome ∧ (vs.getD (i + 1) none).isSome ∧
            i + 1 < vs.length ∧ d ∈ listOfDarts (quotientList L N)) →
          d ∈ listPairs (core L r)))

/-- **`k3UvnsSlot` 的四件供料接线**：`hU` = U 段主定理，其余四前提由在库件填。 -/
theorem k3UvnsOfSlots (hU : k3UvnsMainSlot) : k3UvnsSlot := by
  intro L hL hgn hres N r x k hm hnf hk v hv
  have haq : Kepler.Text.Reduction4Idx.AqiunppSlot L hL :=
    fun hgn' N' r' x' hm' j => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' j
  exact hU L hL hgn hres hm hnf hk
    (fun i hi hbet => k3Sx3SlotInstance L hL hgn hres hm hnf hk i hi hbet)
    (fun i hi hlt =>
      Kepler.Text.Reduction4.finalAssumptionNotMemSndXFy L hL hgn hres haq hm hnf hk i
        ⟨hi, hlt⟩)
    (Kepler.Text.Reduction4.finalAssumptionNotMemSndXZx L hL hgn hres haq hm hnf hk)
    (indexSndX L hL hgn hres hm hnf hk)
    v hv

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零占位依赖项） -/
#print axioms Kepler.Text.Reduction5.k3UvnsOfSlots

/- 接口探针 ①：`k3UvnsOfSlots` 的形。 -/
#check fun (hU : Kepler.Text.Reduction5.k3UvnsMainSlot) =>
  Kepler.Text.Reduction5.k3UvnsOfSlots hU

/- 接口探针 ②：K3 引理两槽（hSx3/hUvns）全消，只剩 hF8。 -/
#check fun (haq : ∀ (L : Kepler.Graphs.fgraph ℕ) (hL : Kepler.Assembly.GoodList L),
      Kepler.Text.Reduction4Idx.AqiunppSlot L hL)
    (hF8 : Kepler.Text.Reduction5.k3Indexf8Slot)
    (hU : Kepler.Text.Reduction5.k3UvnsMainSlot) =>
  Kepler.Text.Reduction5.reductionK3 haq
    (Kepler.Text.Reduction5.reductionK3ConclOfSlots hF8
      Kepler.Text.Reduction5.k3Sx3SlotInstance
      (Kepler.Text.Reduction5.k3UvnsOfSlots hU))
