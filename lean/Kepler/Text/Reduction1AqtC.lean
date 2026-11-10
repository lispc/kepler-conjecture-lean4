/-
  Kepler.Text.Reduction1AqtC — hEpc 接线（`existsPathComplementSlot`，TameList63）
  + 主定理「单槽」收口形：`auqtzyzConclOf5`（⑤ 槽）与 `auqtzyzConclOfHid`
  （node 平方槽）。

  背景：编排者知会 `EXISTS_PATH_COMPLEMENT` 早已在树（`TameList63`，12 合取全闭）
  + 槽形包装 `existsPathComplementSlot`（`1b5c4266`）；本文件把该包装接进
  AqtA/AqtB 的收口形，把 `hEpc` 槽彻底消掉。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.TameSpine.TameList63
import Kepler.Text.Reduction1AqtB

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction1

open Kepler.Text (Hypermap Loop)

/-- **hEpc 供料接线**：`ExistsPathComplementSlot` 由 TameList63 的
`existsPathComplementSlot` 一条实例化即得（12 合取逐槽同形）。 -/
theorem existsPathComplementSlotOfTame63 {α : Type*} [DecidableEq α]
    (H : Hypermap α) (x : α) : ExistsPathComplementSlot H x :=
  Kepler.Text.TameSpine.existsPathComplementSlot H x

/-- **AUQTZYZ 主定理收口形（⑤ 单槽版）**：`hEpc` 已由
`existsPathComplementSlot` 接线；剩 ⑤ 槽（`hasOrders nodeMap 2`）。
剩余：node 平方（每商节点恰二原子）一件。 -/
theorem auqtzyzConclOf5 {α : Type*} [DecidableEq α]
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (h5 : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      Kepler.Text.hasOrders_p3 (((H.quotientHypermap hnf).nodeMap : Set α → Set α)) 2) :
    AuqtzyzConcl H x L1 :=
  auqtzyzConclOfEpcAnd5 existsPathComplementSlotOfTame63 H x L1 h5

/-- **AUQTZYZ 主定理收口形（node 平方单槽版）**：`hEpc` 已接线；剩
`∀ a ∈ darts, (nQ²) a = a` 一件（⑤ 的非恒等半已由 AqtB `nodeQuotient_ne` 内置）。 -/
theorem auqtzyzConclOfHid {α : Type*} [DecidableEq α]
    (H : Hypermap α) (x : α) (L1 : Loop α)
    (hhid : ∀ (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      ∀ a ∈ (H.quotientHypermap hnf).darts,
        ((H.quotientHypermap hnf).nodeMap ^ 2) a = a) :
    AuqtzyzConcl H x L1 :=
  auqtzyzConclOfEpcAndHid existsPathComplementSlotOfTame63 H x L1 hhid

/-- **AUQTZYZ 全称闭包的条件形（逐宇宙）**：固定 `α`，`∀ H x L1, AuqtzyzConcl`
由 node 平方槽一条给出（`Auqtzyz` 的宇宙多态闭包取各宇宙实例）。 -/
theorem auqtzyzOfHid {α : Type*} [DecidableEq α]
    (hhid : ∀ (H : Hypermap α) (x : α) (L : Loop α),
      ∀ hnf : H.IsNormalFamily ({H.loopOfFace x, L} : Set (Loop α)),
      ∀ a ∈ (H.quotientHypermap hnf).darts,
        ((H.quotientHypermap hnf).nodeMap ^ 2) a = a) :
    ∀ (H : Hypermap α) (x : α) (L1 : Loop α), AuqtzyzConcl H x L1 :=
  fun H x L1 => auqtzyzConclOfHid H x L1 (hhid H x)

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.existsPathComplementSlotOfTame63
#print axioms Kepler.Text.Reduction1.auqtzyzConclOf5
#print axioms Kepler.Text.Reduction1.auqtzyzConclOfHid
#print axioms Kepler.Text.Reduction1.auqtzyzOfHid
