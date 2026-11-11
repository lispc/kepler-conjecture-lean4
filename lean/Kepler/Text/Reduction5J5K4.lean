/-
  Kepler.Text.Reduction5J5K4 — J4 D1 打包：K3 INDEX 8 槽实例 + `reductionK4OfSlots`。

  ┌─ 件表 ─────────────────────────────────────────────────────────
  │ `k3Indexf8`          : `k3Indexf8Slot`（SUC 形 `i+1 < k`，B3' `indexf8FinalLemmas`
  │                        于 `i := i+1` 一行实例；槽内 `hgn/hres/hm/hnf/hk` 逐字对齐）
  │ `reductionK4OfSlots` : K4 引理槽（`hK4` 参数按 ml15 判词零消费、直接丢弃）
  │                        ⇒ `assumptionSetK10Full`；haq 由 `TameSpine.aqiunpp` 现拼
  │ `jcajyduOfK4Slots`   : 同上 + `jcajyduOfK4`，封 J5-9 最终条件形
  └────────────────────────────────────────────────────────────────

  **纪律**：零公理、零占位证明、零反射式判定；不改已落库陈述/定义；主仓 tracked 零写入。
-/
import Kepler.Text.Reduction5J5K3Indexf678
import Kepler.Text.Reduction5J5K4Lemma
import Kepler.Text.Reduction5K5
import Kepler.Text.Reduction5J5HfSupply
import Kepler.Text.TameSpine.JcajyduRed2Tav2
import Kepler.Text.Reduction3DefsAssumptionInst

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (GoodListNodesTl hypermapOfList)
open Kepler.Text.ChainLists (markedList)

/-- **槽 ①（INDEX 8）实例**：`indexf8FinalLemmas` 于 `i := i+1`。
槽形 `i+1 < k` 与 B3' 的 `0 < i ∧ i < k` 只差 `omega`；`PRE (i+1) ↦ i` 定义级。 -/
theorem k3Indexf8 : k3Indexf8Slot :=
  fun L hL hgn hres N r x k hm _hnf hk i hi =>
    indexf8FinalLemmas L hL hgn hres hm hk (i + 1) ⟨by omega, hi⟩

/-- **D1：K4 引理槽 ⇒ K10**。`hK4` 按 ml15 判词**零消费**（`_` 丢弃）；
K3 供给由 `k3Indexf8` + SND_X c 槽 `hSx3` + UVNS 槽 `hUvns` 组成，
`reductionK3` 的 `haq` 按 `TameSpine.aqiunpp` 逐状态现拼。 -/
theorem reductionK4OfSlots
    (hSx3 : Kepler.Text.Reduction5.k3Sx3Slot)
    (hUvns : Kepler.Text.Reduction5.k3UvnsSlot) :
    (∀ (L : fgraph ℕ) (N : List (List Dart)) (r : List Dart) (x : Dart) (k : ℕ),
      reductionK4Asm Kepler.Text.Reduction3.GoodNodesSlot
        Kepler.Text.Reduction3.IsRestrictedSlot Kepler.Text.Reduction3.MarkedSlot
        L N r x k → reductionK4Concl L N r x k) →
      Kepler.Text.Reduction3.assumptionSetK10Full :=
  fun _ => Kepler.Text.Reduction5.reductionK3
    (fun L hL hgn' N' r' x' hm' i => Kepler.Text.TameSpine.aqiunpp L hL hgn' N' r' x' hm' i)
    (Kepler.Text.Reduction5.reductionK3ConclOfSlots k3Indexf8 hSx3 hUvns)

/-- **J5-9 最终条件形封口**：上面 `reductionK4OfSlots` 代入 `jcajyduOfK4`
（只吃 hK4 的装配件）。 -/
theorem jcajyduOfK4Slots
    (hSx3 : Kepler.Text.Reduction5.k3Sx3Slot)
    (hUvns : Kepler.Text.Reduction5.k3UvnsSlot)
    {α : Type*} [DecidableEq α] (H : Kepler.Text.Hypermap α) (hres : H.IsRestricted) :
    ∃ g : Kepler.Graphs.Graph, Kepler.Graphs.PlaneGraphs g ∧
      Kepler.Text.TameCorrList.GoodGraphV4 g ∧
      ∃ H' : Kepler.Text.Hypermap (ℕ × ℕ),
        Kepler.Text.TameLp.IsHypermapOfListTl g.fgraph H' ∧ H.Iso H' :=
  Kepler.Text.Reduction5.jcajyduOfK4 (reductionK4OfSlots hSx3 hUvns) H hres

end Kepler.Text.Reduction5

/-! 探针（编译即执行；目标 ⊆ 标准三，零 sorryAx） -/
#print axioms Kepler.Text.Reduction5.k3Indexf8
#print axioms Kepler.Text.Reduction5.reductionK4OfSlots
#print axioms Kepler.Text.Reduction5.jcajyduOfK4Slots
