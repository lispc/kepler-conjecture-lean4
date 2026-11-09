/- Reduction3MarkRtrans — reduction3.hl:2611-2628 `marked_list_mark_rtrans`
   的 Lean 移植（首个真实塔顶消费者）：ta 前提 = `transformAssumptionSpine_top`。0 禁词。 -/
import Kepler.Text.TameSpine.JcajyduTowerConsumers
import Kepler.Text.TameSpine.TameList72

set_option autoImplicit false
set_option linter.unusedVariables false
open Kepler.Graphs (fgraph)
namespace Kepler.Text.TameSpine
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (GoodListNodesTl)

/-- **HOL `marked_list_mark_rtrans`**（reduction3.hl:2611-2628）：
`marked_list L N r x ⇒ MEM x (rtrans L N r x i)`——
ta 前提 = `transformAssumptionSpine_top L hL`（TowerTop 13/13），体 = `aqiunpp3`
（TameList17:255）的 MarkedListSpine 投影 `x ∈ rtrans i`（aq7 的 i 次换槽形）。 -/
theorem marked_list_mark_rtrans_top (L : fgraph ℕ) (hL : GoodList L) (i : ℕ)
    (hgn : GoodListNodesTl L hL) {N : List (List (ℕ × ℕ))} {r : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hm : MarkedListSpineFull hL N r x) :
    x ∈ rtransSpine L N r x i :=
  (aqiunpp3 L hL i (transformAssumptionSpine_top L hL) hgn hm).1.2.2.2.1

#print axioms marked_list_mark_rtrans_top
