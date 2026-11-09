/-
  Kepler.Text.Reduction5Tav2 — W2-a patch1①：HOL `transform_assumption_v2`
  （`tame_defs2.hl:568-572`）的链侧 def。

  ┌─ 落点勘误（对工单「def 落 Reduction5Base」；机器证据为准）──────
  │ `Reduction5Base` 不可承载本 def：`markedList`（9 合取载体）在
  │ `ChainListsL2`，而 `ChainListsL1.lean:44 import Kepler.Text.Reduction5Base`
  │ ⇒ Reduction5Base import ChainListsL2 成环（Base→L2→L1→Base）。
  │ 故落本新链侧文件（import = Reduction5Base + ChainListsL2，无环；
  │ 本文件不 import 任何 TameSpine 模块）。
  └────────────────────────────────────────────────────────────────

  ┌─ DIFFERS（折算记档）──────────────────────────────────────────
  │ HOL：`transform_assumption_v2 L <=> !N r x. (good_list L ∧
  │ good_list_nodes L ∧ marked_list L N r x ==> marked_list L
  │ (ntrans L N r x 1) (rtrans L N r x 1) x)`（HOL 的 new_definition'
  │ 名叫 `transform_assumption`、正文定义 `transform_assumption_v2`，
  │ 本文件取正文名）。前提合取三项按链侧载体惯例折算：
  │ `good_list` ↦ 显式参 `(hL : GoodList L)`（`ChainLists.markedList`
  │ 同款显式参形，编排者 2026-11-09 批准）；
  │ `good_list_nodes` ↦ `GoodListNodesTl L hL`（TameLp:5278 链侧忠实形，
  │ ChainTav2Interface.transformAssumptionOfAqChain 同款）；
  │ `marked_list` 保持前提位（箭头前件）；i = 1（HOL 定值）逐字。
  └────────────────────────────────────────────────────────────────

  **纪律**：纯 def 零证明义务；零 axiom/sorry/admit/native_decide；
  主仓 tracked 零改动（本文件经 patch 交付）。
-/

import Kepler.Text.Reduction5Base
import Kepler.Text.ChainListsL2

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction5

open Kepler.Graphs (fgraph)
open Kepler.Assembly (GoodList)

/-- HOL `transform_assumption_v2`（`tame_defs2.hl:568-572`）。
链侧载体形（逐槽对照见文件头 DIFFERS）：三次变换保 `markedList`。 -/
def transformAssumptionV2 (L : fgraph ℕ) : Prop :=
  ∀ (hL : GoodList L) (hgn : Kepler.Text.TameLp.GoodListNodesTl L hL)
    (N : List (List Dart)) (r : List Dart) (x : Dart),
    Kepler.Text.ChainLists.markedList L hL N r x →
    Kepler.Text.ChainLists.markedList L hL
      (ntrans L N r x 1) (rtrans L N r x 1) x

#check @Kepler.Text.Reduction5.transformAssumptionV2

end Kepler.Text.Reduction5
