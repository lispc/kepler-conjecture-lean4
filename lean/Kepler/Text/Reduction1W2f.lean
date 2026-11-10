/-
  Kepler.Text.Reduction1W2f — J4 Wave W2 批 3（W2_SPLIT_FROZEN 的 W2-2 簇
  第 5-6 件）：`vertices_normal_list`（HOL reduction1.hl:1856）+
  `card_vertices_normal_list`（:1878）。

  路线（HOL 两行式 chase 的 Lean 形）：
  `set_of_list (MAP FST (flatten N))`
  = `elements_of_list (quotient_list L N)`（`quotient_list_elements`：
  Spine 侧 `TameSpine.quotientListElements` 过
  `ChainBridgeParts.quotientList_eq_quotientListSpine` +
  `normalList_iff_normalListSpine`，与已落库 `Reduction3Thm13B` 同桥）
  = `{v | v ∈ g.vertices}`（`match_quotient_list` 右合取 + 前提）
  = `set_of_list (iota 0 (countVertices g))`（`Graph.vertices` 定义层
  `List.range g.countVertices`；`iota m (SUC n)` ↦ `List.range' m n` 链岛
  惯例，`range' 0 n = range n`）。CARD 件过 `cardSetOfListUniq`
  （`Reduction1W3d`，HOL `card_set_of_list_uniq` 同名族）。

  **纪律**：零公理、零占位证明、零反射式判定；不改既有陈述/定义。
-/
import Kepler.Text.Reduction5Base
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.TameList35
import Kepler.Text.Reduction3DefsAssumptionInst
import Kepler.Text.ChainBridgeParts
import Kepler.Text.ChainListsL1
import Kepler.Text.Reduction3DefsLayer
import Kepler.Text.Reduction1W3d

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.Reduction1

open Kepler.Assembly (GoodList)
open Kepler.Graphs (Graph)
open Kepler.Text.ChainLists (normalList)
open Kepler.Text.Reduction3 (matchQuotientList)
open Kepler.Text.Reduction5 (Dart quotientList)
open Kepler.Text.TameLp (elementsOfList)

/-- **HOL `vertices_normal_list`**（reduction1.hl:1856）：`good_list L ∧
normal_list L N ∧ match_quotient_list g L N ∧ vertices_set2 g =
elements_of_list (fgraph g)` ⇒ `set_of_list (MAP FST (flatten N)) =
set_of_list (iota 0 (countVertices g))`。
（`iota 0 (countVertices g)` ↦ `List.range' 0 (g.countVertices)`；
第 4 前提取图级簇既落形 `{v | v ∈ g.vertices} = elementsOfList (Kepler.Text.Reduction3.fgraphOfGraph g)`，
与 `Reduction3Thm13B.elementsOfListVerticesSet2Converse` 的消费形一致。） -/
theorem verticesNormalList {g : Graph} {L : Kepler.Graphs.fgraph ℕ}
    {N : List (List Dart)}
    (hgood : GoodList L) (hnl : normalList L hgood N)
    (hmq : matchQuotientList g L N)
    (hv2 : {v : ℕ | v ∈ g.vertices} = elementsOfList (Kepler.Text.Reduction3.fgraphOfGraph g)) :
    Kepler.Text.setOfList (N.flatten.map (fun d => d.1)) =
      Kepler.Text.setOfList (List.range' 0 (g.countVertices)) := by
  have hnsp : Kepler.Text.TameSpine.NormalListSpine hgood N :=
    (Kepler.Text.ChainBridge.normalList_iff_normalListSpine
      L hgood N).mp hnl
  have h1 : Kepler.Text.setOfList (N.flatten.map (fun d => d.1)) =
      elementsOfList (quotientList L N) := by
    rw [Kepler.Text.ChainBridge.quotientList_eq_quotientListSpine]
    exact (Kepler.Text.TameSpine.quotientListElements L hgood hnsp).symm
  have h2 : elementsOfList (quotientList L N) = {v : ℕ | v ∈ g.vertices} := by
    rw [← hmq.2]
    exact hv2.symm
  have hv : g.vertices = List.range (g.countVertices) := rfl
  have h3 : {v : ℕ | v ∈ g.vertices} =
      Kepler.Text.setOfList (List.range' 0 (g.countVertices)) := by
    rw [hv, List.range_eq_range']
    rfl
  exact h1.trans (h2.trans h3)

/-- **HOL `card_vertices_normal_list`**（reduction1.hl:1878）：同前提 ⇒
`CARD (set_of_list (MAP FST (flatten N))) = countVertices g`。 -/
theorem cardVerticesNormalList {g : Graph} {L : Kepler.Graphs.fgraph ℕ}
    {N : List (List Dart)}
    (hgood : GoodList L) (hnl : normalList L hgood N)
    (hmq : matchQuotientList g L N)
    (hv2 : {v : ℕ | v ∈ g.vertices} = elementsOfList (Kepler.Text.Reduction3.fgraphOfGraph g)) :
    (Kepler.Text.setOfList (N.flatten.map (fun d => d.1))).ncard =
      g.countVertices := by
  rw [verticesNormalList hgood hnl hmq hv2]
  have hcoe : Kepler.Text.setOfList (List.range' 0 (g.countVertices)) =
      Kepler.Text.TameSpine.setOfListNatSpine
        (List.range (g.countVertices)) := by
    rw [List.range_eq_range']
    rfl
  rw [hcoe, Kepler.Text.Reduction1.cardSetOfListUniq
    (by simpa using List.nodup_range)]
  simp

end Kepler.Text.Reduction1

/-! 公理审计锚（编译即执行；预期 ⊆ 标准三，零未证公理） -/
#print axioms Kepler.Text.Reduction1.verticesNormalList
#print axioms Kepler.Text.Reduction1.cardVerticesNormalList
