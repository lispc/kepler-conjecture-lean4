/-
  Kepler.Text.TameCorrG4b — `tame_correspondence_iso` 三波施工的 **W3 第七波**：
  G4 收尾两件（HOL `WMLNYMD.hl:722` / `:745`）。

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrG4`（→ G4 → Node → Card → …，
  │ 闭包零 `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 对照**：
  · `card_set_of_n_meeting_node_pqr`（:722）：
    `CARD (set_of_triangles_meeting_node (hypermap_of_list L) x) = tri_list L (FST x) ∧
     CARD (set_of_quadrilaterals_meeting_node …) = quad_list L (FST x) ∧
     CARD (set_of_exceptional_meeting_node …) = except_list L (FST x)`
    —— 三实例 = `card_set_of_n_meeting_node` 取
    `P = (· = 3)` / `(· = 4)` / `(5 ≤ ·)`；`tri_list/quad_list` 的 `LENGTH f = 3/4`
    在 W3-W2 取 `f.length == 3/4`（Bool 等值），故补 `decide (n = k) = (n == k)` 桥。
  · `type_of_node_vertextype`（:745）：
    `type_of_node (hypermap_of_list L) x = vertextype_list L (FST x)`
    —— `typeOfNode` 三元组逐槽 `_pqr` 改写。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrG4

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrG4b

open Classical
open Kepler.Assembly (listPairs listOfDarts findFaceDarts GoodList)
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList setOfTrianglesMeetingNode setOfQuadrilateralsMeetingNode
  setOfExceptionalMeetingNode typeOfNode GoodListNodesTl)
open Kepler.Text.TameCorrFloor (facesAtList)
open Kepler.Text.TameCorrNode (dartOf)
open Kepler.Text.TameCorrG4 (cardSetOfNMeetingNode)
open Kepler.Graphs (fgraph)

/-- HOL `card_set_of_n_meeting_node_pqr`（WMLNYMD.hl:722）：
三角/四边/例外三类 meeting-node 集的基数 = 列表 `tri_list`/`quad_list`/`except_list`。 -/
theorem cardSetOfNMeetingNodePqr {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (x : ℕ × ℕ) (hx : x ∈ listOfDarts L) :
    (setOfTrianglesMeetingNode (hypermapOfList L hL) x).ncard
        = Kepler.Text.TameCorrList.triList L x.1 ∧
      (setOfQuadrilateralsMeetingNode (hypermapOfList L hL) x).ncard
        = Kepler.Text.TameCorrList.quadList L x.1 ∧
      (setOfExceptionalMeetingNode (hypermapOfList L hL) x).ncard
        = Kepler.Text.TameCorrList.exceptList L x.1 := by
  refine ⟨?_, ?_, ?_⟩
  · -- triangles (P = (· = 3))
    have h := cardSetOfNMeetingNode hL hgn x hx (fun n => n = 3)
    rw [show (setOfTrianglesMeetingNode (hypermapOfList L hL) x).ncard
        = ((facesAtList L x.1).filter (fun f => decide (f.length = 3))).length from h]
    unfold Kepler.Text.TameCorrList.triList
    rfl
  · -- quadrilaterals (P = (· = 4))
    have h := cardSetOfNMeetingNode hL hgn x hx (fun n => n = 4)
    rw [show (setOfQuadrilateralsMeetingNode (hypermapOfList L hL) x).ncard
        = ((facesAtList L x.1).filter (fun f => decide (f.length = 4))).length from h]
    unfold Kepler.Text.TameCorrList.quadList
    rfl
  · -- exceptional (P = (5 ≤ ·))
    have h := cardSetOfNMeetingNode hL hgn x hx (fun n => 5 ≤ n)
    rw [show (setOfExceptionalMeetingNode (hypermapOfList L hL) x).ncard
        = ((facesAtList L x.1).filter (fun f => decide (5 ≤ f.length))).length from h]
    unfold Kepler.Text.TameCorrList.exceptList
    rfl

/-- HOL `type_of_node_vertextype`（WMLNYMD.hl:745）：
`type_of_node (hypermap_of_list L) x = vertextype_list L (FST x)`。 -/
theorem typeOfNodeVertextype {L : fgraph ℕ} (hL : GoodList L)
    (hgn : GoodListNodesTl L hL) (x : ℕ × ℕ) (hx : x ∈ listOfDarts L) :
    typeOfNode (hypermapOfList L hL) x = Kepler.Text.TameCorrList.vertextypeList L x.1 := by
  obtain ⟨h1, h2, h3⟩ := cardSetOfNMeetingNodePqr hL hgn x hx
  unfold typeOfNode Kepler.Text.TameCorrList.vertextypeList
  rw [h1, h2, h3]

end Kepler.Text.TameCorrG4b
