/-
  Kepler.Text.TameCorrG9 — `tame_correspondence_iso` 三波施工的 **W3 第十波（笔 1）**：
  G9 `tame_correspondence1`（HOL `WMLNYMD.hl:1473`）——六个对应件的图侧装配。
  **纯 glue，无新数学。**

  ┌─ 落点与环安全 ────────────────────────────────────────────────
  │ 唯一 import = `Kepler.Text.TameCorrG8`（→ …，闭包零
  │ `Kepler.Assembly` 本体）。环自检：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  **HOL 对照**（:1473）：
  `good_graph_v4 g ∧ tame_9a/10/11a/11b/12o/13a (hypermap_of_list (fgraph g))
   ⇒ tame g`。
  装配链：`tame9a/10_correspondence` → graph 面 9a/10；
  `tame11_correspondence` + `tame12o_correspondence` + `tame13a_correspondence`
  → list 面 11a/11b/12o/13a；再 `tame11a_good_graph`/`tame11b_list_tame11b`/
  `tame12o_list_tame12o`/`tame13a_list_tame13a` → graph 面，最后拼
  `Graphs.tame`（六合取；Bool 判据经 Lean 的 `Bool → Prop` coercion 即 `= true`）。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrG8
import Kepler.Text.TameCorrG3

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrG9

open Classical
open Kepler.Assembly (GoodList)
open Kepler.Text (Hypermap)
open Kepler.Text.TameLp (hypermapOfList elementsOfList Tame9a Tame10 Tame11a Tame11b
  Tame12o Tame13a GoodListNodesTl)
open Kepler.Text.TameCorrList (GoodGraphV4 GoodListNodes AllUniq VerticesSet2Eq
  tame11aList tame11bList tame12oList tame13aList)
open Kepler.Text.TameCorrCard (tame9aCorrespondence)
open Kepler.Text.TameCorrNode (tame10Correspondence)
open Kepler.Text.TameCorrG5 (tame11Correspondence tame12oCorrespondence)
open Kepler.Text.TameCorrG8 (tame13aCorrespondence)
open Kepler.Text.TameCorrList (tame11aGoodGraph tame11bListTame11b tame12oListTame12o)
open Kepler.Text.TameCorrG3 (tame13aListTame13a)
open Kepler.Graphs (Graph tame)

/-- HOL `tame_correspondence1`（WMLNYMD.hl:1473）：
`good_graph_v4 g ∧ 六个 hypermap 层平判 (hypermap_of_list (fgraph g)) ⇒ tame g`。
`GoodList` 证人显式取 `hgg.1`（`good_graph_v4` 首合取；Prop 证明无关，
消费者可传任意 `hL`）。 -/
theorem tameCorrespondence1 {g : Graph} (hgg : GoodGraphV4 g)
    (h9 : Tame9a (hypermapOfList g.fgraph hgg.1))
    (h10 : Tame10 (hypermapOfList g.fgraph hgg.1))
    (h11a : Tame11a (hypermapOfList g.fgraph hgg.1))
    (h11b : Tame11b (hypermapOfList g.fgraph hgg.1))
    (h12o : Tame12o (hypermapOfList g.fgraph hgg.1))
    (h13 : Tame13a (hypermapOfList g.fgraph hgg.1)) :
    tame g := by
  have hgn : GoodListNodesTl g.fgraph hgg.1 := hgg.2.1 hgg.1
  have hun : ∀ l ∈ g.fgraph, l.Nodup := hgg.2.2.2.1
  have hvert : Kepler.Text.TameCorrList.verticesSet2 g
      = elementsOfList g.fgraph := hgg.2.2.2.2.2
  have h9g : Kepler.Graphs.tame9a g = true := tame9aCorrespondence hgg.1 h9
  have h10g : Kepler.Graphs.tame10 g = true :=
    tame10Correspondence hgg.1 hgn hvert h10
  have h11 := tame11Correspondence hgg.1 hgn hun h11a h11b h12o
  have h12o_list := tame12oCorrespondence hgg.1 hgn hun h12o
  have h13_list := tame13aCorrespondence hgg.1 hgn hun h9 h13
  have h11a_g : Kepler.Graphs.tame11a g = true := tame11aGoodGraph hgg h11.1
  have h11b_g : Kepler.Graphs.tame11b g = true := tame11bListTame11b hgg h11.2
  have h12o_g : Kepler.Graphs.tame12o g = true := tame12oListTame12o hgg h12o_list
  have h13_g : Kepler.Graphs.tame13a g := tame13aListTame13a hgg h13_list
  exact ⟨h9g, h10g, h11a_g, h11b_g, h12o_g, h13_g⟩

end Kepler.Text.TameCorrG9
