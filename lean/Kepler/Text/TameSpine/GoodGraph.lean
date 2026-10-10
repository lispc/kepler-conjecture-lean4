/-
  Kepler.Text.TameSpine.GoodGraph — W0 keystone 批 2：S11 GoodGraphV4/GoodListNodes
  忠实 def 层（六合取真形，DEF-FIX flip 源）。

  立项：`docs/tamespine-port-plan.md` §4 W0 批 + §6 风险 3（弱编码占位链）。
  深侦：`docs/tame-chapter-scout.md` §3.3-S11 + §6-R1/R2/R9。

  镜像对象（HOL Light Flyspeck，reference/flyspeck commit 1ce0353）：
  - `text_formalization/tame/tame_defs2.hl:56-63`（`good_graph_v4` 六合取）；
  - `tame_defs2.hl:33-36`（`good_list_nodes`：`node_set (hypermap_of_list L) =
    set_of_list (nodes_of_list L)`——**依赖 S1 构造才能陈述**，scout §6-R2）；
  - `tame_defs2.hl:31`（`facesAt_v2`）、`tame_defs.hl:384-419`
    （`vertices_graph`/`vertices_set2`/`finalGraph`）。

  结构（Assembly §2b 五个 True 占位的补全源，逐一对应）：

  | Assembly §2b 占位（现态）          | 本模块 flip 源            | HOL 源 |
  | `GoodListNodes := True`（:612）    | `GoodListNodesSpine`      | tame_defs2:33 |
  | `FinalGraph := True`（:602）       | `FinalGraphSpine`         | tame_defs:419 |
  | `AllUniq := True`（:604）          | `AllUniqSpine`            | tame_defs2:59 |
  | `GoodFacesV3 := True`（:606）      | `GoodFacesV3Spine`        | tame_defs2:37-40 |
  | `VerticesSet2Eq := True`（:608）   | `VerticesSet2EqSpine`     | tame_defs2:61 |
  | `GoodGraphV4`（首合取外全占位）    | `GoodGraphV4Spine` 六合取 | tame_defs2:56-63 |

  **DEF-FIX 纪律（scout §6-R9）**：flip = 把各 `*Spine` def 体逐字抄入 Assembly §2b
  对应 def（def 体变更、定理陈述文本冻结、登记折算）——需编排者拍板授权（立项
  §6.6），本模块按红线不触碰 Assembly，只供 flip 源 + 现编码桥。flip 后
  `GoodGraphV4Spine g ↔ Assembly.GoodGraphV4 g` 退化为 `Iff.rfl`，本模块的桥
  `goodGraphV4Spine_implies` 无需改动即自动强化为同体。

  消费语义（scout §6-R1 后果注记）：占位态下 `Assembly.GoodGraphV4` 是假设侧
  弱化（A8 按现编码不可证）+ 结论侧空壳（A9）；R1 要求 **A9 装配从一开始就对着
  补强后的 def**——故 A9 的 `GoodGraphV4 g` 结论义务在 flip 前一律以
  `GoodGraphV4Spine g`（真形）记账，经 `goodGraphV4Spine_implies` 满足现编码。

  S1 衔接：`GoodListNodesSpine` 的 nodeSet 陈述经 TameLp W1 keystone 构造
  （9d775467）落地；与 TameLp 孪生 `GoodListNodesTl` 的衔接见
  `goodListNodesSpine_iff_tameLp`。规格桥（Assembly 谓词层）见姊妹模块
  `Kepler.Text.TameSpine.Keystone`（W0 批 1）。

  红线遵守：本模块零 sorry、零既有签名触碰。
-/
import Kepler.Assembly
import Kepler.Text.TameLp
import Kepler.Text.TameSpine.Keystone

namespace Kepler.Text.TameSpine

open Kepler.Text (Hypermap)
open Kepler.Graphs (fgraph Graph Vertex Face)
open Kepler.Assembly (GoodList)
open Kepler.Text.TameLp (hypermapOfList nodesOfListSet elementsOfList)

/-! ### AFP↔HOL 图数据桥支撑 def（scout §4-S11 "vertices_set2/facesAt_v2/perm_eq"） -/

/-- HOL `vertices_set2`（tame_defs.hl:392-394 `set_of_list (vertices_graph g)`）。
`vertices_graph g = upt 0 (countVertices g)`（:387）↦ AFP `Graph.vertices g =
List.range g.countVertices`（Graph.lean:98，`Vertex = ℕ`，Graph.lean:24）。 -/
def verticesSet2 (g : Graph) : Set Vertex := {v | v ∈ g.vertices}

/-- HOL `facesAt_v2`（tame_defs2.hl:31-32
`facesAt_v2 g v = FILTER (λf. MEM v (FST f)) (faces g)`）。
`FST f` ↦ `Face.vertices`；`faces g` ↦ `g.faces`。 -/
def facesAtV2 (g : Graph) (v : Vertex) : List Face :=
  g.faces.filter (fun f => v ∈ f.vertices)

/-! ### 五合取逐项忠实 def（Assembly §2b 占位的 flip 源） -/

/-- HOL `finalGraph`（tame_defs.hl:419 `finalGraph g = (nonFinals g = [])`）。
折算：AFP `Graph.final g = (nonFinals g).isEmpty`（Graph.lean:125）。 -/
def FinalGraphSpine (g : Graph) : Prop := g.final = true

/-- HOL `all uniq (fgraph g)`（tame_defs2.hl:59 合取项；`uniq` ↦ `List.Nodup`）。 -/
def AllUniqSpine (g : Graph) : Prop := ∀ l ∈ g.fgraph, l.Nodup

/-- HOL `good_faces_v3`（tame_defs2.hl:37-40
`!v. v IN vertices_set2 g ==> perm_eq (facesAt_v2 g v) (facesAt g v)`）。
`perm_eq` 折算：math-comp `perm_eq s t`（逐元素 count 相等，seq2-compiled.hl
`perm_eq_cat`/`perm_eq0r` 定理族同源）↦ Mathlib `List.Perm`
（`List.perm_iff_count`）。`facesAt g v = EL v (faceListAt g)` ↦ `g.facesAt v`
（越界约定：Isabelle `undefined` ↦ `getD []`，Graph.lean:100-103，生成器内
`v < countVertices g` 恒不触发）。 -/
def GoodFacesV3Spine (g : Graph) : Prop :=
  ∀ v ∈ verticesSet2 g, (facesAtV2 g v).Perm (g.facesAt v)

/-- HOL `vertices_set2 g = elements_of_list (fgraph g)`（tame_defs2.hl:61 合取项）。
`elements_of_list` ↦ `Kepler.Text.TameLp.elementsOfList`
（`undup (flatten L)` 的集合形，TameLp.lean:2622-2626 逐字镜像）。 -/
def VerticesSet2EqSpine (g : Graph) : Prop :=
  verticesSet2 g = elementsOfList g.fgraph

/-- HOL `good_list_nodes`（tame_defs2.hl:33-36
`node_set (hypermap_of_list L) = set_of_list (nodes_of_list L)`）。
`node_set` ↦ `Hypermap.nodeSet`（Hypermap.lean:1005 = `setOfOrbits darts nodeMap`）；
`nodes_of_list` 的集合形 ↦ `TameLp.nodesOfListSet`（TameLp.lean:2628-2632）。

arity 折算记账（flip 时逐字保此体）：Assembly 占位 `GoodListNodes (_ : fgraph ℕ)`
无 `GoodList` 前提，而 Lean 构造 `hypermapOfList` 是依赖式的（proof 参数）。
此处以 `∀ hL : GoodList L` 内量化保持 arity 不变——flip 后下游合取项
`GoodListNodes g.fgraph` 文本零改动。junk 语义差异：非 good `L` 时 HOL 计算
junk 超映射的 node_set（可假），此形空洞为真；全部消费语境（A8 假设侧经
`GoodGraphV4` 首合取、A9 经 `GoodList`）都携带 `GoodList L`，分歧不可达。
（与 TameLp.lean:2634-2638 `GoodListNodesTl` 同体，衔接见
`goodListNodesSpine_iff_tameLp`。） -/
def GoodListNodesSpine (L : fgraph ℕ) : Prop :=
  ∀ hL : GoodList L, (hypermapOfList L hL).nodeSet = nodesOfListSet L

/-! ### 六合取真形 -/

/-- HOL `good_graph_v4`（tame_defs2.hl:56-63）六合取真形：
`good_list (fgraph g) ∧ good_list_nodes (fgraph g) ∧ finalGraph g ∧
all uniq (fgraph g) ∧ good_faces_v3 g ∧ vertices_set2 g = elements_of_list (fgraph g)`。

Assembly §2b `GoodGraphV4`（Assembly.lean:615-617，后五合取 True 占位）的
DEF-FIX flip 源：flip = 五个 `*Spine` 体逐字抄入对应占位 def，本 def 体与
`Assembly.GoodGraphV4` 退化为逐字同体（`Iff.rfl`）。合取顺序与 Assembly/HOL
逐槽一致。 -/
def GoodGraphV4Spine (g : Graph) : Prop :=
  GoodList g.fgraph ∧ GoodListNodesSpine g.fgraph ∧ FinalGraphSpine g ∧
    AllUniqSpine g ∧ GoodFacesV3Spine g ∧ VerticesSet2EqSpine g

/-! ### 桥件 -/

/-- **现编码桥**（flip 前后两态共用）：忠实六合取真形 ⟹ Assembly §2b 谓词。
现态：占位五合取为 `True` 占位 def，逐槽 `trivial`；flip 后：右侧逐槽同体，
本桥仍真（并强化为 `Iff.rfl` 形的 `Iff.rfl`）——A9 结论义务以真形记账、
经本桥满足现编码的通道在 flip 前后无断裂。 -/
theorem goodGraphV4Spine_implies {g : Graph} (h : GoodGraphV4Spine g) :
    Kepler.Assembly.GoodGraphV4 g :=
  ⟨h.1, trivial, trivial, trivial, trivial, trivial⟩

/-- **S11 孪生衔接**：flip-ready 形 ↔ TameLp `GoodListNodesTl` 孪生
（TameLp.lean:2637-2638，同一 nodeSet 等式的显式前提形）——∀/→ 一身两形，
`Iff.rfl` 同体。TameLp 侧后续 `nodeSet` 定理族（若有）经此直接进出。 -/
theorem goodListNodesSpine_iff_tameLp (L : fgraph ℕ) :
    GoodListNodesSpine L ↔
      ∀ hL : GoodList L, Kepler.Text.TameLp.GoodListNodesTl L hL :=
  Iff.rfl

/-- **A9 证人出料（W0 组合验收）**：忠实 `GoodGraphV4` 自带列表机器前提
（首合取 `GoodList g.fgraph`），canonical `hypermapOfList` 构造即为
**Assembly 规格谓词**的证人（经 W0 批 1 验收锚）——A9 装配（`jcajydu`，
Assembly.lean:681 的 `∃ H'` 分量）与 A8 假设侧（`tameCorrespondenceIso` 的
`hIs : IsHypermapOfList g.fgraph H'`）自此有出料口。 -/
theorem goodGraphV4Spine_witness {g : Graph} (h : GoodGraphV4Spine g) :
    ∃ H' : Hypermap (ℕ × ℕ), Kepler.Assembly.IsHypermapOfList g.fgraph H' :=
  ⟨hypermapOfList g.fgraph h.1, isHypermapOfList_hypermapOfList' g.fgraph h.1⟩

end Kepler.Text.TameSpine

/-! 公理审计锚（收口探针执行；def 层 + 桥件预期零新公理依赖，
标准三 = `[propext, Classical.choice, Quot.sound]`）：
#print axioms Kepler.Text.TameSpine.goodGraphV4Spine_implies
#print axioms Kepler.Text.TameSpine.goodGraphV4Spine_witness
#print axioms Kepler.Text.TameSpine.goodListNodesSpine_iff_tameLp
-/
