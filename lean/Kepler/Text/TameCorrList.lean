/-
  Kepler.Text.TameCorrList — `tame_correspondence_iso` 三波施工的 **W3 第二波**：
  `reference/flyspeck/text_formalization/tame/WMLNYMD.hl` 的
  **G1+G2 列表面词汇**（11 个 `*_list` def，HOL :170-:556）+
  **`faces_at_list` 的 filter/长度桥**（15 件 prove，HOL :139-:415）。

  ┌─ 落点与环安全（刻意设计，非偶然）───────────────────────────────────
  │ import = `Kepler.Text.TameCorrFloor`（→ TameLp + Graphs.Tame）+
  │ `Kepler.Graphs.RelativeCompleteness`（提供 `Graph.fgraph`；闭包
  │ 零 `Kepler.Assembly`）。**不 import `Kepler.Assembly`**。
  │ 环自检（编排者复跑同款）：
  │   `#check @Kepler.Assembly.the_kepler_conjecture_from_interfaces`
  │   必须 **unknown identifier**。
  └────────────────────────────────────────────────────────────────

  ┌─ 图侧镜像 def（Assembly §2b，逐字抄体）───────────────────────────
  │ 15 件桥的假设侧是 HOL `good_graph_v4 g` / `finalGraph g` /
  │ `vertices_set2 g` / `facesAt_v2 g v`，Lean 侧只在
  │ `Kepler.Assembly`（`Kepler.Assembly.GoodGraphV4` 等）里有。
  │ 本波不能 import Assembly，故在 §0 **逐字复制** 六个 def +
  │ `verticesSet2`/`facesAtV2` 两个支撑 def（与岛
  │ `Kepler.Text.TameSpine.*Spine` 体同体；两处 namespace 隔离）。
  │ **落库义务（登记，不在本波）**：`TameCorrList.GoodGraphV4 g ↔
  │ Assembly.GoodGraphV4 g` 等八条桥在 HOIST/Assembly 侧
  │ 均为 `Iff.rfl`（体逐字同体），需在 Assembly 侧接线时补一个
  │ `Iff.rfl` 文件（本模块受“不 import Assembly”硬约束，无法在此验证）。
  └────────────────────────────────────────────────────────────────

  **HOL 逐件对照**（载体折算：`fgraph g` ↦ `Graph.fgraph g = g.faces.map
  Face.vertices`、`facesAt_list` ↦ `TameCorrFloor.facesAtList`、
  `elements_of_list` ↦ `TameLp.elementsOfList`、`FST f` ↦ `f.vertices`、
  `SND f` ↦ `f.final`、`LENGTH` ↦ `List.length`、`perm_eq` ↦ `List.Perm`、
  `sumn` ↦ `List.sum`、`MAP/FILTER` ↦ `List.map/List.filter`。
  Lean 的 `tame11a/tame11b/tame12o` 是 `Bool` 判据（`Graphs/Tame.lean`
  头注的既有载体），故三条对应定理结论为 `… = true`；`tri_list/quad_list`
  的 `LENGTH f = 3/4` 用 Lean `tri/quad` 同款 `f.length == 3/4` 书写的
  Bool 等值（命题上与 `decide (f.length = 3)` 等价）。

  **本波未含（明确 GAP，非 sorry）**：G1 的 `tame9a_correspondence`
  （HOL :42）与 `tame10_correspondence`（HOL :107）需要 List_hypermap
  缺口的 `card_face_of_list`/`components_hypermap_of_list`/
  `good_list_nodes_condition`/`uniq_list_of_elements`（TameLp 无），
  属工单列明的“前置 = List_hypermap 缺口 5–7 件”，留给后续波。

  **纪律**：无 `axiom`/`sorry`/`admit`/`native_decide`；不改既有陈述。
-/

import Kepler.Text.TameCorrFloor
import Kepler.Graphs.RelativeCompleteness

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Kepler.Text.TameCorrList

open Classical
open Kepler.Text.TameLp (elementsOfList nodesOfListSet)
open Kepler.Text.TameCorrFloor (facesAtList)
open Kepler.Assembly (GoodList)
open Kepler.Graphs

/-! ## §0 图侧镜像 def（HOL tame_defs2.hl:31-63 / Assembly §2b 逐字抄体） -/

/-- HOL `finalGraph`（tame_defs.hl:419）↦ `Graph.final g = true`。 -/
def FinalGraph (g : Graph) : Prop := g.final = true

/-- HOL `all uniq (fgraph g)`（tame_defs2.hl:58；`uniq` ↦ `List.Nodup`）。 -/
def AllUniq (g : Graph) : Prop := ∀ l ∈ g.fgraph, l.Nodup

/-- HOL `vertices_set2`（tame_defs.hl:392）= `set_of_list (vertices_graph g)`。 -/
def verticesSet2 (g : Graph) : Set Vertex := {v | v ∈ g.vertices}

/-- HOL `facesAt_v2`（tame_defs2.hl:31-32）：
`FILTER (λf. MEM v (FST f)) (faces g)`。 -/
def facesAtV2 (g : Graph) (v : Vertex) : List Face :=
  g.faces.filter (fun f => v ∈ f.vertices)

/-- HOL `good_faces_v3`（tame_defs2.hl:48-51）：`perm_eq (facesAt_v2 g v) (facesAt g v)`。 -/
def GoodFacesV3 (g : Graph) : Prop :=
  ∀ v ∈ verticesSet2 g, (facesAtV2 g v).Perm (g.facesAt v)

/-- HOL `vertices_set2 g = elements_of_list (fgraph g)`（tame_defs2.hl:60）。 -/
def VerticesSet2Eq (g : Graph) : Prop :=
  verticesSet2 g = elementsOfList g.fgraph

/-- HOL `good_list_nodes`（tame_defs2.hl:33-36）。 -/
def GoodListNodes (L : fgraph ℕ) : Prop :=
  ∀ hL : GoodList L,
    (Kepler.Text.TameLp.hypermapOfList L hL).nodeSet = nodesOfListSet L

/-- HOL `good_graph_v4`（tame_defs2.hl:56-63）六合取（顺序与 Assembly 逐槽一致）。 -/
def GoodGraphV4 (g : Graph) : Prop :=
  GoodList g.fgraph ∧ GoodListNodes g.fgraph ∧ FinalGraph g ∧ AllUniq g ∧
    GoodFacesV3 g ∧ VerticesSet2Eq g

/-! ## §1 11 个 `*_list` 列表面 def（HOL :170-:556 逐字） -/

/-- HOL `tame11a_list`（WMLNYMD.hl:170）：
`!v IN elements_of_list L. 3 <= LENGTH (facesAt_list L v)`。 -/
def tame11aList (L : fgraph ℕ) : Prop :=
  ∀ v ∈ elementsOfList L, 3 ≤ (facesAtList L v).length

/-- HOL `except_list`（WMLNYMD.hl:286）：
`LENGTH (FILTER (λf. 5 <= LENGTH f) (facesAt_list L v))`。 -/
def exceptList (L : fgraph ℕ) (v : ℕ) : ℕ :=
  ((facesAtList L v).filter (fun f => decide (5 ≤ f.length))).length

/-- HOL `tame11b_list`（WMLNYMD.hl:304）：
`LENGTH (facesAt_list L v) <= if except_list L v = 0 then 7 else 6`。 -/
def tame11bList (L : fgraph ℕ) : Prop :=
  ∀ v ∈ elementsOfList L,
    (facesAtList L v).length ≤ if exceptList L v = 0 then 7 else 6

/-- HOL `tri_list`（WMLNYMD.hl:325）：
`LENGTH (FILTER (λf. LENGTH f = 3) (facesAt_list L v))`。
`LENGTH f = 3` 取 Lean `tri` 同款 Bool 等值 `f.length == 3`（`Graph.lean:134`）。 -/
def triList (L : fgraph ℕ) (v : ℕ) : ℕ :=
  ((facesAtList L v).filter (fun f => f.length == 3)).length

/-- HOL `quad_list`（WMLNYMD.hl:328）；同 `tri_list`，`== 4`。 -/
def quadList (L : fgraph ℕ) (v : ℕ) : ℕ :=
  ((facesAtList L v).filter (fun f => f.length == 4)).length

/-- HOL `vertextype_list`（WMLNYMD.hl:331）：`(tri_list, quad_list, except_list)`。 -/
def vertextypeList (L : fgraph ℕ) (v : ℕ) : ℕ × ℕ × ℕ :=
  (triList L v, quadList L v, exceptList L v)

/-- HOL `tame12o_list`（WMLNYMD.hl:392）。 -/
def tame12oList (L : fgraph ℕ) : Prop :=
  ∀ v, v ∈ elementsOfList L ∧ exceptList L v ≠ 0 ∧ (facesAtList L v).length = 6 →
    vertextypeList L v = (5, 0, 1)

/-- HOL `admissible1_list`（WMLNYMD.hl:418）。 -/
def admissible1List (w : List ℕ → ℕ) (L : fgraph ℕ) : Prop :=
  ∀ f ∈ L, squanderFace f.length ≤ w f

/-- HOL `admissible2_list`（WMLNYMD.hl:487）。 -/
def admissible2List (w : List ℕ → ℕ) (L : fgraph ℕ) : Prop :=
  ∀ v ∈ elementsOfList L, exceptList L v = 0 →
    squanderVertex (triList L v) (quadList L v) ≤ ((facesAtList L v).map w).sum

/-- HOL `admissible3_list`（WMLNYMD.hl:516）。 -/
def admissible3List (w : List ℕ → ℕ) (L : fgraph ℕ) : Prop :=
  ∀ v ∈ elementsOfList L, vertextypeList L v = (5, 0, 1) →
    excessTCount ≤ (((facesAtList L v).filter (fun f => f.length == 3)).map w).sum

/-- HOL `tame13a_list`（WMLNYMD.hl:550）。 -/
def tame13aList (L : fgraph ℕ) : Prop :=
  ∃ w : List ℕ → ℕ,
    admissible1List w L ∧ admissible2List w L ∧ admissible3List w L ∧
      (L.map w).sum < squanderTarget

/-! ## §2 列表/图数据换装助手 -/

private theorem mem_facesAtV2 {g : Graph} {v : Vertex} {f : Face} :
    f ∈ facesAtV2 g v ↔ f ∈ g.faces ∧ v ∈ f.vertices := by
  simp [facesAtV2]

/-- `finalGraph` 的逐面形态：所有面都是 final（HOL `finalGraph` 拆支）。 -/
private theorem all_final_of_finalGraph {g : Graph} (h : FinalGraph g) :
    ∀ f ∈ g.faces, f.final = true := by
  intro f hf
  have hnil : g.faces.filter (fun f => !f.final) = [] := by
    have h1 : (nonFinals g).isEmpty = true := h
    rw [nonFinals] at h1
    exact List.isEmpty_iff.mp h1
  have hfalse : ¬ ((!f.final) = true) := (List.filter_eq_nil_iff.mp hnil) f hf
  have hb : (!f.final) = false := Bool.eq_false_iff.mpr hfalse
  simpa using hb

/-- `v ∈ vertices_set2 g` → `v ∈ elements_of_list (fgraph g)`（`good_graph_v4` 第 6 合取）。 -/
private theorem mem_elementsOfList_of_mem_vertices {g : Graph} {v : Vertex}
    (hgg : GoodGraphV4 g) (hv : v ∈ g.vertices) : v ∈ elementsOfList g.fgraph := by
  rw [← hgg.2.2.2.2.2]
  exact hv

/-! ## §3 G2 15 件（WMLNYMD.hl:139-:415） -/

/-- HOL `finalGraph_except`（WMLNYMD.hl:139）。 -/
theorem finalGraphExcept {g : Graph} {v : Vertex} (hfin : FinalGraph g)
    (hperm : (facesAtV2 g v).Perm (g.facesAt v)) :
    except g v =
      ((facesAtV2 g v).filter (fun f => decide (5 ≤ f.vertices.length))).length := by
  have hall : ∀ f ∈ g.facesAt v, f.final = true := by
    intro f hf
    have hfv2 : f ∈ facesAtV2 g v := hperm.mem_iff.mpr hf
    exact all_final_of_finalGraph hfin f (mem_facesAtV2.mp hfv2).1
  have hfilt : (g.facesAt v).filter (fun f => f.final && decide (5 ≤ f.vertices.length)) =
      (g.facesAt v).filter (fun f => decide (5 ≤ f.vertices.length)) := by
    refine List.filter_congr ?_
    intro f hf
    rw [hall f hf]
    rfl
  calc except g v
      = ((g.facesAt v).filter (fun f => f.final && decide (5 ≤ f.vertices.length))).length :=
          rfl
    _ = ((g.facesAt v).filter (fun f => decide (5 ≤ f.vertices.length))).length := by rw [hfilt]
    _ = ((facesAtV2 g v).filter (fun f => decide (5 ≤ f.vertices.length))).length :=
        ((hperm.filter (fun f => decide (5 ≤ f.vertices.length))).length_eq).symm

/-- HOL `facesAt2_list`（WMLNYMD.hl:176）。 -/
theorem facesAt2List {g : Graph} {v : Vertex} (_hgg : GoodGraphV4 g)
    (_hv : v ∈ verticesSet2 g) :
    (facesAtV2 g v).map Face.vertices = facesAtList g.fgraph v := by
  unfold facesAtV2 facesAtList Graph.fgraph
  exact (List.filter_map (f := Face.vertices) (p := fun l => decide (v ∈ l))
    (l := g.faces)).symm

/-- HOL `good_graph_perm_eq_facesAt`（WMLNYMD.hl:190）；`good_graph_v4` 第 5 合取。 -/
theorem goodGraphPermEqFacesAt {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) : (facesAtV2 g v).Perm (g.facesAt v) :=
  hgg.2.2.2.2.1 v hv

/-- HOL `LENGTH_facesAt`（WMLNYMD.hl:199）。 -/
theorem lengthFacesAt {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) : (facesAtV2 g v).length = (g.facesAt v).length :=
  (goodGraphPermEqFacesAt hgg hv).length_eq

/-- `facesAt_list` 长度 = 图侧度数（`facesAt2_list` + `LENGTH_facesAt` 合流）。 -/
private theorem length_facesAtList_eq_degree {g : Graph} {v : Vertex}
    (hgg : GoodGraphV4 g) (hv : v ∈ verticesSet2 g) :
    (facesAtList g.fgraph v).length = degree g v := by
  rw [← facesAt2List hgg hv, List.length_map, lengthFacesAt hgg hv]
  rfl

/-- HOL `tame11a_good_graph`（WMLNYMD.hl:212）；Lean `tame11a : Bool` ⇒ `= true`。 -/
theorem tame11aGoodGraph {g : Graph} (hgg : GoodGraphV4 g)
    (hlist : tame11aList g.fgraph) : tame11a g = true := by
  rw [tame11a, List.all_eq_true]
  intro v hv
  have hv' : v ∈ elementsOfList g.fgraph :=
    mem_elementsOfList_of_mem_vertices hgg hv
  have h3 : 3 ≤ (facesAtList g.fgraph v).length := hlist v hv'
  have hlen : (facesAtList g.fgraph v).length = degree g v := by
    rw [← facesAt2List hgg hv, List.length_map, lengthFacesAt hgg hv]
    rfl
  exact decide_eq_true (hlen ▸ h3)

/-- HOL `good_final_filter`（WMLNYMD.hl:229）。 -/
theorem goodFinalFilter {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) (P : Face → Bool) :
    (facesAtV2 g v).filter (fun f => f.final && P f) =
      (facesAtV2 g v).filter P := by
  refine List.filter_congr ?_
  intro f hf
  have hmem := mem_facesAtV2.mp hf
  have hfinal : f.final = true := all_final_of_finalGraph hgg.2.2.1 f hmem.1
  rw [hfinal]
  rfl

/-- HOL `length_good_final_filter`（WMLNYMD.hl:249）。 -/
theorem lengthGoodFinalFilter {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) (P : Face → Bool) :
    ((g.facesAt v).filter (fun f => f.final && P f)).length =
      ((g.facesAt v).filter P).length := by
  have hperm := goodGraphPermEqFacesAt hgg hv
  have hp1 : ((facesAtV2 g v).filter (fun f => f.final && P f)).Perm
      ((g.facesAt v).filter (fun f => f.final && P f)) :=
    hperm.filter (fun f => f.final && P f)
  have hp2 : ((facesAtV2 g v).filter P).Perm ((g.facesAt v).filter P) := hperm.filter P
  have heq := goodFinalFilter hgg hv P
  calc ((g.facesAt v).filter (fun f => f.final && P f)).length
      = ((facesAtV2 g v).filter (fun f => f.final && P f)).length := hp1.length_eq.symm
    _ = ((facesAtV2 g v).filter P).length := by rw [heq]
    _ = ((g.facesAt v).filter P).length := hp2.length_eq

/-- HOL `good_type_filter`（WMLNYMD.hl:271）。 -/
theorem goodTypeFilter {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) (P : ℕ → Bool) :
    (facesAtList g.fgraph v).filter (fun l => P l.length) =
      ((facesAtV2 g v).filter (fun f => P f.vertices.length)).map Face.vertices := by
  rw [← facesAt2List hgg hv]
  exact List.filter_map (f := Face.vertices) (p := fun l => P l.length)
    (l := facesAtV2 g v)

/-- HOL `except_list_except`（WMLNYMD.hl:289）。 -/
theorem exceptListExcept {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) : exceptList g.fgraph v = except g v := by
  have hfin : FinalGraph g := hgg.2.2.1
  have hperm : (facesAtV2 g v).Perm (g.facesAt v) := goodGraphPermEqFacesAt hgg hv
  unfold exceptList
  rw [goodTypeFilter hgg hv (fun n => decide (5 ≤ n)), List.length_map]
  exact (finalGraphExcept hfin hperm).symm

/-- HOL `tame11b_list_tame11b`（WMLNYMD.hl:308）；Lean `tame11b : Bool` ⇒ `= true`。 -/
theorem tame11bListTame11b {g : Graph} (hgg : GoodGraphV4 g)
    (hlist : tame11bList g.fgraph) : tame11b g = true := by
  rw [tame11b, List.all_eq_true]
  intro v hv
  have hv' : v ∈ elementsOfList g.fgraph :=
    mem_elementsOfList_of_mem_vertices hgg hv
  have hb : (facesAtList g.fgraph v).length ≤
      if exceptList g.fgraph v = 0 then 7 else 6 := hlist v hv'
  have hexc : exceptList g.fgraph v = except g v := exceptListExcept hgg hv
  have hlen : (facesAtList g.fgraph v).length = degree g v :=
    length_facesAtList_eq_degree hgg hv
  exact decide_eq_true (by rw [← hlen, ← hexc]; exact hb)

/-- HOL `length_filter_facesAt`（WMLNYMD.hl:334）。 -/
theorem lengthFilterFacesAt {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) (P : Face → Bool) :
    ((facesAtV2 g v).filter P).length = ((g.facesAt v).filter P).length :=
  ((goodGraphPermEqFacesAt hgg hv).filter P).length_eq

/-- HOL `tri_list_tri`（WMLNYMD.hl:349）。 -/
theorem triListTri {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) : triList g.fgraph v = tri g v := by
  unfold triList
  rw [← facesAt2List hgg hv, List.filter_map, List.length_map]
  change ((facesAtV2 g v).filter (fun f => f.vertices.length == 3)).length = tri g v
  rw [lengthFilterFacesAt hgg hv (fun f => f.vertices.length == 3)]
  rw [← lengthGoodFinalFilter hgg hv (fun f => f.vertices.length == 3)]
  unfold tri
  rfl

/-- HOL `quad_list_quad`（WMLNYMD.hl:365）。 -/
theorem quadListQuad {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) : quadList g.fgraph v = quad g v := by
  unfold quadList
  rw [← facesAt2List hgg hv, List.filter_map, List.length_map]
  change ((facesAtV2 g v).filter (fun f => f.vertices.length == 4)).length = quad g v
  rw [lengthFilterFacesAt hgg hv (fun f => f.vertices.length == 4)]
  rw [← lengthGoodFinalFilter hgg hv (fun f => f.vertices.length == 4)]
  unfold quad
  rfl

/-- HOL `vertextype_list_vertextype`（WMLNYMD.hl:381）。 -/
theorem vertextypeListVertextype {g : Graph} {v : Vertex} (hgg : GoodGraphV4 g)
    (hv : v ∈ verticesSet2 g) : vertextypeList g.fgraph v = vertextype g v := by
  simp only [vertextypeList, vertextype, triListTri hgg hv, quadListQuad hgg hv,
    exceptListExcept hgg hv]

/-- HOL `tame12o_list_tame12o`（WMLNYMD.hl:397）；Lean `tame12o : Bool` ⇒ `= true`。 -/
theorem tame12oListTame12o {g : Graph} (hgg : GoodGraphV4 g)
    (hlist : tame12oList g.fgraph) : tame12o g = true := by
  rw [tame12o, List.all_eq_true]
  intro v hv
  have hv' : v ∈ elementsOfList g.fgraph :=
    mem_elementsOfList_of_mem_vertices hgg hv
  have hexc : exceptList g.fgraph v = except g v := exceptListExcept hgg hv
  have hlen : (facesAtList g.fgraph v).length = degree g v :=
    length_facesAtList_eq_degree hgg hv
  by_cases hc : except g v ≠ 0 ∧ degree g v = 6
  · rw [if_pos hc]
    apply decide_eq_true
    have hlist' : vertextypeList g.fgraph v = (5, 0, 1) := by
      refine hlist v ⟨hv', ?_, ?_⟩
      · rw [hexc]
        exact hc.1
      · rw [hlen]
        exact hc.2
    rw [← vertextypeListVertextype hgg hv]
    exact hlist'
  · rw [if_neg hc]

end Kepler.Text.TameCorrList
